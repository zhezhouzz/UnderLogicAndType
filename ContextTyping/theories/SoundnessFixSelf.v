(** * ContextTyping.SoundnessFixSelf

    Recursive-self support for the Fix Fundamental case. *)

From Stdlib Require Import Lia Logic.Classical.
From CoreLang Require Import BasicTyping BasicTypingProps InstantiationProps
  SmallStep StrongNormalization.
From ContextStore Require Import Store.
From ContextAlgebra Require Import ResourceInterface ResourceExtension.
From ContextBasicDenotation Require Import StoreTyping TermExtension TermTLet Qualifier
  BasicTypingFormula RelevantEnv.
From Denotation Require Import Context
  TypeEquivCore
  TypeEquivBody
  TypeEquivArrow
  TypeEquivWand
  TypeEquiv
  ConstDenote.
From ContextTyping Require Import Typing SoundnessLam SoundnessFixBase
  SoundnessFixOpen SoundnessFixApply.

Local Ltac fix_self_in_union :=
  first
    [ assumption
    | apply elem_of_union_l; fix_self_in_union
    | apply elem_of_union_r; fix_self_in_union
    | apply elem_of_singleton_2; reflexivity ].

Local Ltac fix_self_break_union H :=
  repeat match type of H with
  | _ ∈ _ ∪ _ => apply elem_of_union in H as [H | H]
  | _ ∈ {[ _ ]} => apply elem_of_singleton in H; subst
  end.

Local Ltac fix_self_notin_union :=
  let Hbad := fresh "Hbad" in
  intros Hbad;
  fix_self_break_union Hbad;
  match type of Hbad with
  | ?x ∈ _ =>
    match goal with
    | H : x ∉ _ |- False =>
      apply H; fix_self_in_union
    end
  end.

Lemma fix_self_rec_call_zero
    (Σ : tyctx) Γ τx τ vf b t (my : WfWorldT) y :
  erase_ty τx = TBase b ->
  erase_ty τ = t ->
  context_typing_wf Σ Γ
    (tret (vfix (TBase b →ₜ t) vf)) (CTArrow τx τ) ->
  context_typing_wf Σ
    (CtxComma Γ (CtxBind y τx))
    (tret ({0 ~> vfvar y} vf))
    (CTArrow (fix_rec_call_ty b y τx τ) ({0 ~> y} τ)) ->
  y ∉ dom (ctx_erasure_under Σ Γ) ->
  my ⊨ ctx_denote_under Σ (CtxComma Γ (CtxBind y τx)) ->
  my ⊨ ty_denote_gas 0
    ((<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ))))
    (fix_rec_call_ty b y τx τ)
    (tret (vfix (TBase b →ₜ t) vf)).
Proof.
Admitted.

Definition world_arg_min_at (b : base_ty) (x : atom)
    (m : WfWorldT) (μ : nat) : Prop :=
  (exists σ c,
    (m : WorldT) σ /\
    σ !! x = Some (vconst c) /\
    constant_measure_for_base b c = μ) /\
  forall σ c,
    (m : WorldT) σ ->
    σ !! x = Some (vconst c) ->
    μ <= constant_measure_for_base b c.

Definition fix_self_rec_call_reducible_at_measure
    (Σ : tyctx) Γ φx τ vf b t (L : aset) (μ : nat) : Prop :=
  forall (parent : WfWorldT) x,
    x ∉ L ∪ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪
        fv_value vf ∪ fv_cty (over_ty b φx) ∪ fv_cty τ ->
    world_arg_min_at b x parent μ ->
    parent ⊨ ctx_denote_under Σ
      (CtxComma Γ (CtxBind x (over_ty b φx))) ->
    parent ⊨ ty_denote_gas
      (Nat.max (cty_depth (over_ty b φx)) (cty_depth τ))
      ((<[LVFree x := TBase b]>
        (atom_env_to_lty_env (erase_ctx Γ))))
      (over_ty b φx)
      (tret (vfvar x)) ->
    parent ⊨ ty_denote_gas 0
      ((<[LVFree x := TBase b]>
        (atom_env_to_lty_env (erase_ctx Γ))))
      (fix_rec_call_ty b x (over_ty b φx) τ)
      (tret (vfix (TBase b →ₜ t) vf)) ->
    parent ⊨ ty_denote_gas
      (cty_depth (fix_rec_call_ty b x (over_ty b φx) τ))
      ((<[LVFree x := TBase b]>
        (atom_env_to_lty_env (erase_ctx Γ))))
      (fix_rec_call_ty b x (over_ty b φx) τ)
      (tret (vfix (TBase b →ₜ t) vf)).

Lemma nat_pred_min_exists (P : nat -> Prop) μ :
  P μ ->
  exists μmin,
    P μmin /\ forall ν, P ν -> μmin <= ν.
Proof.
Admitted.

Lemma world_arg_min_exists_from_const
    b x (m : WfWorldT) :
  (forall σ,
    (m : WorldT) σ ->
    exists c, σ !! x = Some (vconst c)) ->
  exists μ, world_arg_min_at b x m μ.
Proof.
Admitted.

Lemma fix_self_rec_call_world_min_exists
    gas Σ φx b x (m : WfWorldT) :
  m ⊨ ty_denote_gas gas Σ
      (over_ty b φx)
      (tret (vfvar x)) ->
  exists μ, world_arg_min_at b x m μ.
Proof.
Admitted.

Lemma fix_rec_open_arg_normalize
    Γ φx τ vf b t x z (mz : WfWorldT) :
  lc_context_ty (over_ty b φx) ->
  x ∉ fv_cty (over_ty b φx) ->
  z <> x ->
  z ∉ dom (erase_ctx Γ) ∪ fv_value vf ∪
      fv_cty (over_ty b φx) ∪ fv_cty τ ->
  let Δx := (<[LVFree x := TBase b]>
    (atom_env_to_lty_env (erase_ctx Γ))) in
  let τarg := CTInter (over_ty b φx)
    (over_ty b (mk_q_lt_base b (vbvar 0) (vfvar x))) in
  let τself := fix_rec_call_ty b x (over_ty b φx) τ in
  let self := tret (vfix (TBase b →ₜ t) vf) in
  mz ⊨ formula_open 0 z
    (ty_denote_gas (Nat.max (cty_depth τarg) (cty_depth τ))
      (typed_lty_env_bind
        (relevant_env Δx τself self)
        (erase_ty τarg))
      (cty_shift 0 τarg)
      (tret (vbvar 0))) ->
  let Δz := (<[LVFree z := TBase b]>
    (atom_env_to_lty_env (erase_ctx Γ))) in
  mz ⊨ ty_denote_gas
    (Nat.max (cty_depth (over_ty b φx)) (cty_depth τ))
    Δz
    (over_ty b φx)
    (tret (vfvar z)) /\
  mz ⊨ ty_denote_gas
    (Nat.max (cty_depth (over_ty b (mk_q_lt_base b (vbvar 0) (vfvar x))))
      (cty_depth τ))
    ((<[LVFree z := TBase b]>
      (<[LVFree x := TBase b]>
        (atom_env_to_lty_env (erase_ctx Γ)))))
    (over_ty b (mk_q_lt_base b (vbvar 0) (vfvar x)))
    (tret (vfvar z)).
Proof.
Admitted.

Lemma fix_rec_arg_decreases_min
    gas Σ b x z μ (parent mz : WfWorldT) :
  z <> x ->
  lty_env_closed Σ ->
  0 < gas ->
  parent ⊑ mz ->
  world_arg_min_at b x parent μ ->
  mz ⊨ ty_denote_gas gas Σ
    (over_ty b (mk_q_lt_base b (vbvar 0) (vfvar x)))
    (tret (vfvar z)) ->
  exists μ',
    μ' < μ /\
    world_arg_min_at b z mz μ'.
Proof.
Admitted.

Lemma fix_rec_child_ctx_from_arg
    Σ Γ φx τ b x z (parent mz : WfWorldT) :
  basic_ctx (dom Σ) Γ ->
  fv_cty (over_ty b φx) ⊆ dom (erase_ctx Γ) ->
  parent ⊑ mz ->
  parent ⊨ ctx_denote_under Σ
    (CtxComma Γ (CtxBind x (over_ty b φx))) ->
  mz ⊨ ty_denote_gas
    (Nat.max (cty_depth (over_ty b φx)) (cty_depth τ))
    ((<[LVFree z := TBase b]>
      (atom_env_to_lty_env (erase_ctx Γ))))
    (over_ty b φx)
    (tret (vfvar z)) ->
  z ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪
      fv_cty (over_ty b φx) ->
  mz ⊨ ctx_denote_under Σ
    (CtxComma Γ (CtxBind z (over_ty b φx))).
Proof.
Admitted.

Lemma fix_rec_unfolded_result_to_open_goal
    Σ Γ φx τ vf b t (mz : WfWorldT) x z :
  erase_ty τ = t ->
  context_typing_wf Σ Γ
    (tret (vfix (TBase b →ₜ t) vf))
    (CTArrow (over_ty b φx) τ) ->
  z <> x ->
  x ∉ fv_value vf ∪ fv_cty τ ->
  z ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪
      fv_value vf ∪ fv_cty (over_ty b φx) ∪ fv_cty τ ->
  mz ⊨ ctx_denote_under Σ
    (CtxComma Γ (CtxBind z (over_ty b φx))) ->
  mz ⊨ ty_denote_gas
    (Nat.max (cty_depth (over_ty b φx)) (cty_depth τ))
    ((<[LVFree z := TBase b]>
      (atom_env_to_lty_env (erase_ctx Γ))))
    (cty_open 0 z τ)
    (tapp_tm (tret (open_value 0 (vfvar z) vf))
      (vfix (TBase b →ₜ t) vf)) ->
  let Δx := (<[LVFree x := TBase b]>
    (atom_env_to_lty_env (erase_ctx Γ))) in
  let τarg := CTInter (over_ty b φx)
    (over_ty b (mk_q_lt_base b (vbvar 0) (vfvar x))) in
  let τself := fix_rec_call_ty b x (over_ty b φx) τ in
  let self := tret (vfix (TBase b →ₜ t) vf) in
  mz ⊨ formula_open 0 z
    (ty_denote_gas (Nat.max (cty_depth τarg) (cty_depth τ))
      (typed_lty_env_bind
        (relevant_env Δx τself self)
        (erase_ty τarg))
      τ
      (tapp_tm (tm_shift 0 self) (vbvar 0))).
Proof.
Admitted.

Lemma fix_self_rec_call_reducible_measure_step Σ Γ φx τ vf b t (L : aset) μ :
  erase_ty τ = t ->
  context_typing_wf Σ Γ
    (tret (vfix (TBase b →ₜ t) vf))
    (CTArrow (over_ty b φx) τ) ->
  (forall x, x ∉ L ->
    context_typing_wf Σ
      (CtxComma Γ (CtxBind x (over_ty b φx)))
      (tret ({0 ~> vfvar x} vf))
      (CTArrow (fix_rec_call_ty b x (over_ty b φx) τ) ({0 ~> x} τ))) ->
  (forall x, x ∉ L ->
    ctx_denote_under Σ (CtxComma Γ (CtxBind x (over_ty b φx))) ⊫
      ty_denote_under Σ (CtxComma Γ (CtxBind x (over_ty b φx)))
        (CTArrow (fix_rec_call_ty b x (over_ty b φx) τ) ({0 ~> x} τ))
        (tret ({0 ~> vfvar x} vf))) ->
  (forall μ',
    μ' < μ ->
    fix_self_rec_call_reducible_at_measure Σ Γ φx τ vf b t L μ') ->
  fix_self_rec_call_reducible_at_measure Σ Γ φx τ vf b t L μ.
Proof.
Admitted.

Lemma fix_self_rec_call_denotation_by_world_min_induction Σ Γ φx τ vf b t (L : aset) :
  erase_ty τ = t ->
  context_typing_wf Σ Γ
    (tret (vfix (TBase b →ₜ t) vf))
    (CTArrow (over_ty b φx) τ) ->
  (forall x, x ∉ L ->
    context_typing_wf Σ
      (CtxComma Γ (CtxBind x (over_ty b φx)))
      (tret ({0 ~> vfvar x} vf))
      (CTArrow (fix_rec_call_ty b x (over_ty b φx) τ) ({0 ~> x} τ))) ->
  (forall x, x ∉ L ->
    ctx_denote_under Σ (CtxComma Γ (CtxBind x (over_ty b φx))) ⊫
      ty_denote_under Σ (CtxComma Γ (CtxBind x (over_ty b φx)))
        (CTArrow (fix_rec_call_ty b x (over_ty b φx) τ) ({0 ~> x} τ))
        (tret ({0 ~> vfvar x} vf))) ->
  forall μ, fix_self_rec_call_reducible_at_measure Σ Γ φx τ vf b t L μ.
Proof.
Admitted.

Lemma fix_self_rec_call_denotation Σ Γ φx τ vf b t (L : aset)
    (my : WfWorldT) y :
  erase_ty τ = t ->
  context_typing_wf Σ Γ
    (tret (vfix (TBase b →ₜ t) vf))
    (CTArrow (over_ty b φx) τ) ->
  (forall y, y ∉ L ->
    context_typing_wf Σ
      (CtxComma Γ (CtxBind y (over_ty b φx)))
      (tret ({0 ~> vfvar y} vf))
      (CTArrow (fix_rec_call_ty b y (over_ty b φx) τ) ({0 ~> y} τ))) ->
  (forall y, y ∉ L ->
    ctx_denote_under Σ (CtxComma Γ (CtxBind y (over_ty b φx))) ⊫
      ty_denote_under Σ (CtxComma Γ (CtxBind y (over_ty b φx)))
        (CTArrow (fix_rec_call_ty b y (over_ty b φx) τ) ({0 ~> y} τ))
        (tret ({0 ~> vfvar y} vf))) ->
  y ∉ L ∪ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_value vf ∪
      fv_cty (over_ty b φx) ∪ fv_cty τ ->
  my ⊨ ctx_denote_under Σ (CtxComma Γ (CtxBind y (over_ty b φx))) ->
  my ⊨ ty_denote_gas
      (Nat.max (cty_depth (over_ty b φx)) (cty_depth τ))
      ((<[LVFree y := TBase b]>
        (atom_env_to_lty_env (erase_ctx Γ))))
      (over_ty b φx) (tret (vfvar y)) ->
  my ⊨ ty_denote_gas
      (cty_depth (fix_rec_call_ty b y (over_ty b φx) τ))
      ((<[LVFree y := TBase b]>
        (atom_env_to_lty_env (erase_ctx Γ))))
      (fix_rec_call_ty b y (over_ty b φx) τ)
      (tret (vfix (TBase b →ₜ t) vf)).
Proof.
Admitted.
