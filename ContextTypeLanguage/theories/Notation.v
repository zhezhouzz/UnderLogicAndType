(** * ContextTypeLanguage.Notation

    Public syntax notation for the pure context-type language layer. *)

From CoreLang Require Export SyntaxNotation.
From ContextTypeLanguage Require Export WF.
From Stdlib Require Import Arith.Wf_nat Lia.

Declare Scope cty_scope.
Declare Scope ctx_scope.
Declare Scope lvar_scope.
Delimit Scope cty_scope with cty.
Delimit Scope ctx_scope with ctx.
Delimit Scope lvar_scope with lvar.
Bind Scope cty_scope with context_ty.
Bind Scope ctx_scope with ctx.
Bind Scope lvar_scope with logic_var.
Bind Scope lvar_scope with lty_env.

Notation "'{' k '~>' x '}' τ" := (cty_open k x τ)
  (at level 20, k constr, only printing,
   format "{ k ~> x } τ") : cty_scope.
Notation "τ '^^' x" := (cty_open 0 x τ)
  (at level 20, only printing) : cty_scope.
Notation "'↑{' k '}' τ" := (cty_shift k τ)
  (at level 20, k constr, only printing,
   format "↑{ k }  τ") : cty_scope.
Notation "τ '↑'" := (cty_shift 0 τ)
  (at level 20, only printing,
   format "τ  ↑") : cty_scope.

Notation "'⌊' τ '⌋'" := (erase_ty τ)
  (at level 20, only printing,
   format "⌊ τ ⌋") : cty_scope.

Notation "'⌊' Γ '⌋'" := (erase_ctx Γ)
  (at level 20, only printing,
   format "⌊ Γ ⌋") : ctx_scope.

Notation "'FV' '(' τ ')'" := (fv_cty τ)
  (at level 10, only printing,
   format "FV ( τ )") : cty_scope.
Notation "'FV' '(' Γ ')'" := (ctx_fv Γ)
  (at level 10, only printing,
   format "FV ( Γ )") : ctx_scope.
Notation "'FV' '(' D ')'" := (lvars_fv D)
  (at level 10, only printing,
   format "FV ( D )") : lvar_scope.

Notation "'#ₗ' k" := (LVBound k)
  (at level 5, format "#ₗ k").

Notation "'$ₗ' x" := (LVFree x)
  (at level 5, format "$ₗ x").

Notation "'↑ₗ' Σ" := (atom_env_to_lty_env Σ)
  (at level 20, format "↑ₗ Σ").

Notation "'#ₗ' k" := (LVBound k)
  (at level 5, only parsing) : ctx_scope.

Notation "'$ₗ' x" := (LVFree x)
  (at level 5, only parsing) : ctx_scope.

Notation "'↑ₗ' Σ" := (atom_env_to_lty_env Σ)
  (at level 20, only parsing) : ctx_scope.

Notation "'Emp'" := CtxEmpty
  (at level 0, format "Emp") : ctx_scope.

Notation "x '∷' τ" := (CtxBind x τ)
  (at level 60, τ at level 200, no associativity,
   format "x  ∷  τ") : ctx_scope.
Notation "Γ1 ',,' Γ2" := (CtxComma Γ1 Γ2)
  (at level 61, left associativity,
   format "Γ1  ,,  Γ2") : ctx_scope.
Notation "Γ1 '∗' Γ2" := (CtxStar Γ1 Γ2)
  (at level 40, left associativity,
   format "Γ1  ∗  Γ2") : ctx_scope.
Notation "Γ1 '⊕' Γ2" := (CtxSum Γ1 Γ2)
  (at level 70, right associativity,
   format "Γ1  ⊕  Γ2") : ctx_scope.

Notation "τ1 '⊓' τ2" := (CTInter τ1 τ2)
  (at level 40, no associativity,
   format "τ1  ⊓  τ2") : cty_scope.
Notation "τ1 '⊔' τ2" := (CTUnion τ1 τ2)
  (at level 50, no associativity,
   format "τ1  ⊔  τ2") : cty_scope.
Notation "τ1 '⊕' τ2" := (CTSum τ1 τ2)
  (at level 70, right associativity,
   format "τ1  ⊕  τ2") : cty_scope.
Notation "τx '→' τ" := (CTArrow τx τ)
  (at level 99, right associativity,
   format "τx  →  τ") : cty_scope.
Notation "τx '-∗' τ" := (CTWand τx τ)
  (at level 60, right associativity,
   format "τx  -∗  τ") : cty_scope.

(** Lightweight normalization helpers for the syntax/type-language layer. *)


Ltac mopen_norm :=
  rewrite ?mopen_insert_norm;
  type_open_env_syntax_norm.

Ltac type_lvars_norm :=
  repeat match goal with
  | |- context[into_lvars ?X] =>
      let T := type of X in
      lazymatch T with
      | lvset => change (into_lvars X) with X
      | aset => change (into_lvars X) with (lvars_of_atoms X)
      | gmap atom ty => change (into_lvars X) with (lvars_of_atoms (dom X))
      | gmap logic_var ty => change (into_lvars X) with (dom X)
      end
  | H : context[into_lvars ?X] |- _ =>
      let T := type of X in
      lazymatch T with
      | lvset => change (into_lvars X) with X in H
      | aset => change (into_lvars X) with (lvars_of_atoms X) in H
      | gmap atom ty => change (into_lvars X) with (lvars_of_atoms (dom X)) in H
      | gmap logic_var ty => change (into_lvars X) with (dom X) in H
      end
  end.

Ltac type_env_norm :=
  type_open_env_syntax_norm;
  rewrite ?lvar_store_atom_dom_shift in *.

(** Small context-type abbreviations used by the paper-facing typing layer. *)

Fixpoint lvar_value_keys (v : value) : lvset :=
  match v with
  | vconst _ => ∅
  | vfvar x => {[LVFree x]}
  | vbvar k => {[LVBound k]}
  | vlam _ e => tm_lvars e
  | vfix _ vf => lvar_value_keys vf
  end.

Definition denote_lvar_value (σ : LStore (V := value)) (v : value) : option value :=
  match v with
  | vbvar k => (σ : gmap logic_var value) !! LVBound k
  | vfvar x => (σ : gmap logic_var value) !! LVFree x
  | vconst c => Some (vconst c)
  | vlam T e => Some (vlam T e)
  | vfix T vf => Some (vfix T vf)
  end.

Definition mk_q_eq (v1 v2 : value) : type_qualifier :=
  tqual (lvar_value_keys v1 ∪ lvar_value_keys v2)
    (fun σ => denote_lvar_value (lso_store σ) v1 =
              denote_lvar_value (lso_store σ) v2).

(** Default well-founded orders used by context-type fixed points.  This is
    the HAT-style construction: each base type chooses a measure into [nat],
    and recursive calls are required to decrease under that measure. *)
Definition constant_measure_for_base (b : base_ty) (c : constant) : nat :=
  match b, c with
  | TNat, cnat n => n
  | TNat, cbool false => 0
  | TNat, cbool true => 1
  | TBool, cbool false => 0
  | TBool, cbool true => 1
  | TBool, cnat n => n
  end.

Definition constant_lt_for_base (b : base_ty) : constant -> constant -> Prop :=
  ltof _ (constant_measure_for_base b).

Lemma constant_lt_for_base_wf b :
  well_founded (constant_lt_for_base b).
Proof.
  unfold constant_lt_for_base.
  apply well_founded_ltof.
Qed.

Notation " c1 '≺[' b ']' c2 " :=
  (constant_lt_for_base b c1 c2) (at level 20, b at next level).

Definition mk_q_lt_base (b : base_ty) (v1 v2 : value) : type_qualifier :=
  tqual (lvar_value_keys v1 ∪ lvar_value_keys v2)
    (fun σ =>
       exists c1 c2,
         denote_lvar_value (lso_store σ) v1 = Some (vconst c1) /\
         denote_lvar_value (lso_store σ) v2 = Some (vconst c2) /\
         c1 ≺[b] c2).

Definition over_ty (b : base_ty) (φ : type_qualifier) : context_ty :=
  CTOver b φ.

Definition under_ty (b : base_ty) (φ : type_qualifier) : context_ty :=
  CTUnder b φ.

Notation "'{:' b '|' φ '}'" := (over_ty b φ)
  (at level 0, b at level 200, φ at level 200,
   format "{: b  |  φ }") : cty_scope.
Notation "'[:' b '|' φ ']'" := (under_ty b φ)
  (at level 0, b at level 200, φ at level 200,
   format "[: b  |  φ ]") : cty_scope.

Definition precise_ty (b : base_ty) (φ : type_qualifier) : context_ty :=
  CTInter (over_ty b φ) (under_ty b φ).

Definition primop_ty
    (arg_b : base_ty) (arg_φ : type_qualifier)
    (ret_b : base_ty) (ret_φ : type_qualifier) : context_ty :=
  CTArrow (over_ty arg_b arg_φ) (precise_ty ret_b ret_φ).

Definition fix_rec_call_ty
    (b : base_ty) (x : atom) (τx τ : context_ty) : context_ty :=
  CTArrow
    (CTInter τx (over_ty b (mk_q_lt_base b (vbvar 0) (vfvar x))))
    τ.

Ltac cty_depth_norm :=
  cbn [cty_depth over_ty under_ty precise_ty primop_ty fix_rec_call_ty];
  rewrite ?cty_open_preserves_depth, ?cty_shift_preserves_depth.

Ltac cty_depth_norm_in H :=
  cbn [cty_depth over_ty under_ty precise_ty primop_ty fix_rec_call_ty] in H;
  rewrite ?cty_open_preserves_depth in H;
  rewrite ?cty_shift_preserves_depth in H.

Ltac cty_depth_solve :=
  cty_depth_norm; lia.

Lemma erase_fix_rec_call_ty b x τx τ t :
  erase_ty τx = TBase b ->
  erase_ty τ = t ->
  erase_ty (fix_rec_call_ty b x τx τ) = (TBase b →ₜ t).
Proof.
  intros Hτx Hτ.
  unfold fix_rec_call_ty, over_ty.
  cbn [erase_ty].
  congruence.
Qed.

Lemma fv_cty_fix_rec_call_ty_subset b x τx τ :
  fv_cty (fix_rec_call_ty b x τx τ) ⊆
    fv_cty τx ∪ {[x]} ∪ fv_cty τ.
Proof.
  intros a Ha.
  unfold fix_rec_call_ty, over_ty, mk_q_lt_base in Ha.
  cty_fv_syntax_norm_in Ha.
  cbn [qual_vars qual_lvars lvar_value_keys] in Ha.
  rewrite !context_ty_lvars_fv_at in Ha.
  rewrite !lvars_fv_lvars_at_depth in Ha.
  repeat rewrite lvars_fv_union in Ha.
  repeat rewrite lvars_fv_singleton_bound in Ha.
  repeat rewrite lvars_fv_singleton_free in Ha.
  apply elem_of_union in Ha as [Ha_left | Haτ].
  - apply elem_of_union in Ha_left as [Haτx | Ha_mid].
    + apply elem_of_union_l. apply elem_of_union_l. exact Haτx.
    + apply elem_of_union in Ha_mid as [Ha_empty | Hay].
      * rewrite elem_of_empty in Ha_empty. contradiction.
      * apply elem_of_union_l. apply elem_of_union_r. exact Hay.
  - apply elem_of_union_r. exact Haτ.
Qed.

Lemma fv_cty_fix_rec_call_ty_fresh b x τx τ z :
  z <> x ->
  z ∉ fv_cty τx ->
  z ∉ fv_cty τ ->
  z ∉ fv_cty (fix_rec_call_ty b x τx τ).
Proof.
  intros Hzx Hzτx Hzτ Hzbad.
  pose proof (fv_cty_fix_rec_call_ty_subset b x τx τ z Hzbad)
    as Hzsub.
  better_set_solver.
Qed.

Lemma fv_cty_over_lt_bound_fvar b x :
  fv_cty (over_ty b (mk_q_lt_base b (vbvar 0) (vfvar x))) = {[x]}.
Proof.
  unfold over_ty, mk_q_lt_base, fv_cty, context_ty_lvars.
  cbn [context_ty_lvars_at qual_vars qual_lvars lvar_value_keys].
  rewrite lvars_at_depth_union.
  rewrite lvars_at_depth_singleton_bound0_succ.
  rewrite lvars_at_depth_singleton_free.
  rewrite lvars_fv_union, lvars_fv_empty, lvars_fv_singleton_free.
  apply set_eq. intros a. set_unfold. tauto.
Qed.

Lemma lc_context_ty_over_lt_bound_fvar b x :
  lc_context_ty (over_ty b (mk_q_lt_base b (vbvar 0) (vfvar x))).
Proof.
  unfold lc_context_ty, over_ty, mk_q_lt_base.
  cbn [cty_lc_at qual_vars qual_lvars lvar_value_keys lvars_lc_at].
  intros k Hk.
  rewrite lvars_bv_union in Hk.
  apply elem_of_union in Hk as [Hk | Hk].
  - rewrite lvars_bv_elem in Hk.
    apply elem_of_singleton in Hk.
    inversion Hk. subst. lia.
  - rewrite lvars_bv_elem in Hk.
    apply elem_of_singleton in Hk.
    discriminate.
Qed.

Lemma fv_cty_over_lt_bound_fvar_fresh b x z :
  z <> x ->
  z ∉ fv_cty (over_ty b (mk_q_lt_base b (vbvar 0) (vfvar x))).
Proof.
  intros Hzx.
  rewrite fv_cty_over_lt_bound_fvar.
  intros Hz. apply elem_of_singleton in Hz. congruence.
Qed.

Lemma lc_context_ty_fix_rec_call_ty b x τx τ :
  lc_context_ty τx ->
  lc_context_ty τ ->
  lc_context_ty (fix_rec_call_ty b x τx τ).
Proof.
  intros Hτx Hτ.
  unfold lc_context_ty, fix_rec_call_ty.
  cbn [cty_lc_at].
  split.
  - split.
    + exact Hτx.
    + apply lc_context_ty_over_lt_bound_fvar.
  - eapply (cty_lc_at_mono_depth 0 1); [lia|exact Hτ].
Qed.

Lemma cty_open_shift_fix_rec_call_ty_fresh b x z τx τ :
  z <> x ->
  z ∉ fv_cty τx ->
  z ∉ fv_cty τ ->
  lc_context_ty τx ->
  lc_context_ty τ ->
  cty_open 0 z (cty_shift 0 (fix_rec_call_ty b x τx τ)) =
    fix_rec_call_ty b x τx τ.
Proof.
  intros Hzx Hzτx Hzτ Hτx Hτ.
  apply cty_open_shift_from_lc_fresh.
  - apply lc_context_ty_fix_rec_call_ty; assumption.
  - apply fv_cty_fix_rec_call_ty_fresh; assumption.
Qed.

Definition bool_qual (b : bool) : type_qualifier :=
  mk_q_eq (vbvar 0) (vconst (cbool b)).

Definition bool_precise_ty (b : bool) : context_ty :=
  precise_ty TBool (bool_qual b).

Definition const_precise_ty (c : constant) : context_ty :=
  precise_ty (base_ty_of_const c) (mk_q_eq (vbvar 0) (vconst c)).

Notation "'b0:c=' c" := (mk_q_eq (vbvar 0) (vconst c))
  (at level 5, format "b0:c= c").
