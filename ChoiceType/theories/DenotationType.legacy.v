(** * ChoiceType.DenotationType

    Choice-type denotation and formula-locality lemmas. *)

From Stdlib Require Import Logic.FunctionalExtensionality.
From LocallyNameless Require Import Tactics.
From CoreLang Require Import Instantiation InstantiationProps BasicTypingProps
  Sugar.
From ChoiceLogic Require Import FormulaDerived.
From ChoiceType Require Export DenotationEnv.
From ChoiceType Require Import BasicStore BasicTyping LocallyNamelessProps.

Local Notation FQ := FormulaQ.

(** ** Type denotation

    [denot_ty_lvar Σe Στ τ e] is the recursive semantic content of
    "expression [e] has type [τ]" under erased basic environments [Σe] and
    [Στ], including the obligations every denotation needs: basic typing,
    closed resources, and deterministic result reachability.

    The recursion is structural on [τ].  [denot_ty_body_lvar] is the one-step
    view used by proofs to peel the outer obligation layer.
    Expression-result atoms and fresh representatives are driven by the
    environment domains.  The regularity assumptions that [fv_tm e] and
    [fv_cty τ] are contained in the environment are supplied by the basic
    typing conjunct. *)

Definition expr_total_with_store (X : aset) (e : tm)
    (ρ : Store) (m : WfWorld) : Prop :=
  (∀ σ, (m : World) σ → store_closed (store_restrict (ρ ∪ σ) X)) ∧
  ∀ σ, (m : World) σ →
    ∃ vx, subst_map (store_restrict (ρ ∪ σ) X) e →* tret vx.

Fixpoint value_lvars (v : value) : lvset :=
  match v with
  | vconst _ => ∅
  | vfvar x => {[LVFree x]}
  | vbvar k => {[LVBound k]}
  | vlam _ e => tm_lvars e
  | vfix _ vf => value_lvars vf
  end
with tm_lvars (e : tm) : lvset :=
  match e with
  | tret v => value_lvars v
  | tlete e1 e2 => tm_lvars e1 ∪ tm_lvars e2
  | tprim _ v => value_lvars v
  | tapp v1 v2 => value_lvars v1 ∪ value_lvars v2
  | tmatch v et ef => value_lvars v ∪ tm_lvars et ∪ tm_lvars ef
  end.

Fixpoint choice_ty_lvars (τ : choice_ty) : lvset :=
  match τ with
  | CTOver _ φ => qual_vars φ
  | CTUnder _ φ => qual_vars φ
  | CTInter τ1 τ2 => choice_ty_lvars τ1 ∪ choice_ty_lvars τ2
  | CTUnion τ1 τ2 => choice_ty_lvars τ1 ∪ choice_ty_lvars τ2
  | CTSum τ1 τ2 => choice_ty_lvars τ1 ∪ choice_ty_lvars τ2
  | CTArrow τx τ => choice_ty_lvars τx ∪ choice_ty_lvars τ
  | CTWand τx τ => choice_ty_lvars τx ∪ choice_ty_lvars τ
  end.

Definition closed_resource_lvar
    (Σ : lty_env) (η : gmap nat atom) (m : WfWorld) : Prop :=
  world_closed_on (lvars_to_atoms η (dom Σ)) m.

Definition expr_total_lvar
    (Σ : lty_env) (e : tm) (η : gmap nat atom)
    (ρ : Store) (m : WfWorld) : Prop :=
  expr_total_with_store (lvars_to_atoms η (dom Σ ∪ tm_lvars e))
    (open_tm_env η e) ρ m.

Lemma tm_lvars_open k x e :
  tm_lvars ({k ~> x} e) = lvars_open k x (tm_lvars e).
Proof.
  (* Syntax-only open law for the lvars read by a term. *)
Admitted.

Lemma choice_ty_lvars_open k x τ :
  choice_ty_lvars ({k ~> x} τ) = lvars_open k x (choice_ty_lvars τ).
Proof.
  (* Syntax-only open law for the lvars read by a choice type. *)
Admitted.

Lemma closed_resource_lvar_open k x η Σ m :
  closed_resource_lvar ({k ~> x} Σ) η m =
  closed_resource_lvar Σ (<[k := x]> η) m.
Proof.
  (* Predicate-level normalization: opening the environment in syntax is the
     same as interpreting it with the binder map extended. *)
Admitted.

Lemma expr_total_lvar_open k x η Σ e ρ m :
  expr_total_lvar ({k ~> x} Σ) ({k ~> x} e) η ρ m =
  expr_total_lvar Σ e (<[k := x]> η) ρ m.
Proof.
  (* Predicate-level normalization for totality.  The store domain and the
     opened term are both normalized by the lvar/open syntax laws. *)
Admitted.

Definition lty_env_open_lvars (η : gmap nat atom) (Σ : lty_env) : lty_env :=
  map_fold (fun k x acc => lty_env_open_one k x acc) Σ η.

Lemma lty_env_open_lvars_open_one k x η Σ :
  lty_env_open_lvars η (lty_env_open_one k x Σ) =
  lty_env_open_lvars (<[k := x]> η) Σ.
Proof.
  (* Standard mopen composition for lvar environments with lvar output. *)
Admitted.

Definition basic_qualifier_lvar_body (D : lvset) (q : type_qualifier) : Prop :=
  qual_vars q ⊆ lvars_shift D ∪ {[LVBound 0]}.

Inductive basic_choice_ty_lvar : lvset → choice_ty → Prop :=
  | BasicL_CTOver D b φ :
      basic_qualifier_lvar_body D φ →
      basic_choice_ty_lvar D (CTOver b φ)
  | BasicL_CTUnder D b φ :
      basic_qualifier_lvar_body D φ →
      basic_choice_ty_lvar D (CTUnder b φ)
  | BasicL_CTInter D τ1 τ2 :
      basic_choice_ty_lvar D τ1 →
      basic_choice_ty_lvar D τ2 →
      erase_ty τ1 = erase_ty τ2 →
      basic_choice_ty_lvar D (CTInter τ1 τ2)
  | BasicL_CTUnion D τ1 τ2 :
      basic_choice_ty_lvar D τ1 →
      basic_choice_ty_lvar D τ2 →
      erase_ty τ1 = erase_ty τ2 →
      basic_choice_ty_lvar D (CTUnion τ1 τ2)
  | BasicL_CTSum D τ1 τ2 :
      basic_choice_ty_lvar D τ1 →
      basic_choice_ty_lvar D τ2 →
      erase_ty τ1 = erase_ty τ2 →
      basic_choice_ty_lvar D (CTSum τ1 τ2)
  | BasicL_CTArrow D τx τ :
      basic_choice_ty_lvar D τx →
      basic_choice_ty_lvar (lvars_shift D ∪ {[LVBound 0]}) τ →
      basic_choice_ty_lvar D (CTArrow τx τ)
  | BasicL_CTWand D τx τ :
      basic_choice_ty_lvar D τx →
      basic_choice_ty_lvar (lvars_shift D ∪ {[LVBound 0]}) τ →
      basic_choice_ty_lvar D (CTWand τx τ).

Inductive value_has_lty : lty_env → value → ty → Prop :=
  | VTL_Const Σ c :
      value_has_lty Σ (vconst c) (TBase (base_ty_of_const c))
  | VTL_FVar Σ x T :
      Σ !! LVFree x = Some T →
      value_has_lty Σ (vfvar x) T
  | VTL_BVar Σ k T :
      Σ !! LVBound k = Some T →
      value_has_lty Σ (vbvar k) T
  | VTL_Lam Σ s T e (L : aset) :
      (∀ x, x ∉ L →
        tm_has_lty (<[LVFree x := s]> Σ) (e ^^ x) T) →
      value_has_lty Σ (vlam s e) (s →ₜ T)
  | VTL_Fix Σ sx T vf (L : aset) :
      (∀ x, x ∉ L →
        value_has_lty (<[LVFree x := sx]> Σ) (vf ^^ x)
          ((sx →ₜ T) →ₜ T)) →
      value_has_lty Σ (vfix (sx →ₜ T) vf) (sx →ₜ T)

with tm_has_lty : lty_env → tm → ty → Prop :=
  | TTL_Ret Σ v T :
      value_has_lty Σ v T →
      tm_has_lty Σ (tret v) T
  | TTL_Let Σ T1 T2 e1 e2 (L : aset) :
      tm_has_lty Σ e1 T1 →
      (∀ x, x ∉ L →
        tm_has_lty (<[LVFree x := T1]> Σ) (e2 ^^ x) T2) →
      tm_has_lty Σ (tlete e1 e2) T2
  | TTL_Op Σ op v arg_b ret_b :
      prim_op_type op = (arg_b, ret_b) →
      value_has_lty Σ v (TBase arg_b) →
      tm_has_lty Σ (tprim op v) (TBase ret_b)
  | TTL_App Σ s1 s2 v1 v2 :
      value_has_lty Σ v1 (s1 →ₜ s2) →
      value_has_lty Σ v2 s1 →
      tm_has_lty Σ (tapp v1 v2) s2
  | TTL_Match Σ v T et ef :
      value_has_lty Σ v (TBase TBool) →
      tm_has_lty Σ et T →
      tm_has_lty Σ ef T →
      tm_has_lty Σ (tmatch v et ef) T.

Scheme value_has_lty_mut := Induction for value_has_lty Sort Prop
  with tm_has_lty_mut    := Induction for tm_has_lty    Sort Prop.
Combined Scheme has_lty_mutind from value_has_lty_mut, tm_has_lty_mut.

Definition basic_value_typing_lvar (Σ : lty_env) (v : value) (T : ty) : Prop :=
  value_has_lty Σ v T.

Definition basic_typing_lvar (Σ : lty_env) (e : tm) (T : ty) : Prop :=
  tm_has_lty Σ e T.

Lemma lty_env_open_lvars_atom_env η Σ :
  lty_env_open_lvars η (atom_env_to_lty_env Σ) = atom_env_to_lty_env Σ.
Proof.
  (* Opening bound lvars does not affect a purely free-atom environment. *)
Admitted.

Lemma basic_choice_ty_to_lvar_atom_env Σ τ :
  basic_choice_ty (dom Σ) τ →
  basic_choice_ty_lvar (dom (atom_env_to_lty_env Σ)) τ.
Proof.
  (* Formation bridge from the closed atom judgment to the lvar judgment. *)
Admitted.

Lemma basic_choice_ty_lvar_atom_env_to_basic Σ τ :
  basic_choice_ty_lvar (dom (atom_env_to_lty_env Σ)) τ →
  basic_choice_ty (dom Σ) τ.
Proof.
  (* Formation bridge back to the closed atom judgment. *)
Admitted.

Lemma tm_has_type_to_lty_atom_env Γ e T :
  Γ ⊢ₑ e ⋮ T →
  tm_has_lty (atom_env_to_lty_env Γ) e T.
Proof.
  (* Erased core typing embeds into the lvar-aware typing judgment. *)
Admitted.

Lemma tm_has_lty_atom_env_to_type Γ e T :
  tm_has_lty (atom_env_to_lty_env Γ) e T →
  Γ ⊢ₑ e ⋮ T.
Proof.
  (* Lvar-aware typing over a purely atom environment is ordinary typing. *)
Admitted.

Definition FBasicTypingIn (Σe Στ : lty_env) (τ : choice_ty) (e : tm) : FQ :=
  FStoreResourceAtom (dom Σe ∪ dom Στ ∪ choice_ty_lvars τ ∪ tm_lvars e)
    (fun η _ _ =>
      let Γe := lty_env_open_lvars η Σe in
      let Γτ := lty_env_open_lvars η Στ in
      let τη := open_cty_env η τ in
      let eη := open_tm_env η e in
      basic_choice_ty_lvar (dom Γτ) τη ∧
      basic_typing_lvar Γe eη (erase_ty τη)).

Definition FClosedResourceIn (Σ : lty_env) : FQ :=
  FStoreResourceAtom (dom Σ)
    (fun η _ m => closed_resource_lvar Σ η m).

Definition FStrongTotalIn (Σ : lty_env) (e : tm) : FQ :=
  FStoreResourceAtom (dom Σ ∪ tm_lvars e)
    (fun η ρ m => expr_total_lvar Σ e η ρ m).

Definition FResultBasicWorld
    (Σ : lty_env) (b : base_ty) (D : lvset) : FQ :=
  FStoreResourceAtom (lty_env_bvar_scope Σ ∪ D ∪ {[LVBound 0]})
    (fun η _ m =>
      match η !! 0 with
      | Some ν =>
          world_has_type_on (<[ν := TBase b]> (lty_env_open η Σ))
            (lvars_to_atoms η D ∪ {[ν]}) m
      | None => False
      end).

Definition denot_ty_obligations
    (Σe Στ : lty_env) (τ : choice_ty) (e : tm) (φ : FQ) : FQ :=
  FAnd (FBasicTypingIn Σe Στ τ e)
    (FAnd (FClosedResourceIn Σe)
      (FAnd (FStrongTotalIn Σe e) φ)).

Lemma formula_open_FBasicTypingIn k x Σe Στ τ e :
  formula_open k x (FBasicTypingIn Σe Στ τ e) =
  FBasicTypingIn ({k ~> x} Σe) ({k ~> x} Στ)
    ({k ~> x} τ) ({k ~> x} e).
Proof.
  unfold FBasicTypingIn.
  denot_lvars_norm.
  rewrite formula_open_FStoreResourceAtom_lvars.
  unfold lvars_open.
  rewrite set_map_union_L.
  fold (lvars_open k x (dom Σe)).
  fold (lvars_open k x (dom Στ)).
  rewrite <- !lty_env_open_one_dom.
  f_equal.
  f_equal.
  apply functional_extensionality; intro η.
  apply functional_extensionality; intro ρ.
  apply functional_extensionality; intro m.
  cbn [open_one open_tm_atom_inst open_cty_atom_inst open_lty_env_atom_inst].
  rewrite !lty_env_open_lvars_open_one.
  rewrite open_cty_env_open_cty.
  rewrite <- open_tm_env_open_tm.
  reflexivity.
Qed.

Lemma formula_open_FClosedResourceIn k x Σ :
  formula_open k x (FClosedResourceIn Σ) =
  FClosedResourceIn ({k ~> x} Σ).
Proof.
  unfold FClosedResourceIn.
  denot_lvars_norm.
  rewrite formula_open_FStoreResourceAtom_lvars.
  rewrite lty_env_open_one_dom.
  f_equal.
  f_equal.
  apply functional_extensionality; intro η.
  apply functional_extensionality; intro ρ.
  apply functional_extensionality; intro m.
  change (world_closed_on (dom (lty_env_open (<[k:=x]> η) Σ)) m =
          world_closed_on (dom (lty_env_open η (lty_env_open_one k x Σ))) m).
  rewrite lty_env_open_one_open.
  reflexivity.
Qed.

Lemma formula_open_FStrongTotalIn k x Σ e :
  formula_open k x (FStrongTotalIn Σ e) =
  FStrongTotalIn ({k ~> x} Σ) ({k ~> x} e).
Proof.
  unfold FStrongTotalIn.
  denot_lvars_norm.
  rewrite formula_open_FStoreResourceAtom_lvars.
  rewrite lty_env_open_one_dom.
  f_equal.
  f_equal.
  apply functional_extensionality; intro η.
  apply functional_extensionality; intro ρ.
  apply functional_extensionality; intro m.
  change (expr_total_with_store
            (dom (lty_env_open (<[k:=x]> η) Σ))
            (open_tm_env (<[k:=x]> η) e) ρ m =
          expr_total_with_store
            (dom (lty_env_open η (lty_env_open_one k x Σ)))
            (open_tm_env η (open_tm k (vfvar x) e)) ρ m).
  rewrite lty_env_open_one_open.
  rewrite open_tm_env_open_tm.
  reflexivity.
Qed.

Lemma formula_open_denot_ty_obligations k x Σe Στ τ e φ :
  formula_open k x (denot_ty_obligations Σe Στ τ e φ) =
  denot_ty_obligations ({k ~> x} Σe) ({k ~> x} Στ)
    ({k ~> x} τ) ({k ~> x} e) (formula_open k x φ).
Proof.
  unfold denot_ty_obligations.
  rewrite !formula_open_and.
  rewrite formula_open_FBasicTypingIn.
  rewrite formula_open_FClosedResourceIn.
  rewrite formula_open_FStrongTotalIn.
  reflexivity.
Qed.

Lemma formula_open_FExprContIn_lty k x Σ e Q :
  formula_open k x (FExprContIn Σ e Q) =
  FExprContIn ({k ~> x} Σ) ({k ~> x} e) (formula_open (S k) x Q).
Proof.
  rewrite formula_open_FExprContIn_raw.
  unfold FExprContIn.
  rewrite formula_open_FExprResultAtLvar_raw.
  cbn [into_lvars into_lvars_lvset].
  change (into_lvars (lvars_shift (into_lvars Σ))) with
    (lvars_shift (dom Σ)).
  change (into_lvars ({k ~> x} Σ)) with (dom (lty_env_open_one k x Σ)).
  rewrite lvars_open_shift_dom.
  f_equal.
  f_equal.
  - unfold FExprResultAtLvar.
    cbn [into_lvars into_lvars_lvset].
    change (into_lvars (lvars_shift (dom (lty_env_open_one k x Σ))))
      with (lvars_shift (dom (lty_env_open_one k x Σ))).
    rewrite lvars_open_shift_dom_union_bound0.
    f_equal.
    f_equal.
    apply functional_extensionality; intro η.
    apply functional_extensionality; intro σ.
    apply functional_extensionality; intro w.
    cbn [logic_var_to_atom].
    rewrite lookup_insert_ne by lia.
    rewrite <- lvars_to_atoms_shift_open_one.
    rewrite lty_env_open_one_dom.
    rewrite <- open_tm_env_shift_open_one.
    reflexivity.
Qed.

Lemma formula_open_FResultBasicWorld_under_result k x Σ b D :
  formula_open (S k) x
    (FResultBasicWorld (lty_env_shift Σ) b D) =
  FResultBasicWorld (lty_env_shift ({k ~> x} Σ)) b
    (lvars_open (S k) x D).
Proof.
  unfold FResultBasicWorld.
  rewrite formula_open_FStoreResourceAtom_lvars.
  rewrite lty_env_bvar_scope_open_one_shift_under_result.
  f_equal.
  f_equal.
  apply functional_extensionality; intro η.
  apply functional_extensionality; intro ρ.
  apply functional_extensionality; intro m.
  rewrite lookup_insert_ne by lia.
  rewrite lty_env_open_shift_open_one_under_result.
  rewrite lvars_to_atoms_open.
  reflexivity.
Qed.

Lemma FResultBasicWorld_fv Σ b D :
  formula_fv (FResultBasicWorld Σ b D) =
  lvars_fv (lty_env_bvar_scope Σ ∪ D ∪ {[LVBound 0]}).
Proof.
  unfold FResultBasicWorld.
  apply formula_fv_FStoreResourceAtom_lvars.
Qed.

Lemma FResultBasicWorld_fv_atom_env_subset Σ b D :
  lvars_fv D ⊆ dom Σ →
  formula_fv (FResultBasicWorld (atom_env_to_lty_env Σ) b D) ⊆ dom Σ.
Proof.
  intros HD.
  rewrite FResultBasicWorld_fv.
  unfold lty_env_bvar_scope.
  rewrite atom_env_to_lty_env_dom.
  rewrite lvars_bv_of_atoms.
  rewrite lvars_fv_union, lvars_fv_union.
  rewrite lvars_fv_of_bvars, lvars_fv_singleton_bound.
  set_solver.
Qed.

Lemma FResultBasicWorld_fv_atom_env Σ b D :
  formula_fv (FResultBasicWorld (atom_env_to_lty_env Σ) b D) = lvars_fv D.
Proof.
  rewrite FResultBasicWorld_fv.
  unfold lty_env_bvar_scope.
  rewrite atom_env_to_lty_env_dom.
  rewrite lvars_bv_of_atoms.
  rewrite lvars_fv_union, lvars_fv_union.
  rewrite lvars_fv_of_bvars, lvars_fv_singleton_bound.
  set_solver.
Qed.

Lemma FResultBasicWorld_open_fv_atom_env Σ D ν :
  lvars_fv
    (lvars_open 0 ν
      (lty_env_bvar_scope (atom_env_to_lty_env Σ) ∪ D ∪ {[LVBound 0]})) =
  lvars_fv D ∪ {[ν]}.
Proof.
  rewrite lvars_fv_open.
  unfold lty_env_bvar_scope.
  rewrite atom_env_to_lty_env_dom.
  rewrite lvars_bv_of_atoms.
  rewrite ?lvars_fv_union.
  rewrite ?lvars_fv_of_bvars.
  rewrite ?lvars_fv_union.
  rewrite ?lvars_fv_singleton_bound.
  destruct decide as [_|Hnot].
  - set_solver.
  - exfalso.
    apply Hnot.
    replace (lvars_of_bvars ∅ ∪ D ∪ {[LVBound 0]})
      with ((lvars_of_bvars ∅ ∪ D) ∪ {[LVBound 0]}) by set_solver.
    apply lvars_bv_contains_bound_singleton.
Qed.

Lemma FResultBasicWorld_open_fv_atom_env_into Σ D ν :
  lvars_fv
    (lvars_open 0 ν
      (into_lvars
        (lty_env_bvar_scope (atom_env_to_lty_env Σ) ∪ D ∪ {[LVBound 0]}))) =
  lvars_fv D ∪ {[ν]}.
Proof.
  cbn [into_lvars into_lvars_lvset].
  apply FResultBasicWorld_open_fv_atom_env.
Qed.

Lemma FResultBasicWorld_insert_fresh_open_equiv
    Σ x T b D ν :
  x ∉ dom Σ ∪ lvars_fv D →
  x <> ν →
  formula_store_equiv
    (formula_open 0 ν
      (FResultBasicWorld (atom_env_to_lty_env (<[x := T]> Σ)) b D))
    (formula_open 0 ν
      (FResultBasicWorld (atom_env_to_lty_env Σ) b D)).
Proof.
  intros Hx Hxν ρ m.
  unfold FResultBasicWorld, FStoreResourceAtom.
  cbn [formula_open formula_fv lqual_open lqual_dom into_lvars
    into_lvars_lvset stale stale_logic_qualifier].
  unfold res_models_with_store.
  cbn [formula_measure res_models_with_store_fuel formula_scoped_in_world
    formula_fv lqual_dom logic_qualifier_denote lqual_prop].
  rewrite !FResultBasicWorld_open_fv_atom_env_into.
  rewrite !lty_env_open_atom_env.
  rewrite lookup_insert_eq.
  split; intros [Hscope [m0 [Hscope0 [Htyped Hle]]]]; split.
  - unfold formula_scoped_in_world in *.
    cbn [formula_fv lqual_dom stale stale_logic_qualifier] in *.
    rewrite !FResultBasicWorld_open_fv_atom_env_into in *.
    exact Hscope.
  - exists m0. split.
    + unfold formula_scoped_in_world in *.
      cbn [formula_fv lqual_dom stale stale_logic_qualifier] in *.
      rewrite !FResultBasicWorld_open_fv_atom_env_into in *.
      exact Hscope0.
    + split; [| exact Hle].
      pose proof (world_has_type_on_insert_under_result_irrel
        Σ (lvars_to_atoms (<[0:=ν]> ∅) D)
        (res_restrict m0 (lvars_fv D ∪ {[ν]}))
        x T ν b ltac:(
          intros Hbad;
          pose proof (lvars_to_atoms_insert_empty_subset 0 ν D x Hbad);
          set_solver)) as Hiff.
      exact (proj1 Hiff Htyped).
  - unfold formula_scoped_in_world in *.
    cbn [formula_fv lqual_dom stale stale_logic_qualifier] in *.
    rewrite !FResultBasicWorld_open_fv_atom_env_into in *.
    exact Hscope.
  - exists m0. split.
    + unfold formula_scoped_in_world in *.
      cbn [formula_fv lqual_dom stale stale_logic_qualifier] in *.
      rewrite !FResultBasicWorld_open_fv_atom_env_into in *.
      exact Hscope0.
    + split; [| exact Hle].
      pose proof (world_has_type_on_insert_under_result_irrel
        Σ (lvars_to_atoms (<[0:=ν]> ∅) D)
        (res_restrict m0 (lvars_fv D ∪ {[ν]}))
        x T ν b ltac:(
          intros Hbad;
          pose proof (lvars_to_atoms_insert_empty_subset 0 ν D x Hbad);
          set_solver)) as Hiff.
      exact (proj2 Hiff Htyped).
Qed.

Lemma FResultBasicWorld_insert_fresh_open_fv
    Σ x T b D ν :
  x ∉ dom Σ ∪ lvars_fv D →
  formula_fv
    (formula_open 0 ν
      (FResultBasicWorld (atom_env_to_lty_env (<[x := T]> Σ)) b D)) =
  formula_fv
    (formula_open 0 ν
      (FResultBasicWorld (atom_env_to_lty_env Σ) b D)).
Proof.
  intros _.
  unfold FResultBasicWorld, FStoreResourceAtom.
  cbn [formula_open formula_fv lqual_open lqual_dom into_lvars
    into_lvars_lvset stale stale_logic_qualifier].
  rewrite !FResultBasicWorld_open_fv_atom_env_into.
  reflexivity.
Qed.

Lemma expr_total_with_store_empty_restrict X e m :
  world_closed_on X m →
  fv_tm e ⊆ X →
  expr_total_on e m →
  expr_total_with_store X e ∅ (res_restrict m X).
Proof.
  intros Hclosed HfvX [_ Htotal].
  split.
  - intros σ Hσ.
    destruct (res_restrict_lift_store m X σ Hσ) as [σm [Hσm Hrestrict]].
    assert (Heq : store_restrict ((∅ : Store) ∪ σ) X = store_restrict σm X).
    { rewrite map_empty_union.
      rewrite <- Hrestrict.
      rewrite store_restrict_twice_same.
      reflexivity. }
    rewrite Heq. apply Hclosed. exact Hσm.
  - intros σ Hσ.
    destruct (res_restrict_lift_store m X σ Hσ) as [σm [Hσm Hrestrict]].
    assert (Heq : store_restrict ((∅ : Store) ∪ σ) X = store_restrict σm X).
    { rewrite map_empty_union.
      rewrite <- Hrestrict.
      rewrite store_restrict_twice_same.
      reflexivity. }
    rewrite Heq.
    destruct (Htotal σm Hσm) as [vx Hsteps].
    exists vx.
    rewrite <- (subst_map_restrict_to_fv_from_superset e X σm HfvX
      (proj1 (Hclosed σm Hσm))).
    exact Hsteps.
Unshelve.
  all: try typeclasses eauto; try set_solver.
Qed.

Lemma FBasicTypingIn_atom_env_insert_fresh_models Σ x T τ e m :
  x ∉ dom Σ →
  x ∉ fv_cty τ ∪ fv_tm e →
  res_models m (FBasicTypingIn (atom_env_to_lty_env (<[x := T]> Σ))
    (atom_env_to_lty_env (<[x := T]> Σ)) τ e) →
  res_models m (FBasicTypingIn (atom_env_to_lty_env Σ)
    (atom_env_to_lty_env Σ) τ e).
Proof.
  (* Fresh-insert irrelevance for the lvar-aware basic atom.  This replaces the
     old proof that projected through closed atom typing. *)
Admitted.

Lemma FClosedResourceIn_atom_env_insert_restrict_models Σ x T m :
  x ∉ dom Σ →
  res_models m (FClosedResourceIn (atom_env_to_lty_env (<[x := T]> Σ))) →
  res_models (res_restrict m (dom Σ))
    (FClosedResourceIn (atom_env_to_lty_env Σ)).
Proof.
  intros HxΣ Hmodel.
  unfold FClosedResourceIn, res_models in *.
  pose proof (res_models_with_store_fuel_scoped _ _ _ _ Hmodel) as Hscope.
  eapply res_models_with_store_store_resource_atom_vars_elim in Hmodel
    as [m0 [Hscope0 [Hclosed Hle]]].
  eapply res_models_with_store_store_resource_atom_vars_witness_intro
    with (m0 := res_restrict m0 (dom Σ)).
  - unfold formula_scoped_in_world in *.
    rewrite !formula_fv_FStoreResourceAtom_lvars in *.
    rewrite !atom_env_to_lty_env_dom, !lvars_fv_of_atoms in *.
    rewrite dom_insert_L in Hscope.
    rewrite !dom_empty_L in *.
    cbn [world_dom raw_restrict].
    set_solver.
  - unfold formula_scoped_in_world in *.
    rewrite !formula_fv_FStoreResourceAtom_lvars in *.
    rewrite !atom_env_to_lty_env_dom, !lvars_fv_of_atoms in *.
    rewrite dom_insert_L in Hscope0.
    rewrite !dom_empty_L in *.
    cbn [world_dom raw_restrict].
    set_solver.
  - rewrite lty_env_open_atom_env.
    rewrite res_restrict_restrict_eq.
    rewrite atom_env_to_lty_env_dom, lvars_fv_of_atoms.
    replace (dom Σ ∩ dom Σ) with (dom Σ) by set_solver.
    rewrite lty_env_open_atom_env in Hclosed.
    rewrite atom_env_to_lty_env_dom, lvars_fv_of_atoms in Hclosed.
    rewrite dom_insert_L in Hclosed.
    assert (Hclosed_big :
        world_closed_on ({[x]} ∪ dom Σ) (res_restrict m0 (dom Σ))).
    { eapply (world_closed_on_le ({[x]} ∪ dom Σ)
        (res_restrict m0 (dom Σ))
        (res_restrict m0 ({[x]} ∪ dom Σ))).
      - apply res_restrict_mono. set_solver.
      - exact Hclosed.
    }
    intros σ Hσ.
    specialize (Hclosed_big σ Hσ).
    assert (Hdomσ : dom σ ⊆ dom Σ).
    { pose proof (wfworld_store_dom (res_restrict m0 (dom Σ)) σ Hσ).
      set_solver. }
    rewrite store_restrict_idemp in Hclosed_big by set_solver.
    rewrite store_restrict_idemp by exact Hdomσ.
    exact Hclosed_big.
  - eapply res_restrict_le_mono. exact Hle.
Qed.

Fixpoint denot_ty_body_lvar_gas
    (gas : nat) (Σe Στ : lty_env) (τ : choice_ty) (e : tm)
    {struct gas} : FQ :=
  match gas with
  | 0 => FTrue
  | S gas' =>
  match τ with
  | CTOver b φ =>
      FExprContIn Σe e (
        let Στr := lty_env_shift Στ in
        FAnd
          (FResultBasicWorld Στr b (qual_vars φ))
          (FFibVars (qual_vars φ)
       (FOver (FTypeQualifier φ))))
  | CTUnder b φ =>
      FExprContIn Σe e (
        let Στr := lty_env_shift Στ in
        FAnd
          (FResultBasicWorld Στr b (qual_vars φ))
          (FFibVars (qual_vars φ)
       (FUnder (FTypeQualifier φ))))
  | CTInter τ1 τ2 =>
      FAnd
        (denot_ty_obligations Σe Στ τ1 e
          (denot_ty_body_lvar_gas gas' Σe Στ τ1 e))
        (denot_ty_obligations Σe Στ τ2 e
          (denot_ty_body_lvar_gas gas' Σe Στ τ2 e))
  | CTUnion τ1 τ2 =>
      FOr
        (denot_ty_obligations Σe Στ τ1 e
          (denot_ty_body_lvar_gas gas' Σe Στ τ1 e))
        (denot_ty_obligations Σe Στ τ2 e
          (denot_ty_body_lvar_gas gas' Σe Στ τ2 e))
  | CTSum τ1 τ2 =>
      FPlus
        (denot_ty_obligations Σe Στ τ1 e
          (denot_ty_body_lvar_gas gas' Σe Στ τ1 e))
        (denot_ty_obligations Σe Στ τ2 e
          (denot_ty_body_lvar_gas gas' Σe Στ τ2 e))
  | CTArrow τx τ =>
      FForall (
        let Σex := <[LVBound 0 := erase_ty τx]> (lty_env_shift Σe) in
        let Στr := lty_env_shift Στ in
        let Στx := <[LVBound 0 := erase_ty τx]> (lty_env_shift Στ) in
          FImpl
            (denot_ty_obligations Σex Στr τx (tret (vbvar 0))
              (denot_ty_body_lvar_gas gas' Σex Στr τx (tret (vbvar 0))))
            (denot_ty_obligations Σex Στx τ (tapp_tm (tm_shift 0 e) (vbvar 0))
              (denot_ty_body_lvar_gas gas' Σex Στx τ
                (tapp_tm (tm_shift 0 e) (vbvar 0)))))
  | CTWand τx τ =>
      FForall (
        let Σex := <[LVBound 0 := erase_ty τx]> (lty_env_shift Σe) in
        let Στr := lty_env_shift Στ in
        let Στx := <[LVBound 0 := erase_ty τx]> (lty_env_shift Στ) in
          FWand
            (denot_ty_obligations Σex Στr τx (tret (vbvar 0))
              (denot_ty_body_lvar_gas gas' Σex Στr τx (tret (vbvar 0))))
            (denot_ty_obligations Σex Στx τ (tapp_tm (tm_shift 0 e) (vbvar 0))
              (denot_ty_body_lvar_gas gas' Σex Στx τ
                (tapp_tm (tm_shift 0 e) (vbvar 0)))))
  end
  end.

Definition denot_ty_body_lvar
    (Σe Στ : lty_env) (τ : choice_ty) (e : tm) : FQ :=
  denot_ty_body_lvar_gas (cty_depth τ) Σe Στ τ e.

Definition denot_ty_lvar_gas
    (gas : nat) (Σe Στ : lty_env) (τ : choice_ty) (e : tm)
    : FQ :=
  denot_ty_obligations Σe Στ τ e
    (denot_ty_body_lvar_gas gas Σe Στ τ e).

Definition denot_ty_lvar
    (Σe Στ : lty_env) (τ : choice_ty) (e : tm)
    : FQ :=
  denot_ty_lvar_gas (cty_depth τ) Σe Στ τ e.

Lemma denot_ty_body_lvar_gas_saturate τ :
  ∀ gas Σe Στ e,
    cty_depth τ <= gas →
    denot_ty_body_lvar_gas gas Σe Στ τ e =
    denot_ty_body_lvar_gas (cty_depth τ) Σe Στ τ e.
Proof.
  induction τ as [b φ|b φ|τ1 IH1 τ2 IH2|τ1 IH1 τ2 IH2
    |τ1 IH1 τ2 IH2|τx IHx τ IH|τx IHx τ IH];
    intros [|gas] Σe Στ e Hgas; cbn [cty_depth] in Hgas; try lia;
    cbn [denot_ty_body_lvar_gas cty_depth].
  - reflexivity.
  - reflexivity.
  - rewrite !(IH1 gas) by lia.
    rewrite !(IH1 (Nat.max (cty_depth τ1) (cty_depth τ2))) by lia.
    rewrite !(IH2 gas) by lia.
    rewrite !(IH2 (Nat.max (cty_depth τ1) (cty_depth τ2))) by lia.
    reflexivity.
  - rewrite !(IH1 gas) by lia.
    rewrite !(IH1 (Nat.max (cty_depth τ1) (cty_depth τ2))) by lia.
    rewrite !(IH2 gas) by lia.
    rewrite !(IH2 (Nat.max (cty_depth τ1) (cty_depth τ2))) by lia.
    reflexivity.
  - rewrite !(IH1 gas) by lia.
    rewrite !(IH1 (Nat.max (cty_depth τ1) (cty_depth τ2))) by lia.
    rewrite !(IH2 gas) by lia.
    rewrite !(IH2 (Nat.max (cty_depth τ1) (cty_depth τ2))) by lia.
    reflexivity.
  - rewrite !(IHx gas) by lia.
    rewrite !(IHx (Nat.max (cty_depth τx) (cty_depth τ))) by lia.
    rewrite !(IH gas) by lia.
    rewrite !(IH (Nat.max (cty_depth τx) (cty_depth τ))) by lia.
    reflexivity.
  - rewrite !(IHx gas) by lia.
    rewrite !(IHx (Nat.max (cty_depth τx) (cty_depth τ))) by lia.
    rewrite !(IH gas) by lia.
    rewrite !(IH (Nat.max (cty_depth τx) (cty_depth τ))) by lia.
    reflexivity.
Qed.

Lemma denot_ty_lvar_gas_saturate gas Σe Στ τ e :
  cty_depth τ <= gas →
  denot_ty_lvar_gas gas Σe Στ τ e = denot_ty_lvar Σe Στ τ e.
Proof.
  intros Hgas.
  unfold denot_ty_lvar, denot_ty_lvar_gas.
  rewrite denot_ty_body_lvar_gas_saturate by exact Hgas.
  reflexivity.
Qed.

Lemma denot_ty_obligations_body_gas_saturate gas Σe Στ τ e :
  cty_depth τ <= gas →
  denot_ty_obligations Σe Στ τ e
    (denot_ty_body_lvar_gas gas Σe Στ τ e) =
  denot_ty_lvar Σe Στ τ e.
Proof.
  intros Hgas.
  unfold denot_ty_lvar, denot_ty_lvar_gas.
  rewrite denot_ty_body_lvar_gas_saturate by exact Hgas.
  reflexivity.
Qed.

Lemma formula_open_denot_ty_body_lvar_gas k x gas Σe Στ τ e :
  formula_open k x (denot_ty_body_lvar_gas gas Σe Στ τ e) =
  denot_ty_body_lvar_gas gas
    (lty_env_open_one k x Σe)
    (lty_env_open_one k x Στ)
    (cty_open k x τ)
    (open_tm k (vfvar x) e).
Proof.
  (* Legacy strong syntax equality kept for old callers.  The new proof route
     should use [formula_store_equiv_open_denot_ty_body_lvar_gas], because
     qualifier atoms normalize by store-equivalence rather than definitional
     equality. *)
Admitted.

Lemma formula_open_denot_ty_lvar_gas k x gas Σe Στ τ e :
  formula_open k x (denot_ty_lvar_gas gas Σe Στ τ e) =
  denot_ty_lvar_gas gas
    (lty_env_open_one k x Σe)
    (lty_env_open_one k x Στ)
    (cty_open k x τ)
    (open_tm k (vfvar x) e).
Proof.
  unfold denot_ty_lvar_gas.
  rewrite formula_open_denot_ty_obligations.
  rewrite formula_open_denot_ty_body_lvar_gas.
  reflexivity.
Qed.

Lemma formula_fv_open_denot_ty_body_lvar_gas k x gas Σe Στ τ e :
  formula_fv (formula_open k x (denot_ty_body_lvar_gas gas Σe Στ τ e)) =
  formula_fv
    (denot_ty_body_lvar_gas gas
      (lty_env_open_one k x Σe)
      (lty_env_open_one k x Στ)
      (cty_open k x τ)
      (open_tm k (vfvar x) e)).
Proof.
  (* Pure syntax/fv normalization.  This should eventually be proved directly
     by the same induction as the store-equivalence lemma, avoiding the stronger
     formula equality for qualifier atoms. *)
Admitted.

Lemma formula_fv_open_denot_ty_lvar_gas k x gas Σe Στ τ e :
  formula_fv (formula_open k x (denot_ty_lvar_gas gas Σe Στ τ e)) =
  formula_fv
    (denot_ty_lvar_gas gas
      (lty_env_open_one k x Σe)
      (lty_env_open_one k x Στ)
      (cty_open k x τ)
      (open_tm k (vfvar x) e)).
Proof.
  (* Fv companion for the store-equivalence open normalization. *)
Admitted.

Lemma FExprContIn_lty_post_store_equiv
    (Σ : lty_env) e (P Q : FQ) :
  formula_fv P = formula_fv Q →
  (∀ ν, ν ∉ lty_env_atom_dom Σ →
    formula_fv (formula_open 0 ν P) = formula_fv (formula_open 0 ν Q)) →
  (∀ ν, ν ∉ lty_env_atom_dom Σ →
    formula_store_equiv (formula_open 0 ν P) (formula_open 0 ν Q)) →
  formula_store_equiv (FExprContIn Σ e P) (FExprContIn Σ e Q).
Proof.
  intros Hfv Hopen_fv Heq ρ m.
  unfold FExprContIn, res_models_with_store.
  cbn [formula_measure res_models_with_store_fuel formula_scoped_in_world
    formula_fv formula_open].
  split; intros [Hscope [L [HLdom Hforall]]]; split.
  - unfold formula_scoped_in_world in *.
    cbn [formula_fv] in *.
    rewrite <- Hfv. exact Hscope.
  - exists (L ∪ lty_env_atom_dom Σ). split.
    { intros z Hz. apply elem_of_union. left. exact (HLdom z Hz). }
    intros y Hy m' Hdom Hrestrict.
    rewrite not_elem_of_union in Hy.
    destruct Hy as [HyL HyΣ].
    specialize (Hforall y HyL m' Hdom Hrestrict).
    cbn [formula_open formula_measure res_models_with_store_fuel
      formula_scoped_in_world formula_fv] in *.
    destruct Hforall as [HscopeImp Himpl].
    split.
    + unfold formula_scoped_in_world in *.
      cbn [formula_fv] in *.
      rewrite <- Hopen_fv by exact HyΣ.
      exact HscopeImp.
    + intros n Hle HA.
      assert (HA_src : res_models_with_store_fuel
        (0 + formula_measure
          (FExprResultAtLvar (lvars_shift (into_lvars Σ))
            (tm_shift 0 e) (LVBound 0)) +
          formula_measure P)
        ρ n (formula_open 0 y
          (FExprResultAtLvar (lvars_shift (into_lvars Σ))
            (tm_shift 0 e) (LVBound 0)))).
      { models_fuel_irrel HA. }
      specialize (Himpl n Hle HA_src) as HP.
      pose proof (Heq y HyΣ ρ n) as HyEq.
      unfold res_models_with_store in HyEq.
      assert (HQ_exact :
        res_models_with_store_fuel (formula_measure (formula_open 0 y Q))
          ρ n (formula_open 0 y Q)).
      {
        apply (proj1 HyEq).
        eapply res_models_with_store_fuel_irrel; [| | exact HP];
          rewrite formula_open_preserves_measure; simpl; lia.
      }
      eapply res_models_with_store_fuel_irrel; [| | exact HQ_exact];
        rewrite formula_open_preserves_measure; simpl; lia.
  - unfold formula_scoped_in_world in *.
    cbn [formula_fv] in *.
    rewrite Hfv. exact Hscope.
  - exists (L ∪ lty_env_atom_dom Σ). split.
    { intros z Hz. apply elem_of_union. left. exact (HLdom z Hz). }
    intros y Hy m' Hdom Hrestrict.
    rewrite not_elem_of_union in Hy.
    destruct Hy as [HyL HyΣ].
    specialize (Hforall y HyL m' Hdom Hrestrict).
    cbn [formula_open formula_measure res_models_with_store_fuel
      formula_scoped_in_world formula_fv] in *.
    destruct Hforall as [HscopeImp Himpl].
    split.
    + unfold formula_scoped_in_world in *.
      cbn [formula_fv] in *.
      rewrite Hopen_fv by exact HyΣ.
      exact HscopeImp.
    + intros n Hle HA.
      assert (HA_src : res_models_with_store_fuel
        (0 + formula_measure
          (FExprResultAtLvar (lvars_shift (into_lvars Σ))
            (tm_shift 0 e) (LVBound 0)) +
          formula_measure Q)
        ρ n (formula_open 0 y
          (FExprResultAtLvar (lvars_shift (into_lvars Σ))
            (tm_shift 0 e) (LVBound 0)))).
      { models_fuel_irrel HA. }
      specialize (Himpl n Hle HA_src) as HQ.
      pose proof (Heq y HyΣ ρ n) as HyEq.
      unfold res_models_with_store in HyEq.
      assert (HP_exact :
        res_models_with_store_fuel (formula_measure (formula_open 0 y P))
          ρ n (formula_open 0 y P)).
      {
        apply (proj2 HyEq).
        eapply res_models_with_store_fuel_irrel; [| | exact HQ];
          rewrite formula_open_preserves_measure; simpl; lia.
      }
      eapply res_models_with_store_fuel_irrel; [| | exact HP_exact];
        rewrite formula_open_preserves_measure; simpl; lia.
Qed.

Lemma formula_store_equiv_open_refinement_post_over k x Στ b φ :
  formula_store_equiv
    (formula_open (S k) x
      (FAnd
        (FResultBasicWorld (lty_env_shift Στ) b (qual_vars φ))
        (FFibVars (qual_vars φ) (FOver (FTypeQualifier φ)))))
    (FAnd
      (FResultBasicWorld (lty_env_shift (lty_env_open_one k x Στ)) b
        (qual_vars (qual_open_atom (S k) x φ)))
      (FFibVars (qual_vars (qual_open_atom (S k) x φ))
        (FOver (FTypeQualifier (qual_open_atom (S k) x φ))))).
Proof.
  rewrite formula_open_and.
  rewrite formula_open_FResultBasicWorld_under_result.
  rewrite <- qual_vars_open_atom.
  eapply formula_store_equiv_and.
  - reflexivity.
  - apply formula_fv_open_FResultQualifier_over.
  - apply formula_store_equiv_refl.
  - apply formula_store_equiv_open_FResultQualifier_over.
Qed.

Lemma formula_fv_open_refinement_post_over k x Στ b φ :
  formula_fv
    (formula_open (S k) x
      (FAnd
        (FResultBasicWorld (lty_env_shift Στ) b (qual_vars φ))
        (FFibVars (qual_vars φ)
       (FOver (FTypeQualifier φ))))) =
  formula_fv
    (FAnd
      (FResultBasicWorld (lty_env_shift (lty_env_open_one k x Στ)) b
        (qual_vars (qual_open_atom (S k) x φ)))
      (FFibVars (qual_vars (qual_open_atom (S k) x φ))
        (FOver (FTypeQualifier (qual_open_atom (S k) x φ))))).
Proof.
  rewrite formula_open_and.
  rewrite formula_open_FResultBasicWorld_under_result.
  rewrite <- qual_vars_open_atom.
  cbn [formula_fv].
  rewrite formula_fv_open_FResultQualifier_over.
  reflexivity.
Qed.

Lemma formula_store_equiv_open_refinement_post_under k x Στ b φ :
  formula_store_equiv
    (formula_open (S k) x
      (FAnd
        (FResultBasicWorld (lty_env_shift Στ) b (qual_vars φ))
        (FFibVars (qual_vars φ) (FUnder (FTypeQualifier φ)))))
    (FAnd
      (FResultBasicWorld (lty_env_shift (lty_env_open_one k x Στ)) b
        (qual_vars (qual_open_atom (S k) x φ)))
      (FFibVars (qual_vars (qual_open_atom (S k) x φ))
        (FUnder (FTypeQualifier (qual_open_atom (S k) x φ))))).
Proof.
  rewrite formula_open_and.
  rewrite formula_open_FResultBasicWorld_under_result.
  rewrite <- qual_vars_open_atom.
  eapply formula_store_equiv_and.
  - reflexivity.
  - apply formula_fv_open_FResultQualifier_under.
  - apply formula_store_equiv_refl.
  - apply formula_store_equiv_open_FResultQualifier_under.
Qed.

Lemma formula_fv_open_refinement_post_under k x Στ b φ :
  formula_fv
    (formula_open (S k) x
      (FAnd
        (FResultBasicWorld (lty_env_shift Στ) b (qual_vars φ))
        (FFibVars (qual_vars φ)
       (FUnder (FTypeQualifier φ))))) =
  formula_fv
    (FAnd
      (FResultBasicWorld (lty_env_shift (lty_env_open_one k x Στ)) b
        (qual_vars (qual_open_atom (S k) x φ)))
      (FFibVars (qual_vars (qual_open_atom (S k) x φ))
        (FUnder (FTypeQualifier (qual_open_atom (S k) x φ))))).
Proof.
  rewrite formula_open_and.
  rewrite formula_open_FResultBasicWorld_under_result.
  rewrite <- qual_vars_open_atom.
  cbn [formula_fv].
  rewrite formula_fv_open_FResultQualifier_under.
  reflexivity.
Qed.

Lemma formula_fv_open_open_refinement_post_over k x y Στ b φ :
  formula_fv
    (formula_open 0 y
      (formula_open (S k) x
        (FAnd
          (FResultBasicWorld (lty_env_shift Στ) b (qual_vars φ))
          (FFibVars (qual_vars φ)
       (FOver (FTypeQualifier φ)))))) =
  formula_fv
    (formula_open 0 y
      (FAnd
        (FResultBasicWorld (lty_env_shift (lty_env_open_one k x Στ)) b
          (qual_vars (qual_open_atom (S k) x φ)))
        (FFibVars (qual_vars (qual_open_atom (S k) x φ))
          (FOver (FTypeQualifier (qual_open_atom (S k) x φ)))))).
Proof.
  (* Same syntax/fv normalization as [formula_fv_open_refinement_post_over],
     one result-binder open later. *)
Admitted.

Lemma formula_store_equiv_open_open_refinement_post_over k x y Στ b φ :
  formula_store_equiv
    (formula_open 0 y
      (formula_open (S k) x
        (FAnd
          (FResultBasicWorld (lty_env_shift Στ) b (qual_vars φ))
          (FFibVars (qual_vars φ)
       (FOver (FTypeQualifier φ))))))
    (formula_open 0 y
      (FAnd
        (FResultBasicWorld (lty_env_shift (lty_env_open_one k x Στ)) b
          (qual_vars (qual_open_atom (S k) x φ)))
        (FFibVars (qual_vars (qual_open_atom (S k) x φ))
          (FOver (FTypeQualifier (qual_open_atom (S k) x φ)))))).
Proof.
  (* Result-binder-open version of [formula_store_equiv_open_refinement_post_over]. *)
Admitted.

Lemma formula_fv_open_open_refinement_post_under k x y Στ b φ :
  formula_fv
    (formula_open 0 y
      (formula_open (S k) x
        (FAnd
          (FResultBasicWorld (lty_env_shift Στ) b (qual_vars φ))
          (FFibVars (qual_vars φ)
       (FUnder (FTypeQualifier φ)))))) =
  formula_fv
    (formula_open 0 y
      (FAnd
        (FResultBasicWorld (lty_env_shift (lty_env_open_one k x Στ)) b
          (qual_vars (qual_open_atom (S k) x φ)))
        (FFibVars (qual_vars (qual_open_atom (S k) x φ))
          (FUnder (FTypeQualifier (qual_open_atom (S k) x φ)))))).
Proof.
  (* Same syntax/fv normalization as [formula_fv_open_refinement_post_under],
     one result-binder open later. *)
Admitted.

Lemma formula_store_equiv_open_open_refinement_post_under k x y Στ b φ :
  formula_store_equiv
    (formula_open 0 y
      (formula_open (S k) x
        (FAnd
          (FResultBasicWorld (lty_env_shift Στ) b (qual_vars φ))
          (FFibVars (qual_vars φ)
       (FUnder (FTypeQualifier φ))))))
    (formula_open 0 y
      (FAnd
        (FResultBasicWorld (lty_env_shift (lty_env_open_one k x Στ)) b
          (qual_vars (qual_open_atom (S k) x φ)))
        (FFibVars (qual_vars (qual_open_atom (S k) x φ))
          (FUnder (FTypeQualifier (qual_open_atom (S k) x φ)))))).
Proof.
  (* Result-binder-open version of [formula_store_equiv_open_refinement_post_under]. *)
Admitted.

Lemma formula_store_equiv_open_denot_ty_obligations
    k x Σe Στ τ e φ ψ :
  formula_fv (formula_open k x φ) = formula_fv ψ →
  formula_store_equiv (formula_open k x φ) ψ →
  formula_store_equiv
    (formula_open k x (denot_ty_obligations Σe Στ τ e φ))
    (denot_ty_obligations
      (lty_env_open_one k x Σe)
      (lty_env_open_one k x Στ)
      (cty_open k x τ)
      (open_tm k (vfvar x) e)
      ψ).
Proof.
  intros Hfv Heq.
  rewrite formula_open_denot_ty_obligations.
  unfold denot_ty_obligations.
  eapply formula_store_equiv_and.
  - reflexivity.
  - cbn [formula_fv]. rewrite Hfv. reflexivity.
  - apply formula_store_equiv_refl.
  - eapply formula_store_equiv_and.
    + reflexivity.
    + cbn [formula_fv]. rewrite Hfv. reflexivity.
    + apply formula_store_equiv_refl.
    + eapply formula_store_equiv_and.
      * reflexivity.
      * exact Hfv.
      * apply formula_store_equiv_refl.
      * exact Heq.
Qed.

Lemma formula_fv_open_denot_ty_obligations
    k x Σe Στ τ e φ ψ :
  formula_fv (formula_open k x φ) = formula_fv ψ →
  formula_fv
    (formula_open k x (denot_ty_obligations Σe Στ τ e φ)) =
  formula_fv
    (denot_ty_obligations
      (lty_env_open_one k x Σe)
      (lty_env_open_one k x Στ)
      (cty_open k x τ)
      (open_tm k (vfvar x) e)
      ψ).
Proof.
  intros Hfv.
  rewrite formula_open_denot_ty_obligations.
  unfold denot_ty_obligations.
  cbn [formula_fv].
  rewrite Hfv.
  reflexivity.
Qed.

Lemma formula_store_equiv_open_denot_ty_body_lvar_gas_arrow_obligation
    k x gas Σe Στ τx τ e :
  formula_store_equiv
    (formula_open k x
      (FForall (
        let Σex := <[LVBound 0 := erase_ty τx]> (lty_env_shift Σe) in
        let Στr := lty_env_shift Στ in
        let Στx := <[LVBound 0 := erase_ty τx]> (lty_env_shift Στ) in
          FImpl
            (denot_ty_obligations Σex Στr τx (tret (vbvar 0))
              (denot_ty_body_lvar_gas gas Σex Στr τx (tret (vbvar 0))))
            (denot_ty_obligations Σex Στx τ (tapp_tm (tm_shift 0 e) (vbvar 0))
              (denot_ty_body_lvar_gas gas Σex Στx τ
                (tapp_tm (tm_shift 0 e) (vbvar 0)))))))
    (FForall (
      let Σex :=
        <[LVBound 0 := erase_ty (cty_open k x τx)]>
          (lty_env_shift (lty_env_open_one k x Σe)) in
      let Στx :=
        <[LVBound 0 := erase_ty (cty_open k x τx)]>
          (lty_env_shift (lty_env_open_one k x Στ)) in
        FImpl
          (denot_ty_obligations Σex (lty_env_shift (lty_env_open_one k x Στ))
            (cty_open k x τx) (tret (vbvar 0))
            (denot_ty_body_lvar_gas gas Σex (lty_env_shift (lty_env_open_one k x Στ))
              (cty_open k x τx) (tret (vbvar 0))))
          (denot_ty_obligations Σex Στx (cty_open (S k) x τ)
            (tapp_tm (tm_shift 0 (open_tm k (vfvar x) e)) (vbvar 0))
            (denot_ty_body_lvar_gas gas Σex Στx (cty_open (S k) x τ)
              (tapp_tm (tm_shift 0 (open_tm k (vfvar x) e)) (vbvar 0)))))).
Proof.
  (* Binder-level argument/consequent transport for arrow denotations.  This is
     the remaining normalization point after over/under/inter/union/sum are
     handled structurally. *)
Admitted.

Lemma formula_store_equiv_open_denot_ty_body_lvar_gas_wand_obligation
    k x gas Σe Στ τx τ e :
  formula_store_equiv
    (formula_open k x
      (FForall (
        let Σex := <[LVBound 0 := erase_ty τx]> (lty_env_shift Σe) in
        let Στr := lty_env_shift Στ in
        let Στx := <[LVBound 0 := erase_ty τx]> (lty_env_shift Στ) in
          FWand
            (denot_ty_obligations Σex Στr τx (tret (vbvar 0))
              (denot_ty_body_lvar_gas gas Σex Στr τx (tret (vbvar 0))))
            (denot_ty_obligations Σex Στx τ (tapp_tm (tm_shift 0 e) (vbvar 0))
              (denot_ty_body_lvar_gas gas Σex Στx τ
                (tapp_tm (tm_shift 0 e) (vbvar 0)))))))
    (FForall (
      let Σex :=
        <[LVBound 0 := erase_ty (cty_open k x τx)]>
          (lty_env_shift (lty_env_open_one k x Σe)) in
      let Στx :=
        <[LVBound 0 := erase_ty (cty_open k x τx)]>
          (lty_env_shift (lty_env_open_one k x Στ)) in
        FWand
          (denot_ty_obligations Σex (lty_env_shift (lty_env_open_one k x Στ))
            (cty_open k x τx) (tret (vbvar 0))
            (denot_ty_body_lvar_gas gas Σex (lty_env_shift (lty_env_open_one k x Στ))
              (cty_open k x τx) (tret (vbvar 0))))
          (denot_ty_obligations Σex Στx (cty_open (S k) x τ)
            (tapp_tm (tm_shift 0 (open_tm k (vfvar x) e)) (vbvar 0))
            (denot_ty_body_lvar_gas gas Σex Στx (cty_open (S k) x τ)
              (tapp_tm (tm_shift 0 (open_tm k (vfvar x) e)) (vbvar 0)))))).
Proof.
  (* Same binder-level transport as arrow, with the connective changed to wand. *)
Admitted.

Lemma formula_store_equiv_open_denot_ty_body_lvar_gas
    k x gas Σe Στ τ e :
  formula_store_equiv
    (formula_open k x (denot_ty_body_lvar_gas gas Σe Στ τ e))
    (denot_ty_body_lvar_gas gas
      (lty_env_open_one k x Σe)
      (lty_env_open_one k x Στ)
      (cty_open k x τ)
      (open_tm k (vfvar x) e)).
Proof.
  revert k x Σe Στ τ e.
  induction gas as [|gas IH]; intros k x Σe Στ τ e.
  - apply formula_store_equiv_refl.
  - destruct τ as [b φ|b φ|τ1 τ2|τ1 τ2|τ1 τ2|τx τ|τx τ];
      cbn [denot_ty_body_lvar_gas cty_open].
    + rewrite formula_open_FExprContIn_lty.
      eapply FExprContIn_lty_post_store_equiv.
      * apply formula_fv_open_refinement_post_over.
      * intros ν _. apply formula_fv_open_open_refinement_post_over.
      * intros ν _. apply formula_store_equiv_open_open_refinement_post_over.
    + rewrite formula_open_FExprContIn_lty.
      eapply FExprContIn_lty_post_store_equiv.
      * apply formula_fv_open_refinement_post_under.
      * intros ν _. apply formula_fv_open_open_refinement_post_under.
      * intros ν _. apply formula_store_equiv_open_open_refinement_post_under.
    + rewrite formula_open_and.
      eapply formula_store_equiv_and.
      * eapply formula_fv_open_denot_ty_obligations.
        apply formula_fv_open_denot_ty_body_lvar_gas.
      * eapply formula_fv_open_denot_ty_obligations.
        apply formula_fv_open_denot_ty_body_lvar_gas.
      * eapply formula_store_equiv_open_denot_ty_obligations.
        -- apply formula_fv_open_denot_ty_body_lvar_gas.
        -- apply IH.
      * eapply formula_store_equiv_open_denot_ty_obligations.
        -- apply formula_fv_open_denot_ty_body_lvar_gas.
        -- apply IH.
    + rewrite formula_open_or.
      eapply formula_store_equiv_or.
      * eapply formula_fv_open_denot_ty_obligations.
        apply formula_fv_open_denot_ty_body_lvar_gas.
      * eapply formula_fv_open_denot_ty_obligations.
        apply formula_fv_open_denot_ty_body_lvar_gas.
      * eapply formula_store_equiv_open_denot_ty_obligations.
        -- apply formula_fv_open_denot_ty_body_lvar_gas.
        -- apply IH.
      * eapply formula_store_equiv_open_denot_ty_obligations.
        -- apply formula_fv_open_denot_ty_body_lvar_gas.
        -- apply IH.
    + rewrite formula_open_plus.
      eapply formula_store_equiv_plus.
      * eapply formula_fv_open_denot_ty_obligations.
        apply formula_fv_open_denot_ty_body_lvar_gas.
      * eapply formula_fv_open_denot_ty_obligations.
        apply formula_fv_open_denot_ty_body_lvar_gas.
      * eapply formula_store_equiv_open_denot_ty_obligations.
        -- apply formula_fv_open_denot_ty_body_lvar_gas.
        -- apply IH.
      * eapply formula_store_equiv_open_denot_ty_obligations.
        -- apply formula_fv_open_denot_ty_body_lvar_gas.
        -- apply IH.
    + (* CTArrow: the remaining proof is the binder-level argument/consequent
         transport for the denotation body. *)
      apply formula_store_equiv_open_denot_ty_body_lvar_gas_arrow_obligation.
    + (* CTWand: same binder-level transport shape as arrow, with wand. *)
      apply formula_store_equiv_open_denot_ty_body_lvar_gas_wand_obligation.
Qed.

Lemma formula_store_equiv_open_denot_ty_lvar_gas
    k x gas Σe Στ τ e :
  formula_store_equiv
    (formula_open k x (denot_ty_lvar_gas gas Σe Στ τ e))
    (denot_ty_lvar_gas gas
      (lty_env_open_one k x Σe)
      (lty_env_open_one k x Στ)
      (cty_open k x τ)
      (open_tm k (vfvar x) e)).
Proof.
  unfold denot_ty_lvar_gas.
  eapply formula_store_equiv_open_denot_ty_obligations.
  - apply formula_fv_open_denot_ty_body_lvar_gas.
  - apply formula_store_equiv_open_denot_ty_body_lvar_gas.
Qed.

Lemma formula_open_denot_ty_body_lvar k x Σe Στ τ e :
  formula_open k x (denot_ty_body_lvar Σe Στ τ e) =
  denot_ty_body_lvar
    (lty_env_open_one k x Σe)
    (lty_env_open_one k x Στ)
    (cty_open k x τ)
    (open_tm k (vfvar x) e).
Proof.
  unfold denot_ty_body_lvar.
  rewrite formula_open_denot_ty_body_lvar_gas.
  rewrite cty_open_preserves_depth.
  reflexivity.
Qed.

Lemma formula_open_denot_ty_lvar k x Σe Στ τ e :
  formula_open k x (denot_ty_lvar Σe Στ τ e) =
  denot_ty_lvar
    (lty_env_open_one k x Σe)
    (lty_env_open_one k x Στ)
    (cty_open k x τ)
    (open_tm k (vfvar x) e).
Proof.
  unfold denot_ty_lvar.
  rewrite formula_open_denot_ty_lvar_gas.
  rewrite cty_open_preserves_depth.
  reflexivity.
Qed.

Lemma denot_ty_body_lvar_over Σe Στ b φ e :
  denot_ty_body_lvar Σe Στ (CTOver b φ) e =
  FExprContIn Σe e
    (FAnd
      (FResultBasicWorld (lty_env_shift Στ) b (qual_vars φ))
      (FFibVars (qual_vars φ) (FOver (FTypeQualifier φ)))).
Proof.
  unfold denot_ty_body_lvar.
  cbn [cty_depth denot_ty_body_lvar_gas].
  reflexivity.
Qed.

Lemma denot_ty_body_lvar_under Σe Στ b φ e :
  denot_ty_body_lvar Σe Στ (CTUnder b φ) e =
  FExprContIn Σe e
    (FAnd
      (FResultBasicWorld (lty_env_shift Στ) b (qual_vars φ))
      (FFibVars (qual_vars φ) (FUnder (FTypeQualifier φ)))).
Proof.
  unfold denot_ty_body_lvar.
  cbn [cty_depth denot_ty_body_lvar_gas].
  reflexivity.
Qed.

Lemma denot_ty_body_lvar_inter Σe Στ τ1 τ2 e :
  denot_ty_body_lvar Σe Στ (CTInter τ1 τ2) e =
  FAnd (denot_ty_lvar Σe Στ τ1 e) (denot_ty_lvar Σe Στ τ2 e).
Proof.
  unfold denot_ty_body_lvar.
  cbn [cty_depth denot_ty_body_lvar_gas].
  rewrite !denot_ty_obligations_body_gas_saturate by lia.
  reflexivity.
Qed.

Lemma denot_ty_body_lvar_union Σe Στ τ1 τ2 e :
  denot_ty_body_lvar Σe Στ (CTUnion τ1 τ2) e =
  FOr (denot_ty_lvar Σe Στ τ1 e) (denot_ty_lvar Σe Στ τ2 e).
Proof.
  unfold denot_ty_body_lvar.
  cbn [cty_depth denot_ty_body_lvar_gas].
  rewrite !denot_ty_obligations_body_gas_saturate by lia.
  reflexivity.
Qed.

Lemma denot_ty_body_lvar_sum Σe Στ τ1 τ2 e :
  denot_ty_body_lvar Σe Στ (CTSum τ1 τ2) e =
  FPlus (denot_ty_lvar Σe Στ τ1 e) (denot_ty_lvar Σe Στ τ2 e).
Proof.
  unfold denot_ty_body_lvar.
  cbn [cty_depth denot_ty_body_lvar_gas].
  rewrite !denot_ty_obligations_body_gas_saturate by lia.
  reflexivity.
Qed.

Lemma denot_ty_body_lvar_arrow Σe Στ τx τ e :
  denot_ty_body_lvar Σe Στ (CTArrow τx τ) e =
  FForall (
    let Σex := <[LVBound 0 := erase_ty τx]> (lty_env_shift Σe) in
    let Στx := <[LVBound 0 := erase_ty τx]> (lty_env_shift Στ) in
    FImpl
      (denot_ty_lvar Σex (lty_env_shift Στ) τx (tret (vbvar 0)))
      (denot_ty_lvar Σex Στx τ (tapp_tm (tm_shift 0 e) (vbvar 0)))).
Proof.
  unfold denot_ty_body_lvar.
  cbn [cty_depth denot_ty_body_lvar_gas].
  rewrite !denot_ty_obligations_body_gas_saturate by lia.
  reflexivity.
Qed.

Lemma denot_ty_body_lvar_wand Σe Στ τx τ e :
  denot_ty_body_lvar Σe Στ (CTWand τx τ) e =
  FForall (
    let Σex := <[LVBound 0 := erase_ty τx]> (lty_env_shift Σe) in
    let Στx := <[LVBound 0 := erase_ty τx]> (lty_env_shift Στ) in
    FWand
      (denot_ty_lvar Σex (lty_env_shift Στ) τx (tret (vbvar 0)))
      (denot_ty_lvar Σex Στx τ (tapp_tm (tm_shift 0 e) (vbvar 0)))).
Proof.
  unfold denot_ty_body_lvar.
  cbn [cty_depth denot_ty_body_lvar_gas].
  rewrite !denot_ty_obligations_body_gas_saturate by lia.
  reflexivity.
Qed.

Definition denot_ty_body
    (Σ : gmap atom ty) (τ : choice_ty) (e : tm) : FQ :=
  let Σl := atom_env_to_lty_env Σ in
  denot_ty_body_lvar Σl Σl τ e.

Definition denot_ty_on
    (Σ : gmap atom ty) (τ : choice_ty) (e : tm) : FQ :=
  let Σl := atom_env_to_lty_env Σ in
  denot_ty_lvar Σl Σl τ e.

Lemma denot_ty_body_nf Σ τ e :
  denot_ty_body_lvar (atom_env_to_lty_env Σ) (atom_env_to_lty_env Σ) τ e =
  denot_ty_body Σ τ e.
Proof. reflexivity. Qed.

Lemma denot_ty_on_nf Σ τ e :
  denot_ty_lvar (atom_env_to_lty_env Σ) (atom_env_to_lty_env Σ) τ e =
  denot_ty_on Σ τ e.
Proof. reflexivity. Qed.

#[global] Hint Rewrite denot_ty_body_nf denot_ty_on_nf : denot_nf.

Ltac denot_ty_nf :=
  autorewrite with denot_nf.

Ltac denot_ty_nf_in H :=
  autorewrite with denot_nf in H.

Definition denot_ty_under (Σ : gmap atom ty) (τ : choice_ty) (e : tm) : FQ :=
  denot_ty_on Σ τ e.

Definition denot_ty (τ : choice_ty) (e : tm) : FQ :=
  denot_ty_under ∅ τ e.

Definition denot_ty_in_ctx (Γ : ctx) (τ : choice_ty) (e : tm) : FQ :=
  denot_ty_under (erase_ctx Γ) τ e.

Notation "'erase_ctx_under' Σ Γ" := (Σ ∪ erase_ctx Γ)
  (at level 10, Σ at level 9, Γ at level 9, only parsing).

Definition denot_ty_in_ctx_under
    (Σ : gmap atom ty) (Γ : ctx) (τ : choice_ty) (e : tm) : FQ :=
  denot_ty_on (erase_ctx_under Σ Γ) τ e.

Lemma denot_ty_intro Σ τ e m :
  basic_choice_ty (dom Σ) τ →
  Σ ⊢ₑ e ⋮ erase_ty τ →
  world_closed_on (dom Σ) m →
  expr_total_on e m →
  m ⊨ denot_ty_body Σ τ e →
  dom Σ ⊆ world_dom (m : World) →
  m ⊨ denot_ty_on Σ τ e.
Proof.
  intros Hbasic Htyped Hclosed Htotal Hbody Hdom.
  unfold denot_ty_on, denot_ty_body.
  unfold denot_ty_obligations.
  apply res_models_and_intro_from_models.
  - unfold FBasicTypingIn, res_models.
    eapply res_models_with_store_store_resource_atom_vars_intro.
    + unfold formula_scoped_in_world.
      rewrite formula_fv_FStoreResourceAtom_lvars.
      rewrite !atom_env_to_lty_env_dom.
      rewrite lvars_fv_union, !lvars_fv_of_atoms.
      rewrite dom_empty_L. set_solver.
    + rewrite !lty_env_open_lvars_atom_env. cbn [open_cty_env open_tm_env].
      split.
      * apply basic_choice_ty_to_lvar_atom_env. exact Hbasic.
      * apply tm_has_type_to_lty_atom_env. exact Htyped.
  - apply res_models_and_intro_from_models.
    + unfold FClosedResourceIn, res_models.
      eapply res_models_with_store_store_resource_atom_vars_intro.
      * unfold formula_scoped_in_world.
        rewrite formula_fv_FStoreResourceAtom_lvars.
        rewrite atom_env_to_lty_env_dom, lvars_fv_of_atoms.
        rewrite dom_empty_L. set_solver.
      * rewrite lty_env_open_atom_env.
        rewrite atom_env_to_lty_env_dom, lvars_fv_of_atoms.
        eapply world_closed_on_le.
        -- apply res_restrict_le.
        -- exact Hclosed.
    + apply res_models_and_intro_from_models.
      * unfold FStrongTotalIn, res_models.
        eapply res_models_with_store_store_resource_atom_vars_intro.
        -- unfold formula_scoped_in_world.
           rewrite formula_fv_FStoreResourceAtom_lvars.
           rewrite atom_env_to_lty_env_dom, lvars_fv_of_atoms.
           rewrite dom_empty_L. set_solver.
        -- rewrite lty_env_open_atom_env.
           rewrite atom_env_to_lty_env_dom, lvars_fv_of_atoms.
           rewrite store_restrict_empty. cbn [open_tm_env].
           eapply expr_total_with_store_empty_restrict; eauto.
           eapply basic_typing_contains_fv_tm. exact Htyped.
      * exact Hbody.
Qed.

Lemma denot_ty_body_of_formula Σ τ e m :
  m ⊨ denot_ty_on Σ τ e →
  m ⊨ denot_ty_body Σ τ e.
Proof.
  intros Hm.
  unfold denot_ty_on, denot_ty_body in Hm.
  unfold denot_ty_obligations in Hm.
  apply res_models_with_store_and_elim_r in Hm.
  apply res_models_with_store_and_elim_r in Hm.
  apply res_models_with_store_and_elim_r in Hm.
  exact Hm.
Qed.

Lemma denot_ty_basic_of_formula Σ τ e m :
  m ⊨ denot_ty_on Σ τ e →
  basic_choice_ty (dom Σ) τ ∧ Σ ⊢ₑ e ⋮ erase_ty τ.
Proof.
  (* Regularity projection from the new lvar-aware basic atom back to the old
     closed atom judgments. *)
Admitted.

Lemma world_closed_on_extend X (m n : WfWorld) :
  X ⊆ world_dom (m : World) →
  m ⊑ n →
  world_closed_on X m →
  world_closed_on X n.
Proof.
  intros HXm Hle Hclosed σ Hσ.
  pose proof (res_restrict_eq_of_le m n Hle) as Hrestrict.
  assert ((res_restrict n (world_dom (m : World)) : World)
    (store_restrict σ (world_dom (m : World)))) as Hσm.
  { exists σ. split; [exact Hσ | reflexivity]. }
  rewrite Hrestrict in Hσm.
  replace (store_restrict σ X) with
    (store_restrict (store_restrict σ (world_dom (m : World))) X).
  - exact (Hclosed _ Hσm).
  - store_norm. reflexivity.
Qed.

Lemma denot_ty_world_closed_on_of_formula Σ τ e m :
  m ⊨ denot_ty_on Σ τ e →
  world_closed_on (dom Σ) m.
Proof.
  intros Hm.
  unfold denot_ty_on in Hm.
  unfold denot_ty_obligations, FClosedResourceIn in Hm.
  apply res_models_with_store_and_elim_r in Hm.
  apply res_models_with_store_and_elim_l in Hm.
  destruct (res_models_with_store_store_resource_atom_vars_elim ∅ m
    (dom (atom_env_to_lty_env Σ))
    (fun η _ m =>
      world_closed_on (dom (lty_env_open η (atom_env_to_lty_env Σ))) m) Hm)
    as [m0 [Hscope [Hclosed Hle]]].
  rewrite lty_env_open_atom_env in Hclosed.
  rewrite atom_env_to_lty_env_dom, lvars_fv_of_atoms in Hclosed.
  eapply (world_closed_on_extend (dom Σ)
    (res_restrict m0 (dom Σ)) m).
  - simpl. intros z Hz. apply elem_of_intersection. split; [| exact Hz].
    unfold formula_scoped_in_world in Hscope.
    rewrite dom_empty_L in Hscope.
    apply Hscope. apply elem_of_union. right.
    rewrite formula_fv_FStoreResourceAtom_lvars.
    rewrite atom_env_to_lty_env_dom, lvars_fv_of_atoms. exact Hz.
  - etrans; [apply res_restrict_le | exact Hle].
  - exact Hclosed.
Qed.

Lemma denot_ty_expr_total_on_of_formula Σ τ e m :
  m ⊨ denot_ty_on Σ τ e →
  expr_total_on e m.
Proof.
  intros Hm.
  pose proof (denot_ty_basic_of_formula _ _ _ _ Hm)
    as [_ Htyped].
  split.
  - pose proof (res_models_with_store_fuel_scoped _ ∅ m
      (denot_ty_on Σ τ e) Hm) as Hscope.
    pose proof (basic_typing_contains_fv_tm _ _ _ Htyped) as Hfv.
    intros z Hz.
    apply Hscope.
    rewrite dom_empty_L.
    unfold denot_ty_on, denot_ty_lvar, denot_ty_lvar_gas.
    unfold denot_ty_obligations, FBasicTypingIn, FClosedResourceIn,
      FStrongTotalIn, FStoreResourceAtom, FResourceAtom.
    cbn [formula_fv stale stale_logic_qualifier lqual_dom].
    denot_lvars_norm.
    rewrite !atom_env_to_lty_env_dom.
    rewrite !lvars_fv_union, !lvars_fv_of_atoms.
    set_solver.
  - unfold denot_ty_on in Hm.
    unfold denot_ty_obligations, FStrongTotalIn in Hm.
    apply res_models_with_store_and_elim_r in Hm.
    apply res_models_with_store_and_elim_r in Hm.
    apply res_models_with_store_and_elim_l in Hm.
    destruct (res_models_with_store_store_resource_atom_vars_elim ∅ m
      (dom (atom_env_to_lty_env Σ))
      (fun η ρ m =>
        let Γ := lty_env_open η (atom_env_to_lty_env Σ) in
        expr_total_with_store (dom Γ) (open_tm_env η e) ρ m) Hm)
      as [m0 [Hscope [Htotal Hle]]].
    rewrite lty_env_open_atom_env in Htotal.
    rewrite atom_env_to_lty_env_dom, lvars_fv_of_atoms in Htotal.
    rewrite store_restrict_empty in Htotal.
    cbn [open_tm_env] in Htotal.
    destruct Htotal as [Hclosed_total Htotal].
    intros σ Hσ.
    pose proof (res_restrict_eq_of_le m0 m Hle) as Hrestrict.
    assert (Hσm0 :
      (m0 : World) (store_restrict σ (world_dom (m0 : World)))).
    { assert ((res_restrict m (world_dom (m0 : World)) : World)
        (store_restrict σ (world_dom (m0 : World)))) as Hraw.
      { exists σ. split; [exact Hσ | reflexivity]. }
      rewrite Hrestrict in Hraw. exact Hraw. }
    assert (HdomΣ : dom Σ ⊆ world_dom (m0 : World)).
    { unfold formula_scoped_in_world in Hscope.
      rewrite dom_empty_L in Hscope.
      intros z Hz. apply Hscope. apply elem_of_union. right.
      rewrite formula_fv_FStoreResourceAtom_lvars.
      rewrite atom_env_to_lty_env_dom, lvars_fv_of_atoms. exact Hz. }
    assert (HσD :
      (res_restrict m0 (dom Σ) : World) (store_restrict σ (dom Σ))).
    { exists (store_restrict σ (world_dom (m0 : World))).
      split; [exact Hσm0 |].
      rewrite store_restrict_twice_subset by set_solver.
      reflexivity. }
    specialize (Htotal _ HσD) as [vx Hsteps].
    exists vx.
    rewrite map_empty_union in Hsteps.
    rewrite store_restrict_twice_same in Hsteps.
    pose proof (basic_typing_contains_fv_tm _ _ _ Htyped) as HfvΣ.
    rewrite (subst_map_restrict_to_fv_from_superset e
      (dom Σ) σ HfvΣ).
    + exact Hsteps.
    + specialize (Hclosed_total _ HσD).
      rewrite map_empty_union in Hclosed_total.
      rewrite store_restrict_twice_same in Hclosed_total.
      exact (proj1 Hclosed_total).
Qed.

Definition denot_ty_total_in_ctx_under
    (Σ : gmap atom ty) (Γ : ctx) (τ : choice_ty) (e : tm)
    (m : WfWorld) : Prop :=
  m ⊨ denot_ty_in_ctx_under Σ Γ τ e ∧
  expr_total_on e m.

Definition entails_total (φ : FQ) (P : WfWorld → Prop) : Prop :=
  ∀ m, m ⊨ φ → P m.

Definition ty_env_agree_on (X : aset) (Σ1 Σ2 : gmap atom ty) : Prop :=
  ∀ x, x ∈ X → Σ1 !! x = Σ2 !! x.

Lemma ty_env_agree_on_insert_same X Σ1 Σ2 x T :
  ty_env_agree_on (X ∖ {[x]}) Σ1 Σ2 →
  ty_env_agree_on X (<[x := T]> Σ1) (<[x := T]> Σ2).
Proof.
  intros Hagree z Hz.
  destruct (decide (z = x)) as [->|Hne].
  - rewrite !(lookup_insert_eq _ x T). reflexivity.
  - rewrite !lookup_insert_ne by congruence.
    apply Hagree. set_solver.
Qed.

Lemma ty_env_agree_on_insert_same_keep X Σ1 Σ2 x T :
  ty_env_agree_on X Σ1 Σ2 →
  ty_env_agree_on (X ∪ {[x]}) (<[x := T]> Σ1) (<[x := T]> Σ2).
Proof.
  intros Hagree.
  apply ty_env_agree_on_insert_same.
  intros z Hz. apply Hagree. set_solver.
Qed.

Lemma ty_env_agree_on_open_qual_result D Σ1 Σ2 b φ ν :
  ty_env_agree_on (D ∪ qual_dom φ) Σ1 Σ2 →
  ty_env_agree_on ({[ν]} ∪ qual_dom (qual_open_atom 0 ν φ))
    (<[ν := TBase b]> Σ1) (<[ν := TBase b]> Σ2).
Proof.
  intros Hagree z Hz.
  destruct (decide (z = ν)) as [->|Hne].
  - rewrite !(lookup_insert_eq _ ν (TBase b)). reflexivity.
  - rewrite !lookup_insert_ne by congruence.
    apply Hagree.
    pose proof (qual_open_atom_dom_subset 0 ν φ z) as Hdom.
    set_solver.
Qed.

Lemma denot_ty_on_env_agree Σ1 Σ2 τ e :
  dom Σ1 = dom Σ2 →
  ty_env_agree_on (fv_cty τ ∪ fv_tm e) Σ1 Σ2 →
  denot_ty_on Σ1 τ e = denot_ty_on Σ2 τ e.
Proof.
Admitted.

Lemma FExprContIn_fv_lty_env
    (Σ : lty_env) e (Q : FQ) :
  formula_fv (FExprContIn Σ e Q) ⊆ lty_env_atom_dom Σ ∪ formula_fv Q.
Proof.
  unfold FExprContIn.
  cbn [formula_fv].
  denot_lvars_norm.
  rewrite FExprResultAtLvar_fv.
  cbn [into_lvars into_lvars_lvset].
  denot_lvars_norm.
  rewrite lvars_fv_union, lvars_fv_singleton_bound.
  fold (lvars_shift (dom Σ)).
  rewrite lvars_fv_shift.
  unfold lty_env_atom_dom.
  set_solver.
Qed.

(** ** Denotation scoping regularity

    These syntactic facts isolate the variable-accounting needed by semantic
    subtyping reflexivity.  They are intentionally stated at the denotation
    layer: typing proofs should consume these regularity lemmas rather than
    unfolding the formula generated for each type constructor. *)

Lemma denot_ty_obligations_fv_subset (Σe Στ : lty_env) τ e φ S :
  lty_env_atom_dom Σe ∪ lty_env_atom_dom Στ ∪ formula_fv φ ⊆ S →
  formula_fv (denot_ty_obligations Σe Στ τ e φ) ⊆ S.
Proof.
  intros Hsub.
  unfold denot_ty_obligations.
  unfold FBasicTypingIn, FClosedResourceIn, FStrongTotalIn,
    FStoreResourceAtom, FResourceAtom.
  cbn [formula_fv stale stale_logic_qualifier lqual_dom].
  denot_lvars_norm.
  rewrite lvars_fv_union.
  unfold lty_env_atom_dom.
  set_solver.
Qed.

Lemma denot_ty_obligations_body_gas_fv_subset gas Σe Στ τ e :
  formula_fv (denot_ty_body_lvar_gas gas Σe Στ τ e) ⊆
    lty_env_atom_dom Σe ∪ lty_env_atom_dom Στ ∪ fv_cty τ →
  formula_fv (denot_ty_obligations Σe Στ τ e
    (denot_ty_body_lvar_gas gas Σe Στ τ e)) ⊆
    lty_env_atom_dom Σe ∪ lty_env_atom_dom Στ ∪ fv_cty τ.
Proof.
  intros Hbody.
  apply denot_ty_obligations_fv_subset.
  set_solver.
Qed.

Lemma denot_ty_gas_fv_subset gas :
  (∀ Σe Στ τ e,
    formula_fv (denot_ty_body_lvar_gas gas Σe Στ τ e) ⊆
      lty_env_atom_dom Σe ∪ lty_env_atom_dom Στ ∪ fv_cty τ) ∧
  (∀ Σe Στ τ e,
    formula_fv (denot_ty_lvar_gas gas Σe Στ τ e) ⊆
      lty_env_atom_dom Σe ∪ lty_env_atom_dom Στ ∪ fv_cty τ).
Proof.
  induction gas as [|gas [IHbody IHlvar]].
  - split; intros Σe Στ τ e.
    + cbn [denot_ty_body_lvar_gas formula_fv]. set_solver.
    + unfold denot_ty_lvar_gas.
      apply denot_ty_obligations_fv_subset.
      cbn [denot_ty_body_lvar_gas formula_fv]. set_solver.
  - assert (HbodyS : ∀ Σe Στ τ e,
      formula_fv (denot_ty_body_lvar_gas (S gas) Σe Στ τ e) ⊆
        lty_env_atom_dom Σe ∪ lty_env_atom_dom Στ ∪ fv_cty τ).
	    {
	      intros Σe Στ τ e.
	      destruct τ as [b φ|b φ|τ1 τ2|τ1 τ2|τ1 τ2|τx τ|τx τ];
	        cbn [denot_ty_body_lvar_gas fv_cty].
	      - destruct φ as [D p]. cbn [qual_vars qual_dom].
	        pose proof (FExprContIn_fv_lty_env Σe e
	          (FAnd (FResultBasicWorld (lty_env_shift Στ) b (qual_vars (qual D p)))
	            (FFibVars (qual_vars (qual D p))
	              (FOver (FTypeQualifier (qual D p)))))) as Hcont.
	        cbn [qual_vars qual_dom formula_fv] in Hcont.
	        rewrite FResultBasicWorld_fv in Hcont.
	        unfold lty_env_bvar_scope in Hcont.
	        rewrite !lvars_fv_union, lvars_fv_of_bvars,
	          lvars_fv_singleton_bound in Hcont.
	        rewrite formula_fv_FTypeQualifier in Hcont.
	        cbn [qual_dom] in Hcont.
	        etransitivity; [exact Hcont | set_solver].
	      - destruct φ as [D p]. cbn [qual_vars qual_dom].
	        pose proof (FExprContIn_fv_lty_env Σe e
	          (FAnd (FResultBasicWorld (lty_env_shift Στ) b (qual_vars (qual D p)))
	            (FFibVars (qual_vars (qual D p))
	              (FUnder (FTypeQualifier (qual D p)))))) as Hcont.
	        cbn [qual_vars qual_dom formula_fv] in Hcont.
	        rewrite FResultBasicWorld_fv in Hcont.
	        unfold lty_env_bvar_scope in Hcont.
	        rewrite !lvars_fv_union, lvars_fv_of_bvars,
	          lvars_fv_singleton_bound in Hcont.
	        rewrite formula_fv_FTypeQualifier in Hcont.
        cbn [qual_dom] in Hcont.
        etransitivity; [exact Hcont | set_solver].
      - assert (H1 : formula_fv (denot_ty_obligations Σe Στ τ1 e
            (denot_ty_body_lvar_gas gas Σe Στ τ1 e)) ⊆
          lty_env_atom_dom Σe ∪ lty_env_atom_dom Στ ∪ fv_cty τ1)
          by (apply denot_ty_obligations_body_gas_fv_subset; apply IHbody).
        assert (H2 : formula_fv (denot_ty_obligations Σe Στ τ2 e
            (denot_ty_body_lvar_gas gas Σe Στ τ2 e)) ⊆
          lty_env_atom_dom Σe ∪ lty_env_atom_dom Στ ∪ fv_cty τ2)
          by (apply denot_ty_obligations_body_gas_fv_subset; apply IHbody).
        intros z Hz.
        cbn [formula_fv] in Hz.
        rewrite elem_of_union in Hz.
        destruct Hz as [Hz|Hz]; [apply H1 in Hz | apply H2 in Hz];
          set_solver.
      - assert (H1 : formula_fv (denot_ty_obligations Σe Στ τ1 e
            (denot_ty_body_lvar_gas gas Σe Στ τ1 e)) ⊆
          lty_env_atom_dom Σe ∪ lty_env_atom_dom Στ ∪ fv_cty τ1)
          by (apply denot_ty_obligations_body_gas_fv_subset; apply IHbody).
        assert (H2 : formula_fv (denot_ty_obligations Σe Στ τ2 e
            (denot_ty_body_lvar_gas gas Σe Στ τ2 e)) ⊆
          lty_env_atom_dom Σe ∪ lty_env_atom_dom Στ ∪ fv_cty τ2)
          by (apply denot_ty_obligations_body_gas_fv_subset; apply IHbody).
        intros z Hz.
        cbn [formula_fv] in Hz.
        rewrite elem_of_union in Hz.
        destruct Hz as [Hz|Hz]; [apply H1 in Hz | apply H2 in Hz];
          set_solver.
      - assert (H1 : formula_fv (denot_ty_obligations Σe Στ τ1 e
            (denot_ty_body_lvar_gas gas Σe Στ τ1 e)) ⊆
          lty_env_atom_dom Σe ∪ lty_env_atom_dom Στ ∪ fv_cty τ1)
          by (apply denot_ty_obligations_body_gas_fv_subset; apply IHbody).
        assert (H2 : formula_fv (denot_ty_obligations Σe Στ τ2 e
            (denot_ty_body_lvar_gas gas Σe Στ τ2 e)) ⊆
          lty_env_atom_dom Σe ∪ lty_env_atom_dom Στ ∪ fv_cty τ2)
          by (apply denot_ty_obligations_body_gas_fv_subset; apply IHbody).
        intros z Hz.
        cbn [formula_fv] in Hz.
        rewrite elem_of_union in Hz.
        destruct Hz as [Hz|Hz]; [apply H1 in Hz | apply H2 in Hz];
          set_solver.
      - set (Σex := <[LVBound 0:=erase_ty τx]>(lty_env_shift Σe)).
        set (Στx := <[LVBound 0:=erase_ty τx]>(lty_env_shift Στ)).
        assert (Hx : formula_fv (denot_ty_obligations Σex (lty_env_shift Στ) τx
              (tret (vbvar 0))
              (denot_ty_body_lvar_gas gas Σex (lty_env_shift Στ) τx
                (tret (vbvar 0)))) ⊆
            lty_env_atom_dom Σex ∪ lty_env_atom_dom (lty_env_shift Στ) ∪ fv_cty τx)
          by (apply denot_ty_obligations_body_gas_fv_subset; apply IHbody).
        assert (Hbody : formula_fv (denot_ty_obligations Σex Στx τ
              (tapp_tm (tm_shift 0 e) (vbvar 0))
              (denot_ty_body_lvar_gas gas Σex Στx τ
                (tapp_tm (tm_shift 0 e) (vbvar 0)))) ⊆
            lty_env_atom_dom Σex ∪ lty_env_atom_dom Στx ∪ fv_cty τ)
          by (apply denot_ty_obligations_body_gas_fv_subset; apply IHbody).
        subst Σex Στx.
        rewrite !lty_env_atom_dom_insert_bound in Hx.
        rewrite !lty_env_atom_dom_insert_bound in Hbody.
        rewrite !lty_env_atom_dom_shift in Hx.
        rewrite !lty_env_atom_dom_shift in Hbody.
        intros z Hz.
        cbn [formula_fv] in Hz.
        rewrite elem_of_union in Hz.
        destruct Hz as [Hz|Hz]; [apply Hx in Hz | apply Hbody in Hz];
          set_solver.
      - set (Σex := <[LVBound 0:=erase_ty τx]>(lty_env_shift Σe)).
        set (Στx := <[LVBound 0:=erase_ty τx]>(lty_env_shift Στ)).
        assert (Hx : formula_fv (denot_ty_obligations Σex (lty_env_shift Στ) τx
              (tret (vbvar 0))
              (denot_ty_body_lvar_gas gas Σex (lty_env_shift Στ) τx
                (tret (vbvar 0)))) ⊆
            lty_env_atom_dom Σex ∪ lty_env_atom_dom (lty_env_shift Στ) ∪ fv_cty τx)
          by (apply denot_ty_obligations_body_gas_fv_subset; apply IHbody).
        assert (Hbody : formula_fv (denot_ty_obligations Σex Στx τ
              (tapp_tm (tm_shift 0 e) (vbvar 0))
              (denot_ty_body_lvar_gas gas Σex Στx τ
                (tapp_tm (tm_shift 0 e) (vbvar 0)))) ⊆
            lty_env_atom_dom Σex ∪ lty_env_atom_dom Στx ∪ fv_cty τ)
          by (apply denot_ty_obligations_body_gas_fv_subset; apply IHbody).
        subst Σex Στx.
        rewrite !lty_env_atom_dom_insert_bound in Hx.
        rewrite !lty_env_atom_dom_insert_bound in Hbody.
        rewrite !lty_env_atom_dom_shift in Hx.
        rewrite !lty_env_atom_dom_shift in Hbody.
        intros z Hz.
        cbn [formula_fv] in Hz.
        rewrite elem_of_union in Hz.
        destruct Hz as [Hz|Hz]; [apply Hx in Hz | apply Hbody in Hz];
          set_solver.
    }
    split; [exact HbodyS |].
    intros Σe Στ τ e.
    unfold denot_ty_lvar_gas.
    apply denot_ty_obligations_body_gas_fv_subset.
    apply HbodyS.
Qed.

Lemma denot_ty_body_lvar_gas_fv_subset gas Σe Στ τ e :
  formula_fv (denot_ty_body_lvar_gas gas Σe Στ τ e) ⊆
    lty_env_atom_dom Σe ∪ lty_env_atom_dom Στ ∪ fv_cty τ.
Proof.
  exact (proj1 (denot_ty_gas_fv_subset gas) Σe Στ τ e).
Qed.

Lemma denot_ty_lvar_gas_fv_subset gas Σe Στ τ e :
  formula_fv (denot_ty_lvar_gas gas Σe Στ τ e) ⊆
    lty_env_atom_dom Σe ∪ lty_env_atom_dom Στ ∪ fv_cty τ.
Proof.
  exact (proj2 (denot_ty_gas_fv_subset gas) Σe Στ τ e).
Qed.

Lemma denot_ty_lvar_fv_subset Σe Στ τ e :
  formula_fv (denot_ty_lvar Σe Στ τ e) ⊆
    lty_env_atom_dom Σe ∪ lty_env_atom_dom Στ ∪ fv_cty τ.
Proof.
  unfold denot_ty_lvar.
  apply denot_ty_lvar_gas_fv_subset.
Qed.

Lemma denot_ty_body_lvar_fv_subset Σe Στ τ e :
  formula_fv (denot_ty_body_lvar Σe Στ τ e) ⊆
    lty_env_atom_dom Σe ∪ lty_env_atom_dom Στ ∪ fv_cty τ.
Proof.
  unfold denot_ty_body_lvar.
  apply denot_ty_body_lvar_gas_fv_subset.
Qed.

Lemma denot_ty_on_fv_subset Σ τ e :
  formula_fv (denot_ty_on Σ τ e) ⊆ dom Σ ∪ fv_cty τ.
Proof.
  unfold denot_ty_on.
  pose proof (denot_ty_lvar_fv_subset
    (atom_env_to_lty_env Σ) (atom_env_to_lty_env Σ) τ e) as Hfv.
  rewrite !atom_env_to_lty_env_atom_dom in Hfv.
  set_solver.
Qed.

Lemma denot_ty_body_fv_subset Σ τ e :
  formula_fv (denot_ty_body Σ τ e) ⊆ dom Σ ∪ fv_cty τ.
Proof.
  unfold denot_ty_body.
  pose proof (denot_ty_body_lvar_fv_subset
    (atom_env_to_lty_env Σ) (atom_env_to_lty_env Σ) τ e) as Hfv.
  rewrite !atom_env_to_lty_env_atom_dom in Hfv.
  set_solver.
Qed.

Lemma denot_ty_on_fv_subset_env
    (Σ : gmap atom ty) (τ : choice_ty) e :
  fv_cty τ ⊆ dom Σ →
  formula_fv (denot_ty_on Σ τ e) ⊆ dom Σ.
Proof.
  intros Hfv.
  pose proof (denot_ty_on_fv_subset Σ τ e) as Hφ.
  set_solver.
Qed.

Lemma denot_ty_body_fv_subset_env
    (Σ : gmap atom ty) (τ : choice_ty) e :
  fv_cty τ ⊆ dom Σ →
  formula_fv (denot_ty_body Σ τ e) ⊆ dom Σ.
Proof.
  intros Hfv.
  pose proof (denot_ty_body_fv_subset Σ τ e) as Hφ.
  set_solver.
Qed.

Lemma denot_ty_formula_fv_subset τ e :
  formula_fv (denot_ty τ e) ⊆ fv_cty τ.
Proof.
  unfold denot_ty, denot_ty_under.
  pose proof (denot_ty_on_fv_subset ∅ τ e) as Hfv.
  intros z Hz. apply Hfv in Hz. set_solver.
Qed.

Lemma denot_ty_under_fv_subset Σ τ e :
  formula_fv (denot_ty_under Σ τ e) ⊆ dom Σ ∪ fv_cty τ.
Proof.
  apply denot_ty_on_fv_subset.
Qed.

Lemma denot_ty_in_ctx_under_fv_subset Σ Γ τ e :
  formula_fv (denot_ty_in_ctx_under Σ Γ τ e) ⊆
    dom (erase_ctx_under Σ Γ) ∪ fv_cty τ.
Proof.
  unfold denot_ty_in_ctx_under.
  apply denot_ty_on_fv_subset.
Qed.

Lemma denot_ty_on_env_fv_subset Σ τ e :
  dom Σ ⊆ formula_fv (denot_ty_on Σ τ e).
Proof.
  unfold denot_ty_on, denot_ty_lvar, denot_ty_lvar_gas.
  unfold denot_ty_obligations, FBasicTypingIn, FClosedResourceIn,
    FStrongTotalIn, FStoreResourceAtom, FResourceAtom.
  cbn [formula_fv stale stale_logic_qualifier lqual_dom].
  denot_lvars_norm.
  rewrite !atom_env_to_lty_env_dom.
  rewrite !lvars_fv_union, !lvars_fv_of_atoms.
  set_solver.
Qed.

Lemma denot_ty_on_result_atom_fv Σ x τ :
  x ∈ dom Σ →
  x ∈ formula_fv (denot_ty_on Σ τ (tret (vfvar x))).
Proof.
  intros Hx.
  pose proof (denot_ty_on_env_fv_subset Σ τ (tret (vfvar x))) as Hfv.
  apply Hfv. exact Hx.
Qed.

Lemma denot_ty_under_result_atom_fv Σ x τ :
  x ∈ dom Σ →
  x ∈ formula_fv (denot_ty_under Σ τ (tret (vfvar x))).
Proof.
  unfold denot_ty_under.
  apply denot_ty_on_result_atom_fv.
Qed.

Lemma denot_ty_restrict_fv τ e m :
  m ⊨ denot_ty τ e →
  res_restrict m (fv_cty τ) ⊨ denot_ty τ e.
Proof.
  intros Hm.
  eapply res_models_kripke.
  - apply res_restrict_mono. apply denot_ty_formula_fv_subset.
  - apply res_models_restrict_fv. exact Hm.
Qed.

Lemma denot_ty_under_restrict_fv Σ τ e m :
  m ⊨ denot_ty_under Σ τ e →
  res_restrict m (dom Σ ∪ fv_cty τ) ⊨ denot_ty_under Σ τ e.
Proof.
  intros Hm.
  eapply res_models_kripke.
  - apply res_restrict_mono. apply denot_ty_under_fv_subset.
  - apply res_models_restrict_fv. exact Hm.
Qed.

(** ** Context denotation

    [denot_ctx_under Σ Γ] is the formula that holds when [Γ] is satisfied
    under the ambient erased basic environment [Σ].  The public
    [denot_ctx Γ] instantiates [Σ] with [erase_ctx Γ], so later binders in a
    comma context can be checked against earlier erased bindings. *)
