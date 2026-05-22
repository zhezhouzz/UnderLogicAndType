(** * ChoiceType.TypeDenotation.LemmasFormula

    Formula-opening, free-variable, and store-equivalence helpers for
    denotation constructors. *)

From Stdlib Require Import Logic.FunctionalExtensionality
  Logic.PropExtensionality Lia.
From LocallyNameless Require Import Tactics.
From CoreLang Require Import Instantiation InstantiationProps BasicTypingProps
  Sugar.
From ChoiceLogic Require Import FormulaDerived.
From ChoiceType Require Export TypeDenotation.LemmasEnv.
From ChoiceType Require Import BasicStore BasicTyping LocallyNamelessProps
  TypeDenotation.FormulaEquiv.

Local Notation FQ := FormulaQ.

Lemma formula_fv_open_FDenotObligationIn k x Σ τ e :
  formula_fv (formula_open k x (FDenotObligationIn Σ τ e)) =
  formula_fv (FDenotObligationIn ({k ~> x} Σ)
    ({k ~> x} τ) ({k ~> x} e)).
Proof.
  unfold FDenotObligationIn.
  rewrite formula_open_FStoreResourceAtom_lvars.
  rewrite !formula_fv_FStoreResourceAtom_lvars.
  change (dom ({k ~> x} Σ)) with (dom (lty_env_open_one k x Σ)).
  rewrite lty_env_open_one_dom.
  reflexivity.
Qed.

Lemma formula_store_equiv_open_FDenotObligationIn k x Σ τ e :
  formula_store_equiv
    (formula_open k x (FDenotObligationIn Σ τ e))
    (FDenotObligationIn ({k ~> x} Σ) ({k ~> x} τ) ({k ~> x} e)).
Proof.
  unfold formula_store_equiv. intros ρ m.
  unfold FDenotObligationIn.
  rewrite formula_open_FStoreResourceAtom_lvars.
  change (dom ({k ~> x} Σ)) with (dom (lty_env_open_one k x Σ)).
  rewrite lty_env_open_one_dom.
  split; intro Hm.
  - destruct (res_models_with_store_store_resource_atom_vars_elim ρ m
      (lvars_open k x (dom Σ))
      (fun η σ m =>
        denot_obligation_parts Σ τ e (<[k := x]> η) σ m)
      Hm) as [m0 [Hscope0 [Hparts Hle]]].
    eapply res_models_with_store_store_resource_atom_vars_witness_intro.
    + pose proof (res_models_with_store_fuel_scoped _ ρ m
        (FStoreResourceAtom (lvars_open k x (dom Σ))
          (fun η σ m =>
            denot_obligation_parts Σ τ e (<[k := x]> η) σ m)) Hm)
        as Hscope.
      exact Hscope.
    + exact Hscope0.
    + unfold denot_obligation_parts in *.
      rewrite lty_env_open_lvars_open_one_empty.
      rewrite open_cty_env_empty.
      rewrite open_cty_env_singleton in Hparts.
      change ({k ~> x} e) with (open_tm k (vfvar x) e).
      rewrite open_tm_env_open_tm.
      rewrite closed_resource_lvar_open.
      change (open_tm k (vfvar x) e) with ({k ~> x} e).
      rewrite expr_total_lvar_open.
      exact Hparts.
    + exact Hle.
  - destruct (res_models_with_store_store_resource_atom_vars_elim ρ m
      (lvars_open k x (dom Σ))
      (denot_obligation_parts (lty_env_open_one k x Σ)
        ({k ~> x} τ) ({k ~> x} e))
      Hm) as [m0 [Hscope0 [Hparts Hle]]].
    eapply res_models_with_store_store_resource_atom_vars_witness_intro.
    + pose proof (res_models_with_store_fuel_scoped _ ρ m
        (FStoreResourceAtom (lvars_open k x (dom Σ))
          (denot_obligation_parts (lty_env_open_one k x Σ)
            ({k ~> x} τ) ({k ~> x} e))) Hm)
        as Hscope.
      exact Hscope.
    + exact Hscope0.
    + unfold denot_obligation_parts in *.
      rewrite lty_env_open_lvars_open_one_empty in Hparts.
      rewrite open_cty_env_empty in Hparts.
      rewrite open_cty_env_singleton.
      change ({k ~> x} e) with (open_tm k (vfvar x) e) in Hparts.
      rewrite open_tm_env_open_tm in Hparts.
      rewrite closed_resource_lvar_open in Hparts.
      change (open_tm k (vfvar x) e) with ({k ~> x} e) in Hparts.
      rewrite expr_total_lvar_open in Hparts.
      exact Hparts.
	    + exact Hle.
Qed.

Lemma formula_fv_open_env_FDenotObligationIn η Σ τ e :
  formula_fv (formula_open_env η (FDenotObligationIn Σ τ e)) =
  formula_fv (FDenotObligationIn
    (lty_env_open_lvars η Σ) (open_cty_env η τ) (open_tm_env η e)).
Proof.
  unfold FDenotObligationIn.
  rewrite formula_open_env_FStoreResourceAtom_lvars.
  rewrite !formula_fv_FStoreResourceAtom_lvars.
  rewrite lty_env_open_lvars_dom.
  rewrite lvars_fv_open_env_simul.
  reflexivity.
Qed.

Lemma denot_obligation_parts_open_env_empty η Σ τ e ρ m :
  denot_obligation_parts (lty_env_open_lvars η Σ)
    (open_cty_env η τ) (open_tm_env η e) ∅ ρ m ↔
  denot_obligation_parts Σ τ e η ρ m.
Proof.
  unfold denot_obligation_parts.
  rewrite !lty_env_open_lvars_empty.
  rewrite !open_cty_env_empty, !open_tm_env_empty.
  rewrite closed_resource_lvar_open_env_empty.
  rewrite expr_total_lvar_open_env_empty.
  reflexivity.
Qed.

Lemma formula_store_equiv_open_env_FDenotObligationIn η Σ τ e :
  formula_store_equiv
    (formula_open_env η (FDenotObligationIn Σ τ e))
    (FDenotObligationIn
      (lty_env_open_lvars η Σ) (open_cty_env η τ) (open_tm_env η e)).
Proof.
  unfold formula_store_equiv. intros ρ m.
  unfold FDenotObligationIn.
  rewrite formula_open_env_FStoreResourceAtom_lvars.
  rewrite lty_env_open_lvars_dom.
  rewrite lvars_open_env_simul_eq.
  split; intro Hm.
  - destruct (res_models_with_store_store_resource_atom_vars_elim ρ m
      (lvars_open_env η (dom Σ))
      (fun ξ σ m =>
        denot_obligation_parts Σ τ e (open_env_precompose η ξ) σ m)
      Hm) as [m0 [Hscope0 [Hparts Hle]]].
    eapply res_models_with_store_store_resource_atom_vars_witness_intro.
    + pose proof (res_models_with_store_fuel_scoped _ ρ m
        (FStoreResourceAtom (lvars_open_env η (dom Σ))
          (fun ξ σ m =>
            denot_obligation_parts Σ τ e
              (open_env_precompose η ξ) σ m)) Hm)
        as Hscope.
      exact Hscope.
    + exact Hscope0.
    + rewrite open_env_precompose_empty_r in Hparts.
      apply denot_obligation_parts_open_env_empty.
      exact Hparts.
    + exact Hle.
  - destruct (res_models_with_store_store_resource_atom_vars_elim ρ m
      (lvars_open_env η (dom Σ))
      (denot_obligation_parts (lty_env_open_lvars η Σ)
        (open_cty_env η τ) (open_tm_env η e))
      Hm) as [m0 [Hscope0 [Hparts Hle]]].
    eapply res_models_with_store_store_resource_atom_vars_witness_intro.
    + pose proof (res_models_with_store_fuel_scoped _ ρ m
        (FStoreResourceAtom (lvars_open_env η (dom Σ))
          (denot_obligation_parts (lty_env_open_lvars η Σ)
            (open_cty_env η τ) (open_tm_env η e))) Hm)
        as Hscope.
      exact Hscope.
    + exact Hscope0.
    + rewrite open_env_precompose_empty_r.
      apply denot_obligation_parts_open_env_empty.
      exact Hparts.
    + exact Hle.
Qed.

Lemma formula_store_equiv_FDenotObligationIn_cty_vars_equiv Σ τ1 τ2 e :
  τ1 ≡τv τ2 →
  formula_store_equiv
    (FDenotObligationIn Σ τ1 e)
    (FDenotObligationIn Σ τ2 e).
Proof.
  intros Hτ ρ m.
  unfold FDenotObligationIn, FStoreResourceAtom, res_models_with_store.
  cbn [formula_measure res_models_with_store_fuel formula_scoped_in_world
    formula_fv stale logic_qualifier_denote lqual_dom lqual_prop].
  split; intros [Hscope Hex]; split; [exact Hscope | | exact Hscope |].
  - destruct Hex as [m0 [Hscope0 [Hparts Hle]]].
    exists m0. split; [exact Hscope0 |]. split; [| exact Hle].
    unfold denot_obligation_parts in *.
    destruct Hparts as [Hbasic [Htyping [Hclosed Htotal]]].
    split.
    + eapply basic_choice_ty_lvar_cty_vars_equiv; [| exact Hbasic].
      apply open_cty_env_cty_vars_equiv. exact Hτ.
    + split.
      * rewrite <- (cty_vars_equiv_erase _ _
          (open_cty_env_cty_vars_equiv _ _ _ Hτ)).
        exact Htyping.
      * split; [exact Hclosed | exact Htotal].
  - destruct Hex as [m0 [Hscope0 [Hparts Hle]]].
    exists m0. split; [exact Hscope0 |]. split; [| exact Hle].
    unfold denot_obligation_parts in *.
    destruct Hparts as [Hbasic [Htyping [Hclosed Htotal]]].
    split.
    + eapply basic_choice_ty_lvar_cty_vars_equiv; [| exact Hbasic].
      symmetry. apply open_cty_env_cty_vars_equiv. exact Hτ.
    + split.
      * rewrite (cty_vars_equiv_erase _ _
          (open_cty_env_cty_vars_equiv _ _ _ Hτ)).
        exact Htyping.
      * split; [exact Hclosed | exact Htotal].
Qed.

Lemma formula_open_FClosedResourceIn k x Σ :
  formula_open k x (FClosedResourceIn Σ) =
  FClosedResourceIn ({k ~> x} Σ).
Proof.
  unfold FClosedResourceIn.
  rewrite formula_open_FStoreResourceAtom_lvars.
  change (dom ({k ~> x} Σ)) with (dom (lty_env_open_one k x Σ)).
  rewrite lty_env_open_one_dom.
  f_equal.
  apply functional_extensionality; intro η.
  apply functional_extensionality; intro ρ.
  apply functional_extensionality; intro m.
  symmetry. apply closed_resource_lvar_open.
Qed.

Lemma formula_fv_open_FClosedResourceIn k x Σ :
  formula_fv (formula_open k x (FClosedResourceIn Σ)) =
  formula_fv (FClosedResourceIn ({k ~> x} Σ)).
Proof.
  rewrite formula_open_FClosedResourceIn. reflexivity.
Qed.

Lemma formula_store_equiv_open_FClosedResourceIn k x Σ :
  formula_store_equiv
    (formula_open k x (FClosedResourceIn Σ))
    (FClosedResourceIn ({k ~> x} Σ)).
Proof.
  rewrite formula_open_FClosedResourceIn.
  apply formula_store_equiv_refl.
Qed.

Lemma closed_resource_lvar_open_env η ξ Σ m :
  closed_resource_lvar (lty_env_open_lvars η Σ) ξ m =
  closed_resource_lvar Σ (open_env_precompose η ξ) m.
Proof.
  unfold closed_resource_lvar.
  rewrite lty_env_open_lvars_dom.
  rewrite lvars_open_env_simul_eq.
  rewrite lvars_to_atoms_open_env.
  reflexivity.
Qed.

Lemma formula_open_env_FClosedResourceIn η Σ :
  formula_open_env η (FClosedResourceIn Σ) =
  FClosedResourceIn (lty_env_open_lvars η Σ).
Proof.
  unfold FClosedResourceIn.
  rewrite formula_open_env_FStoreResourceAtom_lvars.
  rewrite lty_env_open_lvars_dom.
  rewrite lvars_open_env_simul_eq.
  f_equal.
  apply functional_extensionality; intro ξ.
  apply functional_extensionality; intro σ.
  apply functional_extensionality; intro m.
  symmetry. apply closed_resource_lvar_open_env.
Qed.

Lemma formula_fv_open_env_FClosedResourceIn η Σ :
  formula_fv (formula_open_env η (FClosedResourceIn Σ)) =
  formula_fv (FClosedResourceIn (lty_env_open_lvars η Σ)).
Proof.
  rewrite formula_open_env_FClosedResourceIn. reflexivity.
Qed.

Lemma formula_fv_FClosedResourceIn_atom_env (Δ : gmap atom ty) :
  formula_fv (FClosedResourceIn (atom_env_to_lty_env Δ)) = dom Δ.
Proof.
  unfold FClosedResourceIn.
  rewrite formula_fv_FStoreResourceAtom_lvars.
  rewrite atom_env_to_lty_env_dom.
  apply lvars_fv_of_atoms.
Qed.

Lemma formula_fv_open_FClosedResourceIn_typed_bind_atom_env
    (Δ : gmap atom ty) T y :
  y ∉ dom Δ ->
  formula_fv (formula_open 0 y
    (FClosedResourceIn (typed_lty_env_bind (atom_env_to_lty_env Δ) T))) =
  dom (<[y := T]> Δ).
Proof.
  intros Hy.
  rewrite formula_open_FClosedResourceIn.
  rewrite lty_env_open_typed_bind_atom_env by exact Hy.
  apply formula_fv_FClosedResourceIn_atom_env.
Qed.

Lemma formula_store_equiv_open_env_FClosedResourceIn η Σ :
  formula_store_equiv
    (formula_open_env η (FClosedResourceIn Σ))
    (FClosedResourceIn (lty_env_open_lvars η Σ)).
Proof.
  rewrite formula_open_env_FClosedResourceIn.
  apply formula_store_equiv_refl.
Qed.

Lemma typed_lty_env_bind_open_under k x Σ T :
  LVFree x ∉ dom Σ →
  {S k ~> x} (typed_lty_env_bind Σ T) =
  typed_lty_env_bind ({k ~> x} Σ) T.
Proof.
  intros Hfresh.
  unfold typed_lty_env_bind.
  apply lty_env_open_one_shift_insert_bound. exact Hfresh.
Qed.

Lemma typed_lty_env_bind_free_notin x Σ T :
  LVFree x ∉ dom Σ →
  LVFree x ∉ dom (typed_lty_env_bind Σ T).
Proof.
  intros Hfresh Hbad.
  unfold typed_lty_env_bind in Hbad.
  apply elem_of_dom in Hbad as [Tx Hlookup].
  change ((<[LVBound 0 := T]> (lty_env_shift Σ) : lty_env) !!
    LVFree x = Some Tx) in Hlookup.
  rewrite (lookup_insert_ne (lty_env_shift Σ) (LVBound 0) (LVFree x) T)
    in Hlookup by discriminate.
  apply elem_of_dom_2 in Hlookup.
  apply lty_env_shift_free_notin in Hfresh.
  contradiction.
Qed.

Lemma formula_open_FForallTypedBody_under k x Σ T Q :
  LVFree x ∉ dom Σ →
  formula_open (S k) x (FForallTypedBody Σ T Q) =
  FImpl
    (FClosedResourceIn (typed_lty_env_bind ({k ~> x} Σ) T))
    (formula_open (S k) x (Q (typed_lty_env_bind Σ T))).
Proof.
  intros Hfresh.
  unfold FForallTypedBody.
  rewrite formula_open_impl.
  rewrite formula_open_FClosedResourceIn.
  rewrite typed_lty_env_bind_open_under by exact Hfresh.
  reflexivity.
Qed.

Lemma formula_open_FForallTypedBind k x Σ T Q :
  LVFree x ∉ dom Σ →
  formula_open k x (FForallTypedBind Σ T Q) =
  FForall
    (FImpl
      (FClosedResourceIn (typed_lty_env_bind ({k ~> x} Σ) T))
      (formula_open (S k) x (Q (typed_lty_env_bind Σ T)))).
Proof.
  intros Hfresh.
  unfold FForallTypedBind.
  rewrite formula_open_forall.
  rewrite formula_open_FForallTypedBody_under by exact Hfresh.
  reflexivity.
Qed.

Lemma formula_fv_open_FForallTypedBody_under k x Σ T Q Q' :
  LVFree x ∉ dom Σ →
  formula_fv (formula_open (S k) x (Q (typed_lty_env_bind Σ T))) =
  formula_fv (Q' (typed_lty_env_bind ({k ~> x} Σ) T)) →
  formula_fv (formula_open (S k) x (FForallTypedBody Σ T Q)) =
  formula_fv (FForallTypedBody ({k ~> x} Σ) T Q').
Proof.
  intros Hfresh HQ.
  rewrite formula_open_FForallTypedBody_under by exact Hfresh.
  unfold FForallTypedBody.
  cbn [formula_fv].
  rewrite HQ.
  reflexivity.
Qed.

Lemma formula_fv_open_FForallTypedBind k x Σ T Q Q' :
  LVFree x ∉ dom Σ →
  formula_fv (formula_open (S k) x (Q (typed_lty_env_bind Σ T))) =
  formula_fv (Q' (typed_lty_env_bind ({k ~> x} Σ) T)) →
  formula_fv (formula_open k x (FForallTypedBind Σ T Q)) =
  formula_fv (FForallTypedBind ({k ~> x} Σ) T Q').
Proof.
  intros Hfresh HQ.
  unfold FForallTypedBind.
  rewrite formula_open_forall.
  cbn [formula_fv].
  eapply formula_fv_open_FForallTypedBody_under; eauto.
Qed.

Lemma formula_store_equiv_open_FForallTypedBody_under
    k x Σ T Q Q' :
  LVFree x ∉ dom Σ →
  formula_fv (formula_open (S k) x (Q (typed_lty_env_bind Σ T))) =
  formula_fv (Q' (typed_lty_env_bind ({k ~> x} Σ) T)) →
  (∀ y,
    LVFree y ∉ dom ({k ~> x} Σ) →
    formula_fv
      (formula_open 0 y
        (formula_open (S k) x (Q (typed_lty_env_bind Σ T)))) =
    formula_fv
      (formula_open 0 y
        (Q' (typed_lty_env_bind ({k ~> x} Σ) T)))) →
  (∀ y,
    LVFree y ∉ dom ({k ~> x} Σ) →
    formula_store_equiv
      (formula_open 0 y
        (formula_open (S k) x (Q (typed_lty_env_bind Σ T))))
      (formula_open 0 y
        (Q' (typed_lty_env_bind ({k ~> x} Σ) T)))) →
  formula_store_equiv
    (formula_open (S k) x (Q (typed_lty_env_bind Σ T)))
    (Q' (typed_lty_env_bind ({k ~> x} Σ) T)) →
  formula_store_equiv
    (formula_open (S k) x (FForallTypedBody Σ T Q))
    (FForallTypedBody ({k ~> x} Σ) T Q').
Proof.
  intros Hfresh HQfv Hopen_fv Hopen_eq HQeq.
  rewrite formula_open_FForallTypedBody_under by exact Hfresh.
  unfold FForallTypedBody.
  eapply formula_store_equiv_impl.
  - reflexivity.
  - exact HQfv.
  - apply formula_store_equiv_refl.
  - exact HQeq.
Qed.

Lemma formula_store_equiv_open_FForallTypedBind k x Σ T Q Q' :
  LVFree x ∉ dom Σ →
  formula_fv (formula_open (S k) x (Q (typed_lty_env_bind Σ T))) =
  formula_fv (Q' (typed_lty_env_bind ({k ~> x} Σ) T)) →
  (∀ y,
    LVFree y ∉ dom ({k ~> x} Σ) →
    formula_fv
      (formula_open 0 y
        (formula_open (S k) x (Q (typed_lty_env_bind Σ T)))) =
    formula_fv
      (formula_open 0 y
        (Q' (typed_lty_env_bind ({k ~> x} Σ) T)))) →
  (∀ y,
    LVFree y ∉ dom ({k ~> x} Σ) →
    formula_store_equiv
      (formula_open 0 y
        (formula_open (S k) x (Q (typed_lty_env_bind Σ T))))
      (formula_open 0 y
        (Q' (typed_lty_env_bind ({k ~> x} Σ) T)))) →
  formula_store_equiv
    (formula_open k x (FForallTypedBind Σ T Q))
    (FForallTypedBind ({k ~> x} Σ) T Q').
Proof.
  intros Hfresh HQfv Hopen_fv Hopen_eq.
  unfold FForallTypedBind.
  rewrite formula_open_forall.
  eapply (formula_store_equiv_forall_fresh (lvars_fv (dom ({k ~> x} Σ)))).
  - eapply formula_fv_open_FForallTypedBody_under; eauto.
  - intros y Hy.
    assert (HyΣ : LVFree y ∉ dom ({k ~> x} Σ)).
    { intros Hbad. apply Hy. apply lvars_fv_elem. exact Hbad. }
    rewrite formula_open_FForallTypedBody_under by exact Hfresh.
    unfold FForallTypedBody.
    rewrite formula_open_impl.
    eapply formula_store_equiv_impl.
    + reflexivity.
    + apply Hopen_fv. exact HyΣ.
    + apply formula_store_equiv_refl.
	    + apply Hopen_eq. exact HyΣ.
Qed.

Lemma formula_store_equiv_FForallTypedBind Σ T Q Q' :
  formula_fv (Q (typed_lty_env_bind Σ T)) =
  formula_fv (Q' (typed_lty_env_bind Σ T)) →
  (∀ y,
    LVFree y ∉ dom Σ →
    formula_fv (formula_open 0 y (Q (typed_lty_env_bind Σ T))) =
    formula_fv (formula_open 0 y (Q' (typed_lty_env_bind Σ T)))) →
  (∀ y,
    LVFree y ∉ dom Σ →
    formula_store_equiv
      (formula_open 0 y (Q (typed_lty_env_bind Σ T)))
      (formula_open 0 y (Q' (typed_lty_env_bind Σ T)))) →
  formula_store_equiv (FForallTypedBind Σ T Q) (FForallTypedBind Σ T Q').
Proof.
  intros HQfv Hopen_fv Hopen_eq.
  unfold FForallTypedBind.
  eapply (formula_store_equiv_forall_fresh (lvars_fv (dom Σ))).
  - unfold FForallTypedBody. cbn [formula_fv].
    rewrite HQfv. reflexivity.
  - intros y Hy.
    assert (HyΣ : LVFree y ∉ dom Σ).
    { intros Hbad. apply Hy. apply lvars_fv_elem. exact Hbad. }
    unfold FForallTypedBody.
    rewrite formula_open_impl.
    eapply formula_store_equiv_impl.
    + reflexivity.
    + apply Hopen_fv. exact HyΣ.
    + apply formula_store_equiv_refl.
    + apply Hopen_eq. exact HyΣ.
Qed.

Lemma formula_open_FForallTypedBind_atom_env_const
    k x (Σ : gmap atom ty) T Q :
  x ∉ dom Σ →
  formula_open k x
    (FForallTypedBind (atom_env_to_lty_env Σ) T (fun _ => Q)) =
  FForallTypedBind (atom_env_to_lty_env Σ) T
    (fun _ => formula_open (S k) x Q).
Proof.
  intros Hfresh.
  rewrite formula_open_FForallTypedBind.
  2:{
    rewrite atom_env_to_lty_env_dom.
    unfold lvars_of_atoms.
    intros Hin. apply elem_of_map in Hin as [y [Hy HyΣ]].
    inversion Hy. subst y. exact (Hfresh HyΣ).
  }
  unfold FForallTypedBind, FForallTypedBody, typed_lty_env_bind.
  rewrite lty_env_open_one_atom_env.
  reflexivity.
Qed.

Lemma formula_open_FExprContBody_under k x Σ T e Q :
  LVFree x ∉ dom Σ →
  formula_open (S k) x (FExprContBody Σ T e Q) =
  FImpl
    (FClosedResourceIn (typed_lty_env_bind ({k ~> x} Σ) T))
    (formula_open (S k) x
      (FImpl
        (FExprResultAtLvar (dom (typed_lty_env_bind Σ T))
          (↑[0] e) (LVBound 0))
        (Q (typed_lty_env_bind Σ T)))).
Proof.
  intros Hfresh.
  unfold FExprContBody, FForallTypedBody.
  rewrite formula_open_impl.
  rewrite formula_open_FClosedResourceIn.
  rewrite typed_lty_env_bind_open_under by exact Hfresh.
  reflexivity.
Qed.

Lemma formula_open_FExprContIn k x Σ T e Q :
  LVFree x ∉ dom Σ →
  formula_open k x (FExprContIn Σ T e Q) =
  FForall
    (FImpl
      (FClosedResourceIn (typed_lty_env_bind ({k ~> x} Σ) T))
      (formula_open (S k) x
        (FImpl
          (FExprResultAtLvar (dom (typed_lty_env_bind Σ T))
            (↑[0] e) (LVBound 0))
          (Q (typed_lty_env_bind Σ T))))).
Proof.
  intros Hfresh.
  unfold FExprContIn.
  rewrite formula_open_forall.
  rewrite formula_open_FExprContBody_under by exact Hfresh.
  reflexivity.
Qed.

Lemma formula_open_FForallTypedBody_atom_env_branch
    (Σ : gmap atom ty) T y Q :
  y ∉ dom Σ →
  formula_open 0 y
    (FForallTypedBody (atom_env_to_lty_env Σ) T (fun _ => Q)) =
  FImpl
    (FClosedResourceIn (atom_env_to_lty_env (<[y := T]> Σ)))
    (formula_open 0 y Q).
Proof.
  intros Hy.
  unfold FForallTypedBody, typed_lty_env_bind.
  rewrite formula_open_impl.
  rewrite formula_open_FClosedResourceIn.
  rewrite lty_env_open_one_bind_atom_env by exact Hy.
  reflexivity.
Qed.

Lemma formula_open_FExprResultOn_atom_env
    (Σ : gmap atom ty) e y :
  y ∉ dom Σ →
  lc_tm e →
  formula_open 0 y
    (FExprResultAtLvar
      (lvars_shift (lvars_of_atoms (dom Σ)) ∪ {[LVBound 0]})
      (tm_shift 0 e) (LVBound 0)) =
  FExprResultAt (dom Σ) e y.
Proof.
  intros Hy Hlc.
  apply formula_open_FExprResultAtLvar_shift_atom; eauto.
Qed.

Lemma logic_var_open_succ_eq_bound0 k x v :
  logic_var_open (S k) x v = LVBound 0 ↔ v = LVBound 0.
Proof.
  destruct v as [n|y]; cbn [logic_var_open].
  - destruct n as [|n].
    + split; intros _; reflexivity.
    + destruct (decide (S n = S k)) as [Heq|Hne].
      * inversion Heq. subst n.
        split; intros H; inversion H.
      * split; intros H; inversion H.
  - split; intros H; inversion H.
Qed.

Lemma lvars_open_succ_difference_bound0 k x (D : lvset) :
  lvars_open (S k) x (D ∖ {[LVBound 0]}) =
  lvars_open (S k) x D ∖ {[LVBound 0]}.
Proof.
  apply set_eq. intros v.
  unfold lvars_open.
  rewrite elem_of_difference.
  rewrite !elem_of_map.
  split.
  - intros [u [-> Hu]].
    apply elem_of_difference in Hu as [Hu Hne].
    split.
    + exists u. split; [reflexivity | exact Hu].
    + intros Hv.
      apply Hne.
      apply elem_of_singleton in Hv.
      apply elem_of_singleton.
      apply logic_var_open_succ_eq_bound0 in Hv.
      exact Hv.
  - intros [[u [-> Hu]] Hne].
    exists u. split; [reflexivity |].
    apply elem_of_difference. split; [exact Hu |].
    intros Hu0. apply Hne.
    apply elem_of_singleton.
    apply elem_of_singleton in Hu0. subst u.
    cbn [logic_var_open].
    reflexivity.
Qed.

Lemma formula_open_FExprResultAtLvar_typed_under k x Σ T e :
  LVFree x ∉ dom Σ →
  formula_open (S k) x
    (FExprResultAtLvar (dom (typed_lty_env_bind Σ T))
      (↑[0] e) (LVBound 0)) =
  FExprResultAtLvar (dom (typed_lty_env_bind ({k ~> x} Σ) T))
    (↑[0] ({k ~> x} e)) (LVBound 0).
Proof.
  intros Hfresh.
  rewrite formula_open_FExprResultAtLvar_raw.
  unfold FExprResultAtLvar.
  rewrite <- (typed_lty_env_bind_open_under k x Σ T Hfresh).
  rewrite lty_env_open_one_dom.
  rewrite lvars_open_succ_difference_bound0.
  f_equal. f_equal.
  apply functional_extensionality; intro η.
  apply functional_extensionality; intro σ.
  apply functional_extensionality; intro w.
  cbn [logic_var_to_atom].
  rewrite lookup_insert_ne by lia.
  rewrite <- lvars_to_atoms_open.
  rewrite lvars_open_succ_difference_bound0.
  change (↑[0] e) with (tm_shift 0 e).
  change (↑[0] ({k ~> x} e)) with (tm_shift 0 (open_tm k (vfvar x) e)).
  rewrite open_tm_env_shift_open_one.
  reflexivity.
Qed.

Lemma formula_fv_open_FResultQualifier_over_body k x φ :
  formula_fv
    (formula_open (S k) x
      (FFibVars (qual_vars φ ∖ {[LVBound 0]})
        (FOver (FTypeQualifier φ)))) =
  formula_fv
    (FFibVars (qual_vars ({S k ~> x} φ) ∖ {[LVBound 0]})
      (FOver (FTypeQualifier ({S k ~> x} φ)))).
Proof.
  rewrite formula_open_fibvars, formula_open_over.
  cbn [formula_fv].
  rewrite lvars_open_succ_difference_bound0.
  rewrite qual_vars_open_atom.
  rewrite FTypeQualifier_open_fv.
  reflexivity.
Qed.

Lemma formula_fv_FResultQualifier_over_body_vars φ :
  formula_fv
    (FFibVars (qual_vars φ ∖ {[LVBound 0]})
      (FOver (FTypeQualifier φ))) =
  lvars_fv (qual_vars φ).
Proof.
  destruct φ as [D p].
  cbn [formula_fv].
  change (formula_fv (FTypeQualifier (qual D p))) with (lvars_fv D).
  pose proof (lvars_fv_difference_subset D {[LVBound 0]}) as Hsub.
  set_solver.
Qed.

Lemma formula_fv_open_env_FResultQualifier_over_body_vars η φ :
  formula_fv
    (formula_open_env (open_env_lift η)
      (FFibVars (qual_vars φ ∖ {[LVBound 0]})
        (FOver (FTypeQualifier φ)))) =
  lvars_fv (lvars_open_env (open_env_lift η) (qual_vars φ)).
Proof.
  destruct φ as [D p].
  rewrite formula_open_env_fibvars, formula_open_env_over.
  cbn [formula_fv].
  unfold FTypeQualifier.
  rewrite formula_open_env_FStoreResourceAtom_lvars.
  rewrite formula_fv_FStoreResourceAtom_lvars.
  pose proof (lvars_fv_mono _ _
    (lvars_open_env_mono (open_env_lift η)
      (D ∖ {[LVBound 0]}) D ltac:(set_solver)))
    as Hsub.
  set_solver.
Qed.

Lemma formula_store_equiv_open_FResultQualifier_over_body k x φ :
  formula_store_equiv
    (formula_open (S k) x
      (FFibVars (qual_vars φ ∖ {[LVBound 0]})
        (FOver (FTypeQualifier φ))))
    (FFibVars (qual_vars ({S k ~> x} φ) ∖ {[LVBound 0]})
      (FOver (FTypeQualifier ({S k ~> x} φ)))).
Proof.
  rewrite formula_open_fibvars, formula_open_over.
  eapply formula_store_equiv_fibvars.
  - rewrite lvars_open_succ_difference_bound0.
    rewrite qual_vars_open_atom.
    reflexivity.
  - cbn [formula_fv]. apply FTypeQualifier_open_fv.
  - eapply formula_store_equiv_over.
	    + apply FTypeQualifier_open_fv.
	    + apply FTypeQualifier_open_store_equiv.
Qed.

Lemma formula_fv_open_FResultQualifier_under_body k x φ :
  formula_fv
    (formula_open (S k) x
      (FFibVars (qual_vars φ ∖ {[LVBound 0]})
        (FUnder (FTypeQualifier φ)))) =
  formula_fv
    (FFibVars (qual_vars ({S k ~> x} φ) ∖ {[LVBound 0]})
      (FUnder (FTypeQualifier ({S k ~> x} φ)))).
Proof.
  rewrite formula_open_fibvars, formula_open_under.
  cbn [formula_fv].
  rewrite lvars_open_succ_difference_bound0.
  rewrite qual_vars_open_atom.
  rewrite FTypeQualifier_open_fv.
  reflexivity.
Qed.

Lemma formula_fv_FResultQualifier_under_body_vars φ :
  formula_fv
    (FFibVars (qual_vars φ ∖ {[LVBound 0]})
      (FUnder (FTypeQualifier φ))) =
  lvars_fv (qual_vars φ).
Proof.
  destruct φ as [D p].
  cbn [formula_fv].
  change (formula_fv (FTypeQualifier (qual D p))) with (lvars_fv D).
  pose proof (lvars_fv_difference_subset D {[LVBound 0]}) as Hsub.
  set_solver.
Qed.

Lemma formula_fv_open_env_FResultQualifier_under_body_vars η φ :
  formula_fv
    (formula_open_env (open_env_lift η)
      (FFibVars (qual_vars φ ∖ {[LVBound 0]})
        (FUnder (FTypeQualifier φ)))) =
  lvars_fv (lvars_open_env (open_env_lift η) (qual_vars φ)).
Proof.
  destruct φ as [D p].
  rewrite formula_open_env_fibvars, formula_open_env_under.
  cbn [formula_fv].
  unfold FTypeQualifier.
  rewrite formula_open_env_FStoreResourceAtom_lvars.
  rewrite formula_fv_FStoreResourceAtom_lvars.
  pose proof (lvars_fv_mono _ _
    (lvars_open_env_mono (open_env_lift η)
      (D ∖ {[LVBound 0]}) D ltac:(set_solver)))
    as Hsub.
  set_solver.
Qed.

Lemma formula_store_equiv_open_FResultQualifier_under_body k x φ :
  formula_store_equiv
    (formula_open (S k) x
      (FFibVars (qual_vars φ ∖ {[LVBound 0]})
        (FUnder (FTypeQualifier φ))))
    (FFibVars (qual_vars ({S k ~> x} φ) ∖ {[LVBound 0]})
      (FUnder (FTypeQualifier ({S k ~> x} φ)))).
Proof.
  rewrite formula_open_fibvars, formula_open_under.
  eapply formula_store_equiv_fibvars.
  - rewrite lvars_open_succ_difference_bound0.
    rewrite qual_vars_open_atom.
    reflexivity.
  - cbn [formula_fv]. apply FTypeQualifier_open_fv.
  - eapply formula_store_equiv_under.
	    + apply FTypeQualifier_open_fv.
	    + apply FTypeQualifier_open_store_equiv.
Qed.

Lemma FTypeQualifier_open2_fv k x y φ :
  formula_fv
    (formula_open 0 y (formula_open (S k) x (FTypeQualifier φ))) =
  formula_fv (FTypeQualifier ({0 ~> y} ({S k ~> x} φ))).
Proof.
  destruct φ as [D p].
  unfold FTypeQualifier, FStoreResourceAtom.
  cbn [formula_open formula_fv stale stale_logic_qualifier lqual_dom lqual_open
    qual_vars open_one open_qual_atom_inst qual_open_atom qual_bvars].
  change (into_lvars D) with D.
  destruct (decide (S k ∈ lvars_bv D)) as [Hk|Hk];
    cbn [open_one open_qual_atom_inst qual_open_atom qual_bvars
      formula_fv stale stale_logic_qualifier lqual_dom].
  - destruct (decide (0 ∈ lvars_bv (lvars_open (S k) x D))) as [H0|H0];
      cbn [formula_fv stale stale_logic_qualifier lqual_dom];
      change (into_lvars ?X) with X.
    + reflexivity.
    + rewrite lvars_open_no_bv by exact H0. reflexivity.
  - replace (lvars_open (S k) x D) with D by
      (symmetry; apply lvars_open_no_bv; exact Hk).
    destruct (decide (0 ∈ lvars_bv D)) as [H0|H0];
      cbn [formula_fv stale stale_logic_qualifier lqual_dom];
      change (into_lvars ?X) with X.
    + reflexivity.
    + rewrite lvars_open_no_bv by exact H0. reflexivity.
Qed.

Lemma FTypeQualifier_open2_store_equiv k x y φ :
  formula_store_equiv
    (formula_open 0 y (formula_open (S k) x (FTypeQualifier φ)))
    (formula_open 0 y (FTypeQualifier ({S k ~> x} φ))).
Proof.
  destruct φ as [D p].
  unfold formula_store_equiv; intros ρ m.
  unfold FTypeQualifier, FStoreResourceAtom, res_models_with_store.
  cbn [formula_open formula_measure res_models_with_store_fuel
    formula_scoped_in_world formula_fv stale stale_logic_qualifier
    lqual_dom logic_qualifier_denote lqual_prop lqual_open
    open_one open_qual_atom_inst qual_open_atom qual_vars qual_bvars].
  change (into_lvars D) with D.
  destruct (decide (S k ∈ lvars_bv D)) as [Hk|Hk].
  - split; intros [Hscope Hex]; split; [exact Hscope | | exact Hscope |].
    + destruct Hex as [m0 [Hscope0 [HP Hle]]].
      exists m0. split; [exact Hscope0 |]. split; [| exact Hle].
      destruct HP as [Hdom [σw [Hw Hp]]].
      assert (Hxv :
        ∃ v, store_restrict ρ
          (lvars_fv (lvars_open 0 y (lvars_open (S k) x D))) !! x = Some v).
      {
        eapply bstore_of_env_insert_dom_requires_value; eauto.
      }
      destruct Hxv as [v Hv].
      split.
      * apply (proj1 (bstore_of_env_insert_dom_open (<[0:=y]> ∅)
          (store_restrict ρ
            (lvars_fv (lvars_open 0 y (lvars_open (S k) x D))))
          (S k) x v D Hv)).
        exact Hdom.
      * exists σw. split; [exact Hw |].
        exists v. split.
        { rewrite store_restrict_lookup.
          destruct (decide (x ∈ lvars_fv (lvars_open (S k) x D))) as [_|Hnot].
          - exact Hv.
          - rewrite lvars_fv_open_has_bv in Hnot by exact Hk. set_solver. }
        denot_lvars_norm.
        rewrite (store_restrict_open_old 0 y (lvars_open (S k) x D) ρ).
        rewrite (store_restrict_open_old (S k) x D ρ).
        rewrite (store_restrict_open_old (S k) x D σw).
        rewrite map_restrict_insert_open_bv by exact Hk.
        rewrite <- (bstore_of_env_insert_restrict_some (<[0:=y]> ∅)
          (store_restrict ρ
            (lvars_fv (lvars_open 0 y (lvars_open (S k) x D))))
          (S k) x v (lvars_bv D)) by exact Hv.
        rewrite (store_restrict_open2_old (S k) x 0 y D ρ) in Hp.
        exact Hp.
    + destruct Hex as [m0 [Hscope0 [HP Hle]]].
      exists m0. split; [exact Hscope0 |]. split; [| exact Hle].
      destruct HP as [Hdom [σw [Hw [v [Hv Hp]]]]].
      assert (Hv0 :
        store_restrict ρ (lvars_fv (lvars_open 0 y (lvars_open (S k) x D)))
        !! x = Some v).
      {
        rewrite store_restrict_lookup in Hv.
        destruct (decide (x ∈ lvars_fv (lvars_open (S k) x D))) as [_|Hnot].
        - exact Hv.
        - rewrite lvars_fv_open_has_bv in Hnot by exact Hk. set_solver.
      }
      split.
      * apply (proj2 (bstore_of_env_insert_dom_open (<[0:=y]> ∅)
          (store_restrict ρ
            (lvars_fv (lvars_open 0 y (lvars_open (S k) x D))))
          (S k) x v D Hv0)).
        exact Hdom.
      * exists σw. split; [exact Hw |].
        denot_lvars_norm.
        rewrite map_restrict_insert_open_bv in Hp by exact Hk.
        rewrite <- (bstore_of_env_insert_restrict_some (<[0:=y]> ∅)
          (store_restrict ρ
            (lvars_fv (lvars_open 0 y (lvars_open (S k) x D))))
          (S k) x v (lvars_bv D)) in Hp by exact Hv0.
        rewrite (store_restrict_open2_open_old (S k) x 0 y D ρ) in Hp.
        rewrite (store_restrict_open_old (S k) x D σw) in Hp.
        rewrite (store_restrict_open2_old (S k) x 0 y D ρ).
        exact Hp.
  - replace (lvars_open (S k) x D) with D by
      (symmetry; apply lvars_open_no_bv; exact Hk).
    split; intros [Hscope Hex]; split.
    + unfold formula_scoped_in_world in *.
      cbn [formula_open formula_fv stale stale_logic_qualifier lqual_dom
        lqual_open] in *.
      exact Hscope.
    + destruct Hex as [m0 [Hscope0 [HP Hle]]].
      exists m0. split.
      { unfold formula_scoped_in_world in *.
        cbn [formula_open formula_fv stale stale_logic_qualifier lqual_dom
          lqual_open] in *.
        exact Hscope0. }
      split; [| exact Hle].
      destruct HP as [Hdom [σw [Hw Hp]]].
      denot_lvars_norm.
      split.
      * apply (proj1 (bstore_of_env_insert_dom_absent (<[0:=y]> ∅)
          (store_restrict ρ (lvars_fv (lvars_open 0 y D)))
          (S k) x (lvars_bv D) Hk)).
        exact Hdom.
      * exists σw. split; [exact Hw |].
        rewrite <- (bstore_of_env_insert_restrict_absent (<[0:=y]> ∅)
          (store_restrict ρ (lvars_fv (lvars_open 0 y D)))
          (S k) x (lvars_bv D)) by exact Hk.
        exact Hp.
    + unfold formula_scoped_in_world in *.
      cbn [formula_open formula_fv stale stale_logic_qualifier lqual_dom
        lqual_open] in *.
      exact Hscope.
    + destruct Hex as [m0 [Hscope0 [HP Hle]]].
      exists m0. split.
      { unfold formula_scoped_in_world in *.
        cbn [formula_open formula_fv stale stale_logic_qualifier lqual_dom
          lqual_open] in *.
        exact Hscope0. }
      split; [| exact Hle].
      destruct HP as [Hdom [σw [Hw Hp]]].
      denot_lvars_norm.
      split.
      * apply (proj2 (bstore_of_env_insert_dom_absent (<[0:=y]> ∅)
          (store_restrict ρ (lvars_fv (lvars_open 0 y D)))
          (S k) x (lvars_bv D) Hk)).
        exact Hdom.
      * exists σw. split.
        { exact Hw. }
        rewrite <- (bstore_of_env_insert_restrict_absent (<[0:=y]> ∅)
          (store_restrict ρ (lvars_fv (lvars_open 0 y D)))
          (S k) x (lvars_bv D)) in Hp by exact Hk.
        exact Hp.
Qed.

Lemma formula_fv_open2_FResultQualifier_over_body k x y φ :
  formula_fv
    (formula_open 0 y
      (formula_open (S k) x
        (FFibVars (qual_vars φ ∖ {[LVBound 0]})
          (FOver (FTypeQualifier φ))))) =
  formula_fv
    (formula_open 0 y
      (FFibVars (qual_vars ({S k ~> x} φ) ∖ {[LVBound 0]})
        (FOver (FTypeQualifier ({S k ~> x} φ))))).
Proof.
  rewrite !formula_open_fibvars.
  rewrite !formula_open_over.
  cbn [formula_fv].
  rewrite lvars_open_succ_difference_bound0.
  rewrite qual_vars_open_atom.
  rewrite FTypeQualifier_open2_fv.
  rewrite FTypeQualifier_open_fv.
  reflexivity.
Qed.

Lemma formula_store_equiv_open2_FResultQualifier_over_body k x y φ :
  formula_store_equiv
    (formula_open 0 y
      (formula_open (S k) x
        (FFibVars (qual_vars φ ∖ {[LVBound 0]})
          (FOver (FTypeQualifier φ)))))
    (formula_open 0 y
      (FFibVars (qual_vars ({S k ~> x} φ) ∖ {[LVBound 0]})
        (FOver (FTypeQualifier ({S k ~> x} φ))))).
Proof.
  rewrite !formula_open_fibvars.
  rewrite !formula_open_over.
  eapply formula_store_equiv_fibvars.
  - rewrite lvars_open_succ_difference_bound0.
    rewrite qual_vars_open_atom.
    reflexivity.
  - cbn [formula_fv].
    rewrite FTypeQualifier_open2_fv.
    rewrite FTypeQualifier_open_fv.
    reflexivity.
  - eapply formula_store_equiv_over.
    + rewrite FTypeQualifier_open2_fv.
      rewrite FTypeQualifier_open_fv.
      reflexivity.
    + apply FTypeQualifier_open2_store_equiv.
Qed.

Lemma formula_fv_open2_FResultQualifier_under_body k x y φ :
  formula_fv
    (formula_open 0 y
      (formula_open (S k) x
        (FFibVars (qual_vars φ ∖ {[LVBound 0]})
          (FUnder (FTypeQualifier φ))))) =
  formula_fv
    (formula_open 0 y
      (FFibVars (qual_vars ({S k ~> x} φ) ∖ {[LVBound 0]})
        (FUnder (FTypeQualifier ({S k ~> x} φ))))).
Proof.
  rewrite !formula_open_fibvars.
  rewrite !formula_open_under.
  cbn [formula_fv].
  rewrite lvars_open_succ_difference_bound0.
  rewrite qual_vars_open_atom.
  rewrite FTypeQualifier_open2_fv.
  rewrite FTypeQualifier_open_fv.
  reflexivity.
Qed.

Lemma formula_store_equiv_open2_FResultQualifier_under_body k x y φ :
  formula_store_equiv
    (formula_open 0 y
      (formula_open (S k) x
        (FFibVars (qual_vars φ ∖ {[LVBound 0]})
          (FUnder (FTypeQualifier φ)))))
    (formula_open 0 y
      (FFibVars (qual_vars ({S k ~> x} φ) ∖ {[LVBound 0]})
        (FUnder (FTypeQualifier ({S k ~> x} φ))))).
Proof.
  rewrite !formula_open_fibvars.
  rewrite !formula_open_under.
  eapply formula_store_equiv_fibvars.
  - rewrite lvars_open_succ_difference_bound0.
    rewrite qual_vars_open_atom.
    reflexivity.
  - cbn [formula_fv].
    rewrite FTypeQualifier_open2_fv.
    rewrite FTypeQualifier_open_fv.
    reflexivity.
  - eapply formula_store_equiv_under.
    + rewrite FTypeQualifier_open2_fv.
      rewrite FTypeQualifier_open_fv.
      reflexivity.
    + apply FTypeQualifier_open2_store_equiv.
Qed.

Lemma formula_fv_open_FExprContIn k x Σ T e Q Q' :
  LVFree x ∉ dom Σ →
  formula_fv (formula_open (S k) x (Q (typed_lty_env_bind Σ T))) =
  formula_fv (Q' (typed_lty_env_bind ({k ~> x} Σ) T)) →
  formula_fv (formula_open k x (FExprContIn Σ T e Q)) =
  formula_fv (FExprContIn ({k ~> x} Σ) T ({k ~> x} e) Q').
Proof.
  intros Hfresh HQ.
  unfold FExprContIn.
  rewrite formula_open_forall.
  cbn [formula_fv].
  rewrite formula_open_FExprContBody_under by exact Hfresh.
  unfold FExprContBody, FForallTypedBody.
  cbn [formula_fv].
  rewrite formula_open_impl.
  rewrite formula_open_FExprResultAtLvar_typed_under by exact Hfresh.
  cbn [formula_fv].
  rewrite HQ.
  reflexivity.
Qed.

Lemma formula_store_equiv_open_FExprContIn k x Σ T e Q Q' :
  LVFree x ∉ dom Σ →
  formula_fv (formula_open (S k) x (Q (typed_lty_env_bind Σ T))) =
  formula_fv (Q' (typed_lty_env_bind ({k ~> x} Σ) T)) →
  (∀ y,
    LVFree y ∉ dom ({k ~> x} Σ) →
    formula_fv
      (formula_open 0 y
        (formula_open (S k) x (Q (typed_lty_env_bind Σ T)))) =
    formula_fv
      (formula_open 0 y
        (Q' (typed_lty_env_bind ({k ~> x} Σ) T)))) →
  (∀ y,
    LVFree y ∉ dom ({k ~> x} Σ) →
    formula_store_equiv
      (formula_open 0 y
        (formula_open (S k) x (Q (typed_lty_env_bind Σ T))))
      (formula_open 0 y
        (Q' (typed_lty_env_bind ({k ~> x} Σ) T)))) →
  formula_store_equiv
    (formula_open k x (FExprContIn Σ T e Q))
    (FExprContIn ({k ~> x} Σ) T ({k ~> x} e) Q').
Proof.
  intros Hfresh HQfv Hopen_fv Hopen_eq.
  unfold FExprContIn.
  rewrite formula_open_forall.
  eapply (formula_store_equiv_forall_fresh (lvars_fv (dom ({k ~> x} Σ)))).
  - rewrite formula_open_FExprContBody_under by exact Hfresh.
    unfold FExprContBody, FForallTypedBody.
    cbn [formula_fv].
    rewrite formula_open_impl.
    rewrite formula_open_FExprResultAtLvar_typed_under by exact Hfresh.
    cbn [formula_fv].
    rewrite HQfv.
    reflexivity.
  - intros y Hy.
    assert (HyΣ : LVFree y ∉ dom ({k ~> x} Σ)).
    { intros Hbad. apply Hy. apply lvars_fv_elem. exact Hbad. }
    rewrite formula_open_FExprContBody_under by exact Hfresh.
    unfold FExprContBody, FForallTypedBody.
    rewrite formula_open_impl.
    rewrite formula_open_impl.
    rewrite formula_open_FExprResultAtLvar_typed_under by exact Hfresh.
    eapply formula_store_equiv_impl.
    + reflexivity.
    + rewrite formula_open_impl.
      cbn [formula_fv].
      rewrite Hopen_fv by exact HyΣ.
      reflexivity.
    + apply formula_store_equiv_refl.
    + rewrite formula_open_impl.
      eapply formula_store_equiv_impl.
      * reflexivity.
      * apply Hopen_fv. exact HyΣ.
      * apply formula_store_equiv_refl.
	      * apply Hopen_eq. exact HyΣ.
Qed.

Lemma formula_store_equiv_FExprContIn Σ T e Q Q' :
  formula_fv (Q (typed_lty_env_bind Σ T)) =
  formula_fv (Q' (typed_lty_env_bind Σ T)) →
  (∀ y,
    LVFree y ∉ dom Σ →
    formula_fv (formula_open 0 y (Q (typed_lty_env_bind Σ T))) =
    formula_fv (formula_open 0 y (Q' (typed_lty_env_bind Σ T)))) →
  (∀ y,
    LVFree y ∉ dom Σ →
    formula_store_equiv
      (formula_open 0 y (Q (typed_lty_env_bind Σ T)))
      (formula_open 0 y (Q' (typed_lty_env_bind Σ T)))) →
  formula_store_equiv (FExprContIn Σ T e Q) (FExprContIn Σ T e Q').
Proof.
  intros HQfv Hopen_fv Hopen_eq.
  unfold FExprContIn.
  eapply (formula_store_equiv_forall_fresh (lvars_fv (dom Σ))).
  - unfold FExprContBody, FForallTypedBody.
    cbn [formula_fv].
    rewrite HQfv. reflexivity.
  - intros y Hy.
    assert (HyΣ : LVFree y ∉ dom Σ).
    { intros Hbad. apply Hy. apply lvars_fv_elem. exact Hbad. }
	    unfold FExprContBody, FForallTypedBody.
	    rewrite formula_open_impl.
	    rewrite formula_open_impl.
	    eapply formula_store_equiv_impl.
	    + reflexivity.
	    + cbn [formula_fv]. rewrite Hopen_fv by exact HyΣ. reflexivity.
	    + apply formula_store_equiv_refl.
	    + eapply formula_store_equiv_impl.
	      * reflexivity.
		      * apply Hopen_fv. exact HyΣ.
		      * apply formula_store_equiv_refl.
	      * apply Hopen_eq. exact HyΣ.
Qed.

Lemma formula_open_FExprContBody_atom_env_const_branch
    (Σ : gmap atom ty) T e Q y :
  y ∉ dom Σ →
  lc_tm e →
  formula_open 0 y
    (FExprContBody (atom_env_to_lty_env Σ) T e (fun _ => Q)) =
  FImpl
    (FClosedResourceIn (atom_env_to_lty_env (<[y := T]> Σ)))
    (FImpl
      (FExprResultAt (dom Σ) e y)
      (formula_open 0 y Q)).
Proof.
  intros Hy Hlc.
  unfold FExprContBody, FForallTypedBody, typed_lty_env_bind.
  rewrite formula_open_impl.
  rewrite formula_open_FClosedResourceIn.
  rewrite lty_env_open_one_bind_atom_env by exact Hy.
  rewrite formula_open_impl.
  rewrite lty_env_shift_atom_env.
  rewrite lty_env_bind_atom_env_dom.
  rewrite formula_open_FExprResultOn_atom_env by eauto.
  reflexivity.
Qed.

Lemma formula_open_FExprContIn_atom_env_const
    k x (Σ : gmap atom ty) T e Q :
  formula_open k x
    (FExprContIn (atom_env_to_lty_env Σ) T e (fun _ => Q)) =
  FForall
    (formula_open (S k) x
      (FExprContBody (atom_env_to_lty_env Σ) T e (fun _ => Q))).
Proof.
  reflexivity.
Qed.

Lemma formula_open_FExprContIn_antecedent_atom_env
    (Σ : gmap atom ty) e y Q :
  y ∉ dom Σ →
  lc_tm e →
  formula_open 0 y
    (FImpl
      (FExprResultAtLvar
        (lvars_shift (lvars_of_atoms (dom Σ)) ∪ {[LVBound 0]})
        (tm_shift 0 e) (LVBound 0)) Q) =
  FImpl (FExprResultAt (dom Σ) e y) (formula_open 0 y Q).
Proof.
  intros Hy Hlc.
  cbn [formula_open].
  rewrite formula_open_FExprResultOn_atom_env by eauto.
  reflexivity.
Qed.

Lemma FExprContIn_formula_fv_subset
    (Σ : gmap atom ty) T e (S : aset) Q :
  dom Σ ⊆ S →
  formula_fv Q ⊆ S →
  formula_fv (FExprContIn (atom_env_to_lty_env Σ) T e (fun _ => Q)) ⊆ S.
Proof.
  intros HΣ HQ.
  unfold FExprContIn, FExprContBody, FForallTypedBody,
    FClosedResourceIn, FExprResultAtLvar, typed_lty_env_bind.
  cbn [formula_fv stale stale_formula stale_logic_qualifier lqual_dom].
  rewrite lty_env_shift_atom_env.
  rewrite !lty_env_bind_atom_env_dom.
  rewrite !formula_fv_FStoreResourceAtom_lvars.
  pose proof (lvars_fv_difference_subset
    (lvars_shift (lvars_of_atoms (dom Σ)) ∪ {[LVBound 0]})
    ({[LVBound 0]} : lvset)).
  rewrite lvars_fv_union, lvars_fv_shift, lvars_fv_of_atoms,
    lvars_fv_singleton_bound in H.
  rewrite ?lvars_fv_union.
  rewrite ?lvars_fv_shift, ?lvars_fv_of_atoms, ?lvars_fv_singleton_bound.
  set_solver.
Qed.

Lemma typed_lty_env_bind_open_env_lift_atom_dom η Σ T :
  lty_env_atom_dom
    (lty_env_open_lvars (open_env_lift η) (typed_lty_env_bind Σ T)) =
  lty_env_atom_dom (lty_env_open_lvars η Σ).
Proof.
  unfold lty_env_atom_dom.
  rewrite !lty_env_open_lvars_dom.
  rewrite !lvars_open_env_simul_eq.
  rewrite typed_lty_env_bind_dom.
  rewrite lvars_open_env_lift_shift_bind.
  rewrite lvars_fv_union, lvars_fv_shift, lvars_fv_singleton_bound.
  set_solver.
Qed.

Lemma open_env_lift_delete η k :
  delete (S k) (open_env_lift η) = open_env_lift (delete k η).
Proof.
  apply map_eq. intros [|j].
  - rewrite lookup_delete_ne by lia.
    rewrite !open_env_lift_lookup_zero_none. reflexivity.
  - destruct (decide (j = k)) as [->|Hjk].
    + rewrite lookup_delete_eq.
      symmetry.
      unfold open_env_lift.
      rewrite (lookup_kmap (M1:=gmap nat) (M2:=gmap nat)
        S (Inj0:=ltac:(intros ? ? ?; lia)) (A:=atom)).
      apply lookup_delete_eq.
    + rewrite lookup_delete_ne by lia.
      change (open_env_lift η !! S j =
        open_env_lift (delete k η) !! S j).
      unfold open_env_lift.
      rewrite !(lookup_kmap (M1:=gmap nat) (M2:=gmap nat)
        S (Inj0:=ltac:(intros ? ? ?; lia)) (A:=atom)).
      rewrite lookup_delete_ne by congruence. reflexivity.
Qed.

Lemma open_env_fresh_for_lvars_lift_typed_bind η Σ T :
  open_env_fresh_for_lvars η (dom Σ) →
  open_env_fresh_for_lvars (open_env_lift η)
    (dom (typed_lty_env_bind Σ T)).
Proof.
  intros Hfresh [|k] x Hkx Hbad.
  - rewrite open_env_lift_lookup_zero_none in Hkx. discriminate.
  - unfold open_env_lift in Hkx.
    apply (lookup_kmap_Some (M1:=gmap nat) (M2:=gmap nat)
      S (Inj0:=ltac:(intros ? ? ?; lia)) (A:=atom)) in Hkx
      as [j [Hj Hη]].
    inversion Hj. subst j.
    eapply Hfresh; [exact Hη|].
    rewrite open_env_lift_delete in Hbad.
    rewrite typed_lty_env_bind_dom in Hbad.
    rewrite lvars_open_env_lift_shift_bind in Hbad.
    rewrite lvars_fv_union, lvars_fv_shift, lvars_fv_singleton_bound in Hbad.
    set_solver.
Qed.

Lemma typed_lty_env_bind_open_env_lift η Σ T :
  open_env_fresh_for_lvars η (dom Σ) →
  lty_env_open_lvars (open_env_lift η) (typed_lty_env_bind Σ T) =
  typed_lty_env_bind (lty_env_open_lvars η Σ) T.
Proof.
  revert Σ.
  refine (fin_maps.map_fold_ind
    (fun η => ∀ Σ,
      open_env_fresh_for_lvars η (dom Σ) →
      lty_env_open_lvars (open_env_lift η) (typed_lty_env_bind Σ T) =
      typed_lty_env_bind (lty_env_open_lvars η Σ) T) _ _ η).
  - intros Σ _. rewrite open_env_lift_empty, !lty_env_open_lvars_empty.
    reflexivity.
  - intros k x η' Hηk Hfold IH Σ Hfresh.
    rewrite open_env_lift_insert.
    assert (Htail : open_env_fresh_for_lvars η' (dom Σ)).
    { eapply open_env_fresh_for_lvars_insert_tail; [exact Hηk|exact Hfresh]. }
    assert (Hx : x ∉ lvars_fv (lvars_open_env η' (dom Σ))).
    { eapply open_env_fresh_for_lvars_insert_head; [exact Hηk|exact Hfresh]. }
    rewrite lty_env_open_lvars_insert_fresh.
    2:{ apply open_env_lift_lookup_none. exact Hηk. }
    2:{
      rewrite typed_lty_env_bind_dom.
      rewrite lvars_open_env_lift_shift_bind.
      rewrite lvars_fv_union, lvars_fv_shift, lvars_fv_singleton_bound.
      set_solver.
    }
    2:{ apply open_env_fresh_for_lvars_lift_typed_bind. exact Htail. }
    rewrite IH by exact Htail.
    rewrite typed_lty_env_bind_open_under.
    2:{
      intros Hbad. apply Hx.
      rewrite <- lvars_open_env_simul_eq.
      apply lvars_fv_elem.
      rewrite <- lty_env_open_lvars_dom.
      exact Hbad.
    }
    rewrite lty_env_open_lvars_insert_fresh by exact Hηk || exact Hx || exact Htail.
    reflexivity.
Qed.

Lemma typed_lty_env_bind_atom_dom Σ T :
  lty_env_atom_dom (typed_lty_env_bind Σ T) = lty_env_atom_dom Σ.
Proof.
  unfold lty_env_atom_dom.
  apply typed_lty_env_bind_lvars_fv_dom.
Qed.

Lemma formula_fv_open_env_FForallTypedBind η Σ T Q Q' :
  formula_fv
    (formula_open_env (open_env_lift η) (Q (typed_lty_env_bind Σ T))) =
  formula_fv (Q' (typed_lty_env_bind (lty_env_open_lvars η Σ) T)) →
  formula_fv (formula_open_env η (FForallTypedBind Σ T Q)) =
  formula_fv (FForallTypedBind (lty_env_open_lvars η Σ) T Q').
Proof.
  intros HQ.
  unfold FForallTypedBind.
  rewrite formula_open_env_forall.
  cbn [formula_fv].
  unfold FForallTypedBody.
  rewrite formula_open_env_impl.
  cbn [formula_fv].
  assert (Hclosed :
    formula_fv
      (formula_open_env (open_env_lift η)
        (FClosedResourceIn (typed_lty_env_bind Σ T))) =
    formula_fv
      (FClosedResourceIn
        (typed_lty_env_bind (lty_env_open_lvars η Σ) T))).
  {
    unfold FClosedResourceIn.
    rewrite formula_open_env_FStoreResourceAtom_lvars.
    rewrite !formula_fv_FStoreResourceAtom_lvars.
    rewrite <- lvars_open_env_simul_eq.
    rewrite <- lty_env_open_lvars_dom.
    change (lty_env_atom_dom
      (lty_env_open_lvars (open_env_lift η) (typed_lty_env_bind Σ T)) =
    lty_env_atom_dom
      (typed_lty_env_bind (lty_env_open_lvars η Σ) T)).
    rewrite typed_lty_env_bind_open_env_lift_atom_dom.
    rewrite typed_lty_env_bind_atom_dom.
    reflexivity.
  }
  rewrite Hclosed, HQ.
  reflexivity.
Qed.

Lemma formula_store_equiv_open_env_FForallTypedBind η Σ T Q Q' :
  open_env_fresh_for_lvars η (dom Σ) →
  (∀ y,
    LVFree y ∉ dom (lty_env_open_lvars η Σ) →
    formula_store_iso
      (formula_open 0 y
        (formula_open_env (open_env_lift η)
          (Q (typed_lty_env_bind Σ T))))
      (formula_open 0 y
        (Q' (typed_lty_env_bind (lty_env_open_lvars η Σ) T)))) →
  formula_store_equiv
    (formula_open_env η (FForallTypedBind Σ T Q))
    (FForallTypedBind (lty_env_open_lvars η Σ) T Q').
Proof.
  intros Hfresh Hopen_iso.
  pose proof (formula_fv_eq_of_open_fresh
    (lvars_fv (dom (lty_env_open_lvars η Σ)))
    (formula_open_env (open_env_lift η) (Q (typed_lty_env_bind Σ T)))
    (Q' (typed_lty_env_bind (lty_env_open_lvars η Σ) T))) as Hfv_of_open.
  assert (HQfv :
    formula_fv
      (formula_open_env (open_env_lift η) (Q (typed_lty_env_bind Σ T))) =
    formula_fv (Q' (typed_lty_env_bind (lty_env_open_lvars η Σ) T))).
  {
    apply Hfv_of_open. intros y Hy.
    apply formula_store_iso_fv.
    apply Hopen_iso.
    intros Hbad. apply Hy. apply lvars_fv_elem. exact Hbad.
  }
  clear Hfv_of_open.
  unfold FForallTypedBind.
  rewrite formula_open_env_forall.
  eapply (formula_store_equiv_forall_fresh
    (lvars_fv (dom (lty_env_open_lvars η Σ)))).
  - unfold FForallTypedBody.
    rewrite formula_open_env_impl.
    cbn [formula_fv].
    rewrite formula_fv_open_env_FClosedResourceIn.
    rewrite typed_lty_env_bind_open_env_lift by exact Hfresh.
    rewrite HQfv.
    reflexivity.
  - intros y Hy.
    assert (HyΣ : LVFree y ∉ dom (lty_env_open_lvars η Σ)).
    { intros Hbad. apply Hy. apply lvars_fv_elem. exact Hbad. }
    destruct (Hopen_iso y HyΣ) as [Hopen_fv Hopen_eq].
    unfold FForallTypedBody.
    rewrite formula_open_env_impl.
    rewrite !formula_open_impl.
    eapply formula_store_equiv_impl.
    + rewrite formula_open_env_FClosedResourceIn.
      rewrite typed_lty_env_bind_open_env_lift by exact Hfresh.
      rewrite !formula_fv_open_FClosedResourceIn.
      reflexivity.
    + exact Hopen_fv.
    + rewrite formula_open_env_FClosedResourceIn.
      rewrite typed_lty_env_bind_open_env_lift by exact Hfresh.
      apply formula_store_equiv_refl.
    + exact Hopen_eq.
Qed.

Lemma formula_fv_FImpl (φ ψ : FQ) :
  formula_fv (FImpl φ ψ) = formula_fv φ ∪ formula_fv ψ.
Proof. reflexivity. Qed.

Lemma formula_fv_FWand (φ ψ : FQ) :
  formula_fv (FWand φ ψ) = formula_fv φ ∪ formula_fv ψ.
Proof. reflexivity. Qed.

Lemma FExprResultAtLvar_open_env_fv η L e ν :
  formula_fv (formula_open_env η (FExprResultAtLvar L e ν)) =
  lvars_fv (lvars_open_env η L).
Proof.
  unfold FExprResultAtLvar.
  rewrite formula_open_env_fibvars.
  rewrite formula_open_env_FStoreResourceAtom_lvars.
  cbn [formula_fv].
  pose proof (lvars_fv_mono _ _
    (lvars_open_env_mono η (L ∖ {[ν]}) L ltac:(set_solver))) as Hsub.
  set_solver.
Qed.

Lemma lvars_shift_union_bound0_difference D :
  (lvars_shift D ∪ {[LVBound 0]}) ∖ {[LVBound 0]} =
  lvars_shift D.
Proof.
  apply set_eq. intros v.
  rewrite elem_of_difference, elem_of_union.
  split.
  - intros [[Hv|Hv] Hnot]; [exact Hv|].
    exfalso. apply Hnot. exact Hv.
  - intros Hv. split; [left; exact Hv|].
    intros H0. apply elem_of_singleton in H0. subst v.
    unfold lvars_shift in Hv.
    apply elem_of_map in Hv as [u [Hu _]].
    destruct u as [k|y]; cbn [logic_var_shift] in Hu; inversion Hu.
Qed.

Lemma typed_lty_env_bind_open_env_lift_dom_difference_bound0 η Σ T :
  lvars_open_env (open_env_lift η)
    (dom (typed_lty_env_bind Σ T) ∖ {[LVBound 0]}) =
  dom (typed_lty_env_bind (lty_env_open_lvars η Σ) T) ∖ {[LVBound 0]}.
Proof.
  rewrite !typed_lty_env_bind_dom.
  rewrite lvars_shift_union_bound0_difference.
  rewrite lvars_open_env_lift_shift.
  rewrite lty_env_open_lvars_dom.
  rewrite lvars_open_env_simul_eq.
  rewrite lvars_shift_union_bound0_difference.
  reflexivity.
Qed.

Lemma formula_open_env_FExprResultAtLvar_typed_under η Σ T e :
  open_env_fresh_for_lvars η (dom Σ) →
  formula_open_env (open_env_lift η)
    (FExprResultAtLvar (dom (typed_lty_env_bind Σ T))
      (↑[0] e) (LVBound 0)) =
  FExprResultAtLvar
    (dom (typed_lty_env_bind (lty_env_open_lvars η Σ) T))
    (↑[0] (open_tm_env η e)) (LVBound 0).
Proof.
  intros Hfresh.
  unfold FExprResultAtLvar.
  rewrite formula_open_env_fibvars.
  rewrite formula_open_env_FStoreResourceAtom_lvars.
  rewrite typed_lty_env_bind_open_env_lift_dom_difference_bound0.
  replace (lvars_open_env (open_env_lift η)
    (dom (typed_lty_env_bind Σ T))) with
    (dom (typed_lty_env_bind (lty_env_open_lvars η Σ) T)).
  2:{
    rewrite <- lvars_open_env_simul_eq.
    rewrite <- lty_env_open_lvars_dom.
    rewrite typed_lty_env_bind_open_env_lift by exact Hfresh.
    reflexivity.
  }
  f_equal.
  apply FStoreResourceAtom_ext.
  - reflexivity.
  - intros ξ σ m.
    cbn [logic_var_to_atom].
    unfold open_env_precompose.
    rewrite lookup_union_r by apply open_env_lift_lookup_zero_none.
    destruct (ξ !! 0) as [y|]; [|reflexivity].
    fold (open_env_precompose (open_env_lift η) ξ).
    f_equiv.
    + f_equal.
      rewrite <- lvars_to_atoms_open_env.
      rewrite typed_lty_env_bind_open_env_lift_dom_difference_bound0.
      reflexivity.
    + rewrite <- open_tm_env_lift_shift0.
      rewrite open_tm_env_precompose. reflexivity.
Qed.

Lemma formula_store_equiv_open_env_FExprContIn η Σ T e Q Q' :
  open_env_fresh_for_lvars η (dom Σ) →
  (∀ y,
    LVFree y ∉ dom (lty_env_open_lvars η Σ) →
    formula_store_iso
      (formula_open 0 y
        (formula_open_env (open_env_lift η)
          (Q (typed_lty_env_bind Σ T))))
      (formula_open 0 y
        (Q' (typed_lty_env_bind (lty_env_open_lvars η Σ) T)))) →
  formula_store_equiv
    (formula_open_env η (FExprContIn Σ T e Q))
    (FExprContIn (lty_env_open_lvars η Σ) T (open_tm_env η e) Q').
Proof.
  intros Hfresh Hopen_iso.
  pose proof (formula_fv_eq_of_open_fresh
    (lvars_fv (dom (lty_env_open_lvars η Σ)))
    (formula_open_env (open_env_lift η) (Q (typed_lty_env_bind Σ T)))
    (Q' (typed_lty_env_bind (lty_env_open_lvars η Σ) T))) as Hfv_of_open.
  assert (HQfv :
    formula_fv
      (formula_open_env (open_env_lift η) (Q (typed_lty_env_bind Σ T))) =
    formula_fv (Q' (typed_lty_env_bind (lty_env_open_lvars η Σ) T))).
  {
    apply Hfv_of_open. intros y Hy.
    apply formula_store_iso_fv.
    apply Hopen_iso.
    intros Hbad. apply Hy. apply lvars_fv_elem. exact Hbad.
  }
  clear Hfv_of_open.
  unfold FExprContIn.
  rewrite formula_open_env_forall.
  eapply (formula_store_equiv_forall_fresh
    (lvars_fv (dom (lty_env_open_lvars η Σ)))).
  - unfold FExprContBody, FForallTypedBody.
    rewrite formula_open_env_impl.
    rewrite formula_open_env_impl.
    cbn [formula_fv].
    rewrite formula_fv_open_env_FClosedResourceIn.
    rewrite typed_lty_env_bind_open_env_lift by exact Hfresh.
    rewrite formula_open_env_FExprResultAtLvar_typed_under by exact Hfresh.
    cbn [formula_fv].
    rewrite HQfv.
    reflexivity.
  - intros y Hy.
    assert (HyΣ : LVFree y ∉ dom (lty_env_open_lvars η Σ)).
    { intros Hbad. apply Hy. apply lvars_fv_elem. exact Hbad. }
    destruct (Hopen_iso y HyΣ) as [Hopen_fv Hopen_eq].
    unfold FExprContBody, FForallTypedBody.
    rewrite formula_open_env_impl.
    rewrite formula_open_env_impl.
    rewrite !formula_open_impl.
    eapply formula_store_equiv_impl.
    + rewrite formula_open_env_FClosedResourceIn.
      rewrite typed_lty_env_bind_open_env_lift by exact Hfresh.
      rewrite !formula_fv_open_FClosedResourceIn.
      reflexivity.
    + cbn [formula_fv].
      rewrite formula_open_env_FExprResultAtLvar_typed_under by exact Hfresh.
      rewrite Hopen_fv.
      reflexivity.
    + rewrite formula_open_env_FClosedResourceIn.
      rewrite typed_lty_env_bind_open_env_lift by exact Hfresh.
      apply formula_store_equiv_refl.
    + eapply formula_store_equiv_impl.
      * rewrite formula_open_env_FExprResultAtLvar_typed_under by exact Hfresh.
        reflexivity.
      * exact Hopen_fv.
      * rewrite formula_open_env_FExprResultAtLvar_typed_under by exact Hfresh.
        apply formula_store_equiv_refl.
      * exact Hopen_eq.
Qed.

Lemma FTypeQualifier_open_env_fv η φ :
  formula_fv (formula_open_env η (FTypeQualifier φ)) =
  lvars_fv (lvars_open_env η (qual_vars φ)).
Proof.
  destruct φ as [D p].
  unfold FTypeQualifier, qual_vars.
  rewrite formula_open_env_FStoreResourceAtom_lvars.
  apply formula_fv_FStoreResourceAtom_lvars.
Qed.

Lemma formula_fv_open_env_FExprContIn η Σ T e Q Q' :
  formula_fv
    (formula_open_env (open_env_lift η) (Q (typed_lty_env_bind Σ T))) =
  formula_fv (Q' (typed_lty_env_bind (lty_env_open_lvars η Σ) T)) →
  formula_fv (formula_open_env η (FExprContIn Σ T e Q)) =
  formula_fv
    (FExprContIn (lty_env_open_lvars η Σ) T (open_tm_env η e) Q').
Proof.
  intros HQ.
  unfold FExprContIn.
  rewrite formula_open_env_forall.
  cbn [formula_fv].
  unfold FExprContBody, FForallTypedBody.
  rewrite formula_open_env_impl.
  rewrite formula_open_env_impl.
  cbn [formula_fv].
  assert (Hclosed :
    formula_fv
      (formula_open_env (open_env_lift η)
        (FClosedResourceIn (typed_lty_env_bind Σ T))) =
    formula_fv
      (FClosedResourceIn
        (typed_lty_env_bind (lty_env_open_lvars η Σ) T))).
  {
    unfold FClosedResourceIn.
    rewrite formula_open_env_FStoreResourceAtom_lvars.
    rewrite !formula_fv_FStoreResourceAtom_lvars.
    rewrite <- lvars_open_env_simul_eq.
    rewrite <- lty_env_open_lvars_dom.
    change (lty_env_atom_dom
      (lty_env_open_lvars (open_env_lift η) (typed_lty_env_bind Σ T)) =
    lty_env_atom_dom
      (typed_lty_env_bind (lty_env_open_lvars η Σ) T)).
    rewrite typed_lty_env_bind_open_env_lift_atom_dom.
    rewrite typed_lty_env_bind_atom_dom.
    reflexivity.
  }
  assert (Hresult :
    formula_fv
      (formula_open_env (open_env_lift η)
        (FExprResultAtLvar (dom (typed_lty_env_bind Σ T))
          (↑[0] e) (LVBound 0))) =
    formula_fv
      (FExprResultAtLvar
        (dom (typed_lty_env_bind (lty_env_open_lvars η Σ) T))
        (↑[0] (open_tm_env η e)) (LVBound 0))).
  {
    rewrite FExprResultAtLvar_open_env_fv.
    rewrite FExprResultAtLvar_fv.
    rewrite <- lvars_open_env_simul_eq.
    rewrite <- lty_env_open_lvars_dom.
    change (lty_env_atom_dom
      (lty_env_open_lvars (open_env_lift η) (typed_lty_env_bind Σ T)) =
    lty_env_atom_dom
      (typed_lty_env_bind (lty_env_open_lvars η Σ) T)).
    rewrite typed_lty_env_bind_open_env_lift_atom_dom.
    rewrite typed_lty_env_bind_atom_dom.
    reflexivity.
  }
  rewrite Hclosed, Hresult, HQ.
  reflexivity.
Qed.

Lemma typed_lty_env_bind_atom_fresh x Σ T :
  x ∉ lty_env_atom_dom Σ →
  x ∉ lty_env_atom_dom (typed_lty_env_bind Σ T).
Proof.
  rewrite typed_lty_env_bind_atom_dom. auto.
Qed.

Lemma typed_lty_env_bind_bvar_fresh_under k Σ T :
  k ∉ lvars_bv (dom Σ) →
  S k ∉ lvars_bv (dom (typed_lty_env_bind Σ T)).
Proof.
  intros Hfresh Hbad.
  apply lvars_bv_elem in Hbad.
  unfold typed_lty_env_bind in Hbad.
  change (LVBound (S k) ∈
    dom (<[LVBound 0 := T]> (lty_env_shift Σ) : lty_env)) in Hbad.
  apply elem_of_dom in Hbad as [U Hlookup].
  change ((<[LVBound 0 := T]> (lty_env_shift Σ) : lty_env) !!
    LVBound (S k) = Some U) in Hlookup.
  rewrite (lookup_insert_ne (lty_env_shift Σ) (LVBound 0)
    (LVBound (S k)) T) in Hlookup by discriminate.
  change ((kmap logic_var_shift Σ : lty_env) !!
    LVBound (S k) = Some U) in Hlookup.
  apply lookup_kmap_Some in Hlookup as [v [Hv Hlookup]].
  2:{ apply logic_var_shift_inj. }
  destruct v as [j|y]; cbn [logic_var_shift] in Hv.
  - inversion Hv; subst.
    apply Hfresh. apply lvars_bv_elem.
    apply elem_of_dom. exists U. exact Hlookup.
  - inversion Hv.
Qed.

Lemma typed_lty_env_bind_open_under_atom_dom k x Σ T :
  LVFree x ∉ dom Σ →
  lty_env_atom_dom ({S k ~> x} (typed_lty_env_bind Σ T)) =
  lty_env_atom_dom (typed_lty_env_bind ({k ~> x} Σ) T).
Proof.
  intros Hfresh.
  rewrite typed_lty_env_bind_open_under by exact Hfresh.
  reflexivity.
Qed.

Lemma FForallTypedBody_lvar_formula_fv_subset Σ T (S : aset) Q :
  lvars_fv (dom Σ) ⊆ S →
  formula_fv (Q (typed_lty_env_bind Σ T)) ⊆ S →
  formula_fv (FForallTypedBody Σ T Q) ⊆ S.
Proof.
  intros HΣ HQ.
  unfold FForallTypedBody, FClosedResourceIn.
  cbn [formula_fv stale stale_formula stale_logic_qualifier lqual_dom].
  rewrite formula_fv_FStoreResourceAtom_lvars.
  rewrite typed_lty_env_bind_lvars_fv_dom.
  set_solver.
Qed.

Lemma FForallTypedBind_lvar_formula_fv_subset Σ T (S : aset) Q :
  lvars_fv (dom Σ) ⊆ S →
  formula_fv (Q (typed_lty_env_bind Σ T)) ⊆ S →
  formula_fv (FForallTypedBind Σ T Q) ⊆ S.
Proof.
  intros HΣ HQ.
  unfold FForallTypedBind, FForallTypedBody, FClosedResourceIn.
  cbn [formula_fv stale stale_formula stale_logic_qualifier lqual_dom].
  rewrite formula_fv_FStoreResourceAtom_lvars.
  rewrite typed_lty_env_bind_lvars_fv_dom.
  set_solver.
Qed.

Lemma FExprContIn_lvar_formula_fv_subset Σ T e (S : aset) Q :
  lvars_fv (dom Σ) ⊆ S →
  formula_fv (Q (typed_lty_env_bind Σ T)) ⊆ S →
  formula_fv (FExprContIn Σ T e Q) ⊆ S.
Proof.
  intros HΣ HQ.
  unfold FExprContIn, FExprContBody, FForallTypedBody,
    FClosedResourceIn.
  cbn [formula_fv stale stale_formula stale_logic_qualifier lqual_dom].
  rewrite formula_fv_FStoreResourceAtom_lvars.
  rewrite FExprResultAtLvar_fv.
  rewrite !typed_lty_env_bind_lvars_fv_dom.
  set_solver.
Qed.
