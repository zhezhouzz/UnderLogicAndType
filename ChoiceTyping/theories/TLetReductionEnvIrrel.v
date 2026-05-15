(** * ChoiceTyping.TLetReductionEnvIrrel

    Fuel-level and model-level reduction lemmas for the [tlet] soundness case.
    The final semantic wrappers stay in [TLetDenotation]. *)

From CoreLang Require Import Instantiation InstantiationProps OperationalProps BasicTypingProps
  LocallyNamelessProps StrongNormalization Sugar.
From ChoiceTyping Require Import Naming ResultWorldBridge ResultWorldExprCont.
From ChoiceType Require Import BasicStore LocallyNamelessProps DenotationRefinement.

Import Tactics.

(** Environment irrelevance wrappers used by the fuel-level [tlet] proof. *)
Lemma denot_ty_fuel_drop_fresh_env_irrel gas
    (Σ : gmap atom ty) (τ : choice_ty) e x T (m : WfWorld) :
  cty_measure τ <= gas →
  x ∉ dom Σ ∪ fv_cty τ ∪ fv_tm e →
  world_dom (m : World) = dom (<[x := T]> Σ) →
  world_store_closed_on (dom (<[x := T]> Σ)) m →
  expr_total_on (dom (<[x := T]> Σ)) e m →
  m ⊨ denot_ty_fuel gas (<[x := T]> Σ) τ e →
  res_restrict m (dom Σ) ⊨ denot_ty_fuel gas Σ τ e.
Proof.
Admitted.

Lemma denot_ty_fuel_insert_fresh_env_irrel gas
    (Σ : gmap atom ty) (τ : choice_ty) e x T (m : WfWorld) :
  cty_measure τ <= gas →
  x ∉ dom Σ ∪ fv_cty τ ∪ fv_tm e →
  world_dom (m : World) = dom (<[x := T]> Σ) →
  world_store_closed_on (dom (<[x := T]> Σ)) m →
  expr_total_on (dom (<[x := T]> Σ)) e m →
  res_restrict m (dom Σ) ⊨ denot_ty_fuel gas Σ τ e →
  m ⊨ denot_ty_fuel gas (<[x := T]> Σ) τ e.
Admitted.

Lemma denot_ty_fuel_insert_fresh_env_irrel_iff gas
    (Σ : gmap atom ty) (τ : choice_ty) e x T (m : WfWorld) :
  cty_measure τ <= gas →
  x ∉ dom Σ ∪ fv_cty τ ∪ fv_tm e →
  world_dom (m : World) = dom (<[x := T]> Σ) →
  world_store_closed_on (dom (<[x := T]> Σ)) m →
  expr_total_on (dom (<[x := T]> Σ)) e m →
  m ⊨ denot_ty_fuel gas (<[x := T]> Σ) τ e <->
  res_restrict m (dom Σ) ⊨ denot_ty_fuel gas Σ τ e.
Proof.
  intros Hgas Hx Hdom Hclosed Htotal. split.
  - eapply denot_ty_fuel_drop_fresh_env_irrel; eauto.
  - eapply denot_ty_fuel_insert_fresh_env_irrel; eauto.
Qed.
