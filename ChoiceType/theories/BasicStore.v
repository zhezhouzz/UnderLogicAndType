(** * ChoiceType.BasicStore

    Basic well-typedness for stores and worlds.

    Choice-type denotations are semantic predicates over worlds, but their
    erased basic types must still constrain the values stored at tracked
    coordinates.  This file isolates that constraint from the refinement and
    resource definitions. *)

From CoreLang Require Import BasicTyping.
From ChoiceType Require Export Syntax.

(** [store_has_type_on Σ X σ] says that every coordinate in [X] whose basic
    type is recorded by [Σ] is occupied by a closed value of that type.  The
    relation is intentionally domain-limited: denotations can ask only for the
    coordinates they introduce or inspect. *)
Definition store_has_type_on
    (Σ : gmap atom ty) (X : aset) (σ : Store) : Prop :=
  ∀ x T v,
    x ∈ X →
    Σ !! x = Some T →
    σ !! x = Some v →
    ∅ ⊢ᵥ v ⋮ T.

Definition world_has_type_on
    (Σ : gmap atom ty) (X : aset) (w : WfWorld) : Prop :=
  ∀ σ, (w : World) σ → store_has_type_on Σ X σ.

Definition basic_world_lqual
    (Σ : gmap atom ty) (X : aset) : logic_qualifier :=
  lqual X (fun _ w => world_has_type_on Σ X w).

Definition basic_world_formula
    (Σ : gmap atom ty) (X : aset) : FormulaQ :=
  FAtom (basic_world_lqual Σ X).

Lemma store_has_type_on_mono Σ X Y σ :
  X ⊆ Y →
  store_has_type_on Σ Y σ →
  store_has_type_on Σ X σ.
Proof.
  intros HXY Htyped x T v Hx HΣ Hσ.
  eapply Htyped; eauto.
Qed.

Lemma world_has_type_on_mono Σ X Y w :
  X ⊆ Y →
  world_has_type_on Σ Y w →
  world_has_type_on Σ X w.
Proof.
  intros HXY Htyped σ Hσ.
  eapply store_has_type_on_mono; eauto.
Qed.

Lemma basic_world_formula_fv Σ X :
  formula_fv (basic_world_formula Σ X) = X.
Proof. reflexivity. Qed.

Lemma store_has_type_on_lookup Σ X σ x T v :
  store_has_type_on Σ X σ →
  x ∈ X →
  Σ !! x = Some T →
  σ !! x = Some v →
  ∅ ⊢ᵥ v ⋮ T.
Proof.
  intros Htyped Hx HΣ Hσ.
  eapply Htyped; eauto.
Qed.

Lemma store_has_type_on_insert_self Σ X σ x T v :
  store_has_type_on (<[x := T]> Σ) X σ →
  x ∈ X →
  σ !! x = Some v →
  ∅ ⊢ᵥ v ⋮ T.
Proof.
  intros Htyped Hx Hσ.
  exact (Htyped x T v Hx (lookup_insert_eq Σ x T) Hσ).
Qed.

Lemma world_has_type_on_lookup Σ X w σ x T v :
  world_has_type_on Σ X w →
  (w : World) σ →
  x ∈ X →
  Σ !! x = Some T →
  σ !! x = Some v →
  ∅ ⊢ᵥ v ⋮ T.
Proof.
  intros Htyped Hσ Hx HΣ Hlook.
  eapply store_has_type_on_lookup; eauto.
Qed.

Lemma world_has_type_on_insert_self Σ X w σ x T v :
  world_has_type_on (<[x := T]> Σ) X w →
  (w : World) σ →
  x ∈ X →
  σ !! x = Some v →
  ∅ ⊢ᵥ v ⋮ T.
Proof.
  intros Htyped Hσ Hx Hlook.
  eapply store_has_type_on_insert_self; eauto.
Qed.
