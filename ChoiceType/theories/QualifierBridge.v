(** * ChoiceType.QualifierBridge

    Bridges from type-level shallow qualifiers to Choice Logic atoms.

    The raw [type_qualifier] syntax and its local operations live in
    [Qualifier].  This file contains the denotational lift that depends on the
    Choice Logic world structure. *)

From ChoiceType Require Export Qualifier.
From ChoiceType Require Import QualifierProps.

Definition bstore_of_env (η : gmap nat atom) (σ : Store) : gmap nat value :=
  map_fold (λ k x β,
    match σ !! x with
    | Some v => <[k := v]> β
    | None => β
    end) ∅ η.

(** Formula-level lift of a type qualifier.

    A type qualifier is a shallow predicate over an explicit store and a
    singleton result-resource.  [FTypeQualifier] exposes that shape directly as
    a [FStoreResourceAtom], instead of first manufacturing an intermediate
    logic qualifier. *)
Definition FTypeQualifier (q : type_qualifier) : Formula :=
  match q with
  | qual D p =>
      FStoreResourceAtom D (fun η σ (w : WfWorld) =>
        let β := bstore_of_env η σ in
        lvars_bv D ⊆ dom β ∧
        ∃ σw, (w : World) = singleton_world σw ∧ p β σ σw)
  end.

Lemma formula_fv_FTypeQualifier q :
  formula_fv (FTypeQualifier q) = qual_dom q.
Proof.
  destruct q. unfold FTypeQualifier, FStoreResourceAtom. simpl.
  reflexivity.
Qed.
