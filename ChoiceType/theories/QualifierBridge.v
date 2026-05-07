(** * ChoiceType.QualifierBridge

    Bridges from type-level shallow qualifiers to Choice Logic atoms.

    The raw [type_qualifier] syntax and its local operations live in
    [Qualifier].  This file contains the denotational lift that depends on the
    Choice Logic world structure. *)

From ChoiceType Require Export Qualifier.

(** Lift a type-level store predicate into a logic atom.

    Logic denotation restricts the world to the qualifier domain before this
    predicate is called, so the singleton requirement applies to the relevant
    world fragment. *)
Definition lift_type_qualifier_to_logic (q : type_qualifier) : logic_qualifier :=
  match q with
  | qual B d p =>
      lqual d (fun σ (w : WfWorld) =>
        B = ∅ ∧ ∃ σw, (w : World) = singleton_world σw ∧ p ∅ σ σw)
  end.

Lemma lqual_dom_lift_type_qualifier_to_logic q :
  lqual_dom (lift_type_qualifier_to_logic q) = qual_dom q.
Proof. destruct q; reflexivity. Qed.
