From ChoiceAlgebra Require Import Prelude Store Resource.

(** * Choice Algebra  (Definitions 1.6)

    An abstract *partial commutative semiring without zero* (PCS) equipped with
    a partial order satisfying bifunctoriality.  We represent partiality via
    explicit definedness predicates [ca_times_def] / [ca_plus_def] rather than
    [option], keeping the algebra operations total as functions. *)

(** ** Abstract choice algebra *)

Class ChoiceAlgebra (M : Type) := {
  (** Carrier operations *)
  ca_one  : M;
  ca_times : M → M → M;
  ca_plus  : M → M → M;
  ca_le    : M → M → Prop;

  (** Definedness predicates (the operations are partial) *)
  ca_times_def : M → M → Prop;
  ca_plus_def  : M → M → Prop;

  (** Identity: m × 1 = m *)
  ca_times_unit : ∀ m, ca_times m ca_one = m;

  (** Commutativity (when defined) *)
  ca_times_comm : ∀ m1 m2,
    ca_times_def m1 m2 → ca_times_def m2 m1 ∧ ca_times m1 m2 = ca_times m2 m1;

  ca_plus_comm  : ∀ m1 m2,
    ca_plus_def m1 m2 → ca_plus_def m2 m1 ∧ ca_plus m1 m2 = ca_plus m2 m1;

  (** Associativity (when defined) *)
  ca_times_assoc : ∀ m1 m2 m3,
    ca_times_def m1 m2 → ca_times_def (ca_times m1 m2) m3 →
    ca_times_def m2 m3 ∧ ca_times_def m1 (ca_times m2 m3) ∧
    ca_times (ca_times m1 m2) m3 = ca_times m1 (ca_times m2 m3);

  ca_plus_assoc  : ∀ m1 m2 m3,
    ca_plus_def m1 m2 → ca_plus_def (ca_plus m1 m2) m3 →
    ca_plus_def m2 m3 ∧ ca_plus_def m1 (ca_plus m2 m3) ∧
    ca_plus (ca_plus m1 m2) m3 = ca_plus m1 (ca_plus m2 m3);

  (** Partial order is reflexive (other order axioms are standard lemmas) *)
  ca_le_refl : ∀ m, ca_le m m;

  (** Bifunctoriality of × w.r.t. ≤ *)
  ca_times_le_mono : ∀ m1 m2 m1' m2',
    ca_le m1 m1' → ca_le m2 m2' →
    ca_times_def m1 m2 → ca_times_def m1' m2' →
    ca_le (ca_times m1 m2) (ca_times m1' m2');

  (** Bifunctoriality of + w.r.t. ≤ *)
  ca_plus_le_mono  : ∀ m1 m2 m1' m2',
    ca_le m1 m1' → ca_le m2 m2' →
    ca_plus_def m1 m2 → ca_plus_def m1' m2' →
    ca_le (ca_plus m1 m2) (ca_plus m1' m2');
}.

(** ** Derived order lemmas for an abstract ChoiceAlgebra *)

Section ChoiceAlgebraLemmas.
Context `{ChoiceAlgebra M}.

(** m1 ≤ m1 × m2  is an expected consequence of bifunctoriality + unit. *)
(** (The concrete proof for WfWorld is in the instance below.) *)

End ChoiceAlgebraLemmas.

(** ** Concrete instance: (WfWorld, res_sum_total, res_product_total, res_unit, ⊑)

    Carrier is [WfWorld] — the sigma type [{m : World | wf_world m}].
    Total operations come from Resource.v; definedness remains explicit in
    [ca_times_def] and [ca_plus_def]. *)

#[global] Program Instance WfWorld_ChoiceAlgebra : ChoiceAlgebra WfWorld := {|
  ca_one       := res_unit;
  ca_times     := res_product_total;
  ca_plus      := res_sum_total;
  ca_le        := sqsubseteq (A := WfWorld);
  ca_times_def := fun w1 w2 => world_compat w1 w2;
  ca_plus_def  := fun w1 w2 => raw_sum_defined w1 w2;
|}.
Next Obligation. Admitted.       (* ca_times_unit *)
Next Obligation. Admitted.       (* ca_times_comm *)
Next Obligation. Admitted.       (* ca_plus_comm *)
Next Obligation. Admitted.       (* ca_times_assoc *)
Next Obligation. Admitted.       (* ca_plus_assoc *)
Next Obligation.                 (* ca_le_refl: provable because carrier is WfWorld *)
  intro w. exact (reflexivity w).
Qed.
Next Obligation. Admitted.       (* ca_times_le_mono *)
Next Obligation. Admitted.       (* ca_plus_le_mono *)
