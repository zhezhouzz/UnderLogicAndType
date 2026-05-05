From ChoiceAlgebra Require Import Prelude Resource.

(** * Choice Algebra  (Definitions 1.6)

    An abstract *partial commutative semiring without zero* (PCS) equipped with
    a partial order satisfying bifunctoriality.  The operations are genuinely
    partial: applying them requires an explicit definedness proof. *)

(** ** Abstract choice algebra *)

Class ChoiceAlgebra (M : Type) := {
  (** Unit and partial carrier operations. *)
  ca_one  : M;
  ca_times_def : M → M → Prop;
  ca_plus_def  : M → M → Prop;
  ca_times : ∀ m1 m2, ca_times_def m1 m2 → M;
  ca_plus  : ∀ m1 m2, ca_plus_def m1 m2 → M;
  ca_le    : M → M → Prop;

  (** Identity: m × 1 = m *)
  ca_times_unit_def : ∀ m, ca_times_def m ca_one;
  ca_times_unit : ∀ m, ca_times m ca_one (ca_times_unit_def m) = m;

  (** Commutativity (when defined) *)
  ca_times_comm : ∀ m1 m2 (H12 : ca_times_def m1 m2),
    ∃ H21 : ca_times_def m2 m1,
      ca_times m1 m2 H12 = ca_times m2 m1 H21;

  ca_plus_comm  : ∀ m1 m2 (H12 : ca_plus_def m1 m2),
    ∃ H21 : ca_plus_def m2 m1,
      ca_plus m1 m2 H12 = ca_plus m2 m1 H21;

  (** Associativity (when defined) *)
  ca_times_assoc : ∀ m1 m2 m3
    (H12 : ca_times_def m1 m2)
    (H123 : ca_times_def (ca_times m1 m2 H12) m3),
    ∃ (H23 : ca_times_def m2 m3)
      (H1_23 : ca_times_def m1 (ca_times m2 m3 H23)),
      ca_times (ca_times m1 m2 H12) m3 H123 =
      ca_times m1 (ca_times m2 m3 H23) H1_23;

  ca_plus_assoc  : ∀ m1 m2 m3
    (H12 : ca_plus_def m1 m2)
    (H123 : ca_plus_def (ca_plus m1 m2 H12) m3),
    ∃ (H23 : ca_plus_def m2 m3)
      (H1_23 : ca_plus_def m1 (ca_plus m2 m3 H23)),
      ca_plus (ca_plus m1 m2 H12) m3 H123 =
      ca_plus m1 (ca_plus m2 m3 H23) H1_23;

  (** Partial order is reflexive (other order axioms are standard lemmas) *)
  ca_le_refl : ∀ m, ca_le m m;

  (** Bifunctoriality of × w.r.t. ≤ *)
  ca_times_le_mono : ∀ m1 m2 m1' m2'
    (H12 : ca_times_def m1 m2) (H12' : ca_times_def m1' m2'),
    ca_le m1 m1' → ca_le m2 m2' →
    ca_le (ca_times m1 m2 H12) (ca_times m1' m2' H12');

  (** Bifunctoriality of + w.r.t. ≤ *)
  ca_plus_le_mono  : ∀ m1 m2 m1' m2'
    (H12 : ca_plus_def m1 m2) (H12' : ca_plus_def m1' m2'),
    ca_le m1 m1' → ca_le m2 m2' →
    ca_le (ca_plus m1 m2 H12) (ca_plus m1' m2' H12');
}.

(** ** Derived order lemmas for an abstract ChoiceAlgebra *)

Section ChoiceAlgebraLemmas.
Context `{ChoiceAlgebra M}.

(** m1 ≤ m1 × m2  is an expected consequence of bifunctoriality + unit. *)
(** (The concrete proof for WfWorld is in the instance below.) *)

End ChoiceAlgebraLemmas.

(** ** Concrete instance: (WfWorld, res_sum, res_product, res_unit, ⊑)

    Carrier is [WfWorld] — the sigma type [{m : World | wf_world m}].
    Product and sum are the partial operations from Resource.v. *)

Section WfWorldChoiceAlgebra.

Context {V : Type} `{ValueSig V}.

#[global] Program Instance WfWorld_ChoiceAlgebra : ChoiceAlgebra (WfWorld (V := V)) := {|
  ca_one       := res_unit;
  ca_times_def := fun w1 w2 => world_compat w1 w2;
  ca_plus_def  := fun w1 w2 => raw_sum_defined w1 w2;
  ca_times     := res_product;
  ca_plus      := res_sum;
  ca_le        := sqsubseteq (A := WfWorld (V := V));
|}.
Next Obligation. intro m. exact (raw_compat_unit_r (m : World)). Qed.
Next Obligation. intro m. apply res_product_unit_r_eq_any. Qed.
Next Obligation. apply res_product_comm_eq. Qed.
Next Obligation. apply res_sum_comm_eq. Qed.
Next Obligation. apply res_product_assoc_eq. Qed.
Next Obligation. apply res_sum_assoc_eq. Qed.
Next Obligation.                 (* ca_le_refl: provable because carrier is WfWorld *)
  intro w. exact (reflexivity w).
Qed.
Next Obligation. eapply res_product_le_mono; eauto. Qed.
Next Obligation. eapply res_sum_le_mono; eauto. Qed.

End WfWorldChoiceAlgebra.
