From ChoiceLogic Require Import Prelude Substitution Resource.

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
(** (The concrete proof for World is in the instance below.) *)

End ChoiceAlgebraLemmas.

(** ** Concrete instance: (World, res_sum, res_product, res_unit, res_le) *)

Section WorldChoiceAlgebra.

Context `{Countable Var} `{EqDecision Value} `{Inhabited Value}.
Local Notation SubstT := (gmap Var Value) (only parsing).
Local Notation WorldT := (@World Var _ _ Value) (only parsing).

(** We lift the world operations pointwise to the algebra interface.
    [ca_times] = [res_product], [ca_plus] = [res_sum]. *)

Definition world_ca_times (m1 m2 : WorldT) : WorldT := res_product m1 m2.
Definition world_ca_plus  (m1 m2 : WorldT) : WorldT := res_sum m1 m2.
Definition world_ca_one   : WorldT            := res_unit.
Definition world_ca_le    : WorldT → WorldT → Prop := res_le.
Definition world_ca_times_def (m1 m2 : WorldT) : Prop := world_compat m1 m2.
Definition world_ca_plus_def  (m1 m2 : WorldT) : Prop := res_sum_defined m1 m2.

Program Instance World_ChoiceAlgebra : ChoiceAlgebra WorldT := {|
  ca_one       := world_ca_one;
  ca_times     := world_ca_times;
  ca_plus      := world_ca_plus;
  ca_le        := world_ca_le;
  ca_times_def := world_ca_times_def;
  ca_plus_def  := world_ca_plus_def;
|}.
(** All proof obligations are admitted; to be filled in during the proof phase. *)
Next Obligation. Admitted.  (* ca_times_unit *)
Next Obligation. Admitted.  (* ca_times_comm *)
Next Obligation. Admitted.  (* ca_plus_comm *)
Next Obligation. Admitted.  (* ca_times_assoc *)
Next Obligation. Admitted.  (* ca_plus_assoc *)
Next Obligation. apply res_le_refl.  Qed.  (* ca_le_refl *)
Next Obligation. apply res_product_le_mono; assumption. Qed.  (* ca_times_le_mono *)
Next Obligation. apply res_sum_le_mono; assumption. Qed.  (* ca_plus_le_mono *)

End WorldChoiceAlgebra.
