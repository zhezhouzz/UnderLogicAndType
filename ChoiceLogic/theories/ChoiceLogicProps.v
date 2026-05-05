From ChoiceLogic Require Import Prelude LogicQualifier Formula.

(** * Choice Logic Properties  (§1.2–1.3)

    Key theorems about the logic:
    1.  Modality monotonicity w.r.t. entailment
    2.  Modality set-level characterisations (o, u as closure operators)
    3.  Collapse of nested modalities (Theorem 1.11) *)

Section ChoiceLogicProps.

Context {V : Type} `{ValueSig V}.

Local Notation WfWorldT := (WfWorld (V := V)) (only parsing).
Local Notation LogicQualifierT := (logic_qualifier (V := V)) (only parsing).

Local Notation FormulaT := (Formula (V := V)) (only parsing).

Notation sat m φ := (res_models m φ).
Notation "φ ⊫ ψ" := (entails φ ψ) (at level 85, ψ at level 84, no associativity).

(** *** §1 Modality monotonicity *)

(** o and u are monotone w.r.t. entailment. *)
Lemma over_mono (p q : FormulaT) :
  (p ⊫ q) → (FOver p ⊫ FOver q).
Proof. unfold entails, sat in *. intros Hip m [m' [Hle Hp]]. hauto. Qed.

Lemma under_mono (p q : FormulaT) :
  (p ⊫ q) → (FUnder p ⊫ FUnder q).
Proof. unfold entails, sat in *. intros Hip m [m' [Hle Hp]]. hauto. Qed.

(** Ordinary quantifiers are monotone. *)
Lemma forall_mono (x : atom) (p q : FormulaT) :
  (p ⊫ q) → (FForall x p ⊫ FForall x q).
Proof. Admitted.

Lemma exists_mono (x : atom) (p q : FormulaT) :
  (p ⊫ q) → (FExists x p ⊫ FExists x q).
Proof. Admitted.

(** *** §2 Modality set-level characterisations

    Write ⟦φ⟧ for the extension of φ: the set of worlds satisfying φ. *)

Definition ext (φ : FormulaT) : WfWorldT → Prop :=
  λ m, sat m φ.

(** Over-closure: O(R) = { m' | ∃ m ∈ R. m ⊆ m' }, using same-domain subset. *)
Definition over_closure (R : WfWorldT → Prop) : WfWorldT → Prop :=
  λ m', ∃ m, R m ∧ res_subset m m'.

(** Under-closure: U(R) = { m' | ∃ m ∈ R. m' ⊆ m }, using same-domain subset. *)
Definition under_closure (R : WfWorldT → Prop) : WfWorldT → Prop :=
  λ m', ∃ m, R m ∧ res_subset m' m.

(** FOver p in m ↔ ∃ m' ⊇ m. m' ⊨ p, i.e., m lies in the *under*-closure of ext p. *)
Lemma over_ext_eq (p : FormulaT) :
  ∀ m, ext (FOver p) m ↔ under_closure (ext p) m.
Proof. Admitted.

(** FUnder p in m ↔ ∃ m' ⊆ m. m' ⊨ p, i.e., m lies in the *over*-closure of ext p. *)
Lemma under_ext_eq (p : FormulaT) :
  ∀ m, ext (FUnder p) m ↔ over_closure (ext p) m.
Proof. Admitted.

(** ** Adjunction: ∗ and −∗ *)

Lemma star_wand_adjunction (p q r : FormulaT) :
  (FAnd (FStar p q) r ⊫ FStar p (FAnd q r)) →
  (p ⊫ FWand q r) →
  (FStar p q ⊫ r).
Proof. Admitted.

End ChoiceLogicProps.
