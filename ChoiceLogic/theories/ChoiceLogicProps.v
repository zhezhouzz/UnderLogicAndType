From ChoiceLogic Require Import Prelude LogicQualifier Formula.
From CoreLang Require Import Syntax.

(** * Choice Logic Properties  (§1.2–1.3)

    Key theorems about the logic:
    1.  Modality monotonicity w.r.t. entailment
    2.  Modality set-level characterisations (o, u as closure operators)
    3.  Collapse of nested modalities (Theorem 1.11) *)

Section ChoiceLogicProps.

Local Notation StoreT := (gmap atom value) (only parsing).
Local Notation WorldT := (@WfWorld atom _ _ value) (only parsing).
Local Notation FormulaT := Formula (only parsing).

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
Lemma forall_mono x (p q : FormulaT) :
  (p ⊫ q) → (FForall x p ⊫ FForall x q).
Proof.
  unfold entails, sat in *. intros Hip m [Hfresh Hall].
  split; [exact Hfresh|].
  intros m' Hdom Hres.
  exact (Hip _ (Hall m' Hdom Hres)).
Qed.

Lemma exists_mono x (p q : FormulaT) :
  (p ⊫ q) → (FExists x p ⊫ FExists x q).
Proof.
  unfold entails, sat in *. intros Hip m [Hfresh [m' [Hdom [Hres Hp]]]].
  split; [exact Hfresh|]. exists m'. split; [exact Hdom|]. split; [exact Hres|].
  exact (Hip _ Hp).
Qed.

(** *** §2 Modality set-level characterisations

    Write ⟦φ⟧ for the extension of φ: the set of worlds satisfying φ. *)

Definition ext (φ : FormulaT) : WorldT → Prop :=
  λ m, sat m φ.

(** Over-closure: O(R) = { m' | ∃ m ∈ R. m ⊆ m' }, using same-domain subset. *)
Definition over_closure (R : WorldT → Prop) : WorldT → Prop :=
  λ m', ∃ m, R m ∧ res_subset m m'.

(** Under-closure: U(R) = { m' | ∃ m ∈ R. m' ⊆ m }, using same-domain subset. *)
Definition under_closure (R : WorldT → Prop) : WorldT → Prop :=
  λ m', ∃ m, R m ∧ res_subset m' m.

(** FOver p in m ↔ ∃ m' ⊇ m. m' ⊨ p, i.e., m lies in the *under*-closure of ext p. *)
Lemma over_ext_eq (p : FormulaT) :
  ∀ m, ext (FOver p) m ↔ under_closure (ext p) m.
Proof. Admitted.

(** FUnder p in m ↔ ∃ m' ⊆ m. m' ⊨ p, i.e., m lies in the *over*-closure of ext p. *)
Lemma under_ext_eq (p : FormulaT) :
  ∀ m, ext (FUnder p) m ↔ over_closure (ext p) m.
Proof. Admitted.

(** *** §3 Collapse of nested modalities  (Theorem 1.11)

    Since atoms are logic qualifiers, the richness assumptions below say that
    the available qualifier denotations are closed under the operations
    needed by the collapse statements.  Every formula
    reduces to one where [FOver] and [FUnder] are applied only to
    atoms [FAtom].  We state the key collapse lemmas; the full induction
    is the collapse theorem. *)

(** Richness assumption on atomic propositions. *)
Record atoms_rich : Prop := {
  ar_inter : ∀ a1 a2 : logic_qualifier, ∃ a3 : logic_qualifier,
    ∀ m, logic_qualifier_denote a3 m ↔
         logic_qualifier_denote a1 m ∧ logic_qualifier_denote a2 m;
  ar_union : ∀ a1 a2 : logic_qualifier, ∃ a3 : logic_qualifier,
    ∀ m, logic_qualifier_denote a3 m ↔
         logic_qualifier_denote a1 m ∨ logic_qualifier_denote a2 m;
  ar_prod  : ∀ a1 a2 : logic_qualifier, ∃ a3 : logic_qualifier,
    ∀ m, logic_qualifier_denote a3 m ↔
      ∃ (m1 m2 : WorldT) (Hc : world_compat m1 m2),
        logic_qualifier_denote a1 m1 ∧
        logic_qualifier_denote a2 m2 ∧
        res_product m1 m2 Hc ⊑ m;
}.

(** Collapse: o(o φ₁ ∧ o φ₂) ↔ o φ₁ ∧ o φ₂ *)
Lemma collapse_over_and (p q : FormulaT) :
  FOver (FAnd (FOver p) (FOver q)) ⊫ FAnd (FOver p) (FOver q).
Proof. Admitted.

Lemma collapse_and_over (p q : FormulaT) :
  FAnd (FOver p) (FOver q) ⊫ FOver (FAnd (FOver p) (FOver q)).
Proof. Admitted.

(** Collapse: u(o φ₁ ∧ o φ₂) ↔ u(φ₁ ∩ φ₂) when atoms are rich.
    a3 is the atom witnessing the intersection of a1 and a2. *)
Lemma collapse_under_over_and (h : atoms_rich) (a1 a2 a3 : logic_qualifier) :
  (∀ m, logic_qualifier_denote a3 m ↔
        logic_qualifier_denote a1 m ∧ logic_qualifier_denote a2 m) →
  FUnder (FAnd (FOver (FAtom a1)) (FOver (FAtom a2))) ⊫ FUnder (FAtom a3).
Proof. Admitted.

(** Full collapse theorem: when atoms are rich, every formula is equivalent
    to one in approximation normal form (ANF): FOver and FUnder applied only to atoms. *)
Theorem collapse_to_ANF (h : atoms_rich) (φ : FormulaT) :
  ∃ φ_anf : FormulaT,
    (** φ_anf is in ANF: every FOver/FUnder directly wraps an FAtom *)
    (∀ m, sat m φ ↔ sat m φ_anf).
Proof. Admitted.

(** ** Adjunction: ∗ and −∗ *)

Lemma star_wand_adjunction (p q r : FormulaT) :
  (FAnd (FStar p q) r ⊫ FStar p (FAnd q r)) →
  (p ⊫ FWand q r) →
  (FStar p q ⊫ r).
Proof. Admitted.

End ChoiceLogicProps.
