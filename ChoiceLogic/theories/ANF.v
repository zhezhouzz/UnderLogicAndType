From ChoiceLogic Require Import Prelude LogicQualifier Formula ChoiceLogicProps.

(** * Approximation Normal Form

    Collapse and ANF statements are useful for relating the surface logic to
    simpler normal forms, but they are not on the main proof path for the
    resource semantics.  We keep them isolated here while the exact richness
    assumptions are still evolving. *)

Section ANF.

Context {V : Type} `{ValueSig V}.

Local Notation WfWorldT := (WfWorld (V := V)) (only parsing).
Local Notation LogicQualifierT := (logic_qualifier (V := V)) (only parsing).
Local Notation FormulaT := (Formula (V := V)) (only parsing).

Notation sat m φ := (res_models m φ).
Notation "φ ⊫ ψ" := (entails φ ψ) (at level 85, ψ at level 84, no associativity).

(** Richness assumption on atomic propositions. *)
Record atoms_rich : Prop := {
  ar_inter : ∀ a1 a2 : LogicQualifierT, ∃ a3 : LogicQualifierT,
    ∀ ρ m, logic_qualifier_denote a3 ρ m ↔
           logic_qualifier_denote a1 ρ m ∧ logic_qualifier_denote a2 ρ m;
  ar_union : ∀ a1 a2 : LogicQualifierT, ∃ a3 : LogicQualifierT,
    ∀ ρ m, logic_qualifier_denote a3 ρ m ↔
           logic_qualifier_denote a1 ρ m ∨ logic_qualifier_denote a2 ρ m;
  ar_prod  : ∀ a1 a2 : LogicQualifierT, ∃ a3 : LogicQualifierT,
    ∀ ρ m, logic_qualifier_denote a3 ρ m ↔
      ∃ (m1 m2 : WfWorldT) (Hc : world_compat m1 m2),
        logic_qualifier_denote a1 ρ m1 ∧
        logic_qualifier_denote a2 ρ m2 ∧
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
    [a3] is the atom witnessing the intersection of [a1] and [a2]. *)
Lemma collapse_under_over_and (h : atoms_rich) (a1 a2 a3 : LogicQualifierT) :
  (∀ ρ m, logic_qualifier_denote a3 ρ m ↔
          logic_qualifier_denote a1 ρ m ∧ logic_qualifier_denote a2 ρ m) →
  FUnder (FAnd (FOver (FAtom a1)) (FOver (FAtom a2))) ⊫ FUnder (FAtom a3).
Proof. Admitted.

(** Full collapse theorem: when atoms are rich, every formula is equivalent
    to one in approximation normal form (ANF): [FOver] and [FUnder] applied
    only to atoms. *)
Theorem collapse_to_ANF (h : atoms_rich) (φ : FormulaT) :
  ∃ φ_anf : FormulaT,
    (∀ m, sat m φ ↔ sat m φ_anf).
Proof. Admitted.

End ANF.
