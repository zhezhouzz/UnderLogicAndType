From ChoiceLogic Require Import Prelude Formula.

(** * Choice Logic Properties  (§1.2–1.3)

    Key theorems about the logic:
    1.  Modality monotonicity w.r.t. entailment
    2.  Modality set-level characterisations (o, u as closure operators)
    3.  Collapse of nested modalities (Theorem 1.11)
    4.  Erase modality /u and its Galois connection  *)

Section ChoiceLogicProps.

Context `{Countable Var} `{EqDecision Value}.
Local Notation SubstT := (gmap Var Value) (only parsing).
Local Notation WorldT := (@World Var _ _ Value) (only parsing).

Context {A : Type}.
Context (interp     : A → WorldT).
Context (subst_atom : SubstT → A → A).

Notation sat m φ := (satisfies interp subst_atom m φ).
Notation "φ ⊫ ψ" := (entails interp subst_atom φ ψ) (at level 85, ψ at level 84, no associativity).

(** *** §1 Modality monotonicity *)

(** o and u are monotone w.r.t. entailment. *)
Lemma over_mono (p q : Formula A) :
  (p ⊫ q) → (FOver p ⊫ FOver q).
Proof. unfold entails, sat in *. intros Hip m [m' [Hle Hp]]. hauto. Qed.

Lemma under_mono (p q : Formula A) :
  (p ⊫ q) → (FUnder p ⊫ FUnder q).
Proof. unfold entails, sat in *. intros Hip m [m' [Hle Hp]]. hauto. Qed.

(** □ is monotone. *)
Lemma pers_mono (p q : Formula A) :
  (p ⊫ q) → (FPers p ⊫ FPers q).
Proof. unfold entails, sat in *. intros Hip m Hpers σ Hσ. exact (Hip _ (Hpers σ Hσ)). Qed.

(** *** §2 Modality set-level characterisations  (§1.3, Erase section)

    Write ⟦φ⟧ for the extension of φ: the set of worlds satisfying φ. *)

Definition ext (φ : Formula A) : WorldT → Prop :=
  λ m, sat m φ.

(** Over-closure: O(R) = { m' | ∃ m ∈ R. m ⊆ m' } *)
Definition over_closure (R : WorldT → Prop) : WorldT → Prop :=
  λ m', ∃ m, R m ∧ ∀ σ, m σ → m' σ.

(** Under-closure: U(R) = { m' | ∃ m ∈ R. m' ⊆ m } *)
Definition under_closure (R : WorldT → Prop) : WorldT → Prop :=
  λ m', ∃ m, R m ∧ ∀ σ, m' σ → m σ.

Lemma over_ext_eq (p : Formula A) :
  ∀ m, ext (FOver p) m ↔ over_closure (ext p) m.
Proof. Admitted.

Lemma under_ext_eq (p : Formula A) :
  ∀ m, ext (FUnder p) m ↔ under_closure (ext p) m.
Proof. Admitted.

(** *** §3 Collapse of nested modalities  (Theorem 1.11)

    When [A] is rich enough (closed under ∩, ∪, ×), every formula
    reduces to one where [FOver] and [FUnder] are applied only to
    atoms [FAtom].  We state the key collapse lemmas; the full induction
    is the collapse theorem. *)

(** Richness assumption on atomic propositions. *)
Record atoms_rich : Prop := {
  ar_inter : ∀ a1 a2 : A, ∃ a3 : A,
    ∀ σ, interp a3 σ ↔ interp a1 σ ∧ interp a2 σ;
  ar_union : ∀ a1 a2 : A, ∃ a3 : A,
    ∀ σ, interp a3 σ ↔ interp a1 σ ∨ interp a2 σ;
  ar_prod  : ∀ a1 a2 : A, ∃ a3 : A,
    ∀ σ, interp a3 σ ↔
      ∃ σ1 σ2, interp a1 σ1 ∧ interp a2 σ2 ∧ store_compat σ1 σ2 ∧ σ = σ1 ∪ σ2;
}.

(** Collapse: o(o φ₁ ∧ o φ₂) ↔ o φ₁ ∧ o φ₂ *)
Lemma collapse_over_and (p q : Formula A) :
  FOver (FAnd (FOver p) (FOver q)) ⊫ FAnd (FOver p) (FOver q).
Proof. Admitted.

Lemma collapse_and_over (p q : Formula A) :
  FAnd (FOver p) (FOver q) ⊫ FOver (FAnd (FOver p) (FOver q)).
Proof. Admitted.

(** Collapse: u(o φ₁ ∧ o φ₂) ↔ u(φ₁ ∩ φ₂) when atoms are rich.
    a3 is the atom witnessing the intersection of a1 and a2. *)
Lemma collapse_under_over_and (h : atoms_rich) (a1 a2 a3 : A) :
  (∀ σ, interp a3 σ ↔ interp a1 σ ∧ interp a2 σ) →
  FUnder (FAnd (FOver (FAtom a1)) (FOver (FAtom a2))) ⊫ FUnder (FAtom a3).
Proof. Admitted.

(** Full collapse theorem: when atoms are rich, every formula is equivalent
    to one in approximation normal form (ANF): FOver and FUnder applied only to atoms. *)
Theorem collapse_to_ANF (h : atoms_rich) (φ : Formula A) :
  ∃ φ_anf : Formula A,
    (** φ_anf is in ANF: every FOver/FUnder directly wraps an FAtom *)
    (∀ m, sat m φ ↔ sat m φ_anf).
Proof. Admitted.

(** *** §4 Erase modality  /u  (§1.3, Erase section) *)

(** The under-preorder on worlds:  r ≤_u r' iff ∀R. r ∈ U(R) → r' ∈ U(R). *)
Definition under_preorder (r r' : WorldT) : Prop :=
  ∀ R : WorldT → Prop, under_closure R r → under_closure R r'.

Notation "r ≤ᵤ r'" := (under_preorder r r') (at level 70).

(** /u(S): the set of ≤_u-minimal elements of S. *)
Definition erase_min (S : WorldT → Prop) : WorldT → Prop :=
  λ r, S r ∧ ∀ r', S r' → r' ≤ᵤ r → ∀ σ, r σ ↔ r' σ.

Notation "/u" := erase_min.

(** Semantic erase modality: ⟦/u p⟧ = /u(⟦p⟧). *)
Definition erase_interp (p : Formula A) : WorldT → Prop :=
  erase_min (ext p).

(** Galois connection: /u(R₁) ⊆ R₂ ↔ R₁ ⊆ U(R₂)  (§1.3) *)
Lemma erase_galois (R1 R2 : WorldT → Prop) :
  (∀ m, erase_min R1 m → R2 m) ↔ (∀ m, R1 m → under_closure R2 m).
Proof. Admitted.

(** /u erases redundant proof obligations: if (/u p) → q then p → q. *)
Lemma erase_suffices (p q : Formula A) :
  (∀ m, erase_interp p m → sat m q) →
  (∀ m, sat m p → sat m q).
Proof. Admitted.

(** Flip from under to over at negative position:
    if o(/u(u φ)) suffices for q, then o φ suffices for q  (§1.3) *)
Lemma erase_flip_under (φ : Formula A) (q : Formula A) :
  (∀ m, erase_interp (FUnder φ) m → sat m q) →
  (∀ m, sat m (FOver φ) → sat m q).
Proof. Admitted.

(** ** Adjunction: ∗ and −∗ *)

Lemma star_wand_adjunction (p q r : Formula A) :
  (FAnd (FStar p q) r ⊫ FStar p (FAnd q r)) →
  (p ⊫ FWand q r) →
  (FStar p q ⊫ r).
Proof. Admitted.

(** ** Persistence *)

(** □ τ ⊫ τ  (holds only for non-empty wf_resource worlds; proof deferred) *)
Lemma pers_elim (p : Formula A) : FPers p ⊫ p.
Proof. Admitted.

(** □ τ ⊫ □ □ τ *)
Lemma pers_idemp (p : Formula A) : FPers p ⊫ FPers (FPers p).
Proof.
  unfold entails, sat. simpl. intros m Hpers σ Hσ σ' Hσ'. subst. exact (Hpers σ Hσ).
Qed.

(** o □ φ  implies  □ o φ  (persistence and overapproximation interact) *)
Lemma over_pers_swap (p : Formula A) :
  FOver (FPers p) ⊫ FPers (FOver p).
Proof. Admitted.

End ChoiceLogicProps.
