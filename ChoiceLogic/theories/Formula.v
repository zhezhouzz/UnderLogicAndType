From ChoiceLogic Require Import Prelude.

(** * Choice Logic  (Definitions 1.8 and 1.9)

    We define the syntax of choice logic formulas and the satisfaction relation.

    Atomic propositions are semantic predicates over well-formed worlds
    [WorldT → Prop].
    Hence satisfaction does not need a separate interpretation function.

    The formula type [Formula] contains:
    - standard connectives (⊤, ⊥, atoms, ∧, ∨, ⇒)
    - separation logic connectives (∗, −∗)
    - choice sum (⊕)
    - approximation modalities (o = over, u = under)
    - ordinary quantifiers over fresh world coordinates
    - fiberwise modality [FFib X p]: for each σ_X in the X-projection of m,
      the well-formed fiber world satisfies p. *)

Section ChoiceLogic.

Context `{Countable Var} `{EqDecision Value}.
Local Notation StoreT := (gmap Var Value) (only parsing).
Local Notation WorldT := (@WfWorld Var _ _ Value) (only parsing).

(** ** Formula syntax *)

Inductive Formula : Type :=
  | FTrue
  | FFalse
  | FAtom   (a : WorldT → Prop)
  | FAnd    (p q : Formula)
  | FOr     (p q : Formula)
  | FImpl   (p q : Formula)                     (* Kripke implication *)
  | FStar   (p q : Formula)                     (* separating conjunction p ∗ q *)
  | FWand   (p q : Formula)                     (* magic wand p −∗ q *)
  | FPlus   (p q : Formula)                     (* choice sum p ⊕ q *)
  | FForall (x : Var) (p : Formula)             (* ordinary universal quantifier *)
  | FExists (x : Var) (p : Formula)             (* ordinary existential quantifier *)
  | FOver   (p : Formula)                       (* overapproximation  o p *)
  | FUnder  (p : Formula)                       (* underapproximation u p *)
  | FFib    (X : gset Var)                      (* fiberwise modality *)
            (p : Formula).

(** ** Satisfaction relation

    [res_models m φ] is written [m ⊨ φ] by the ChoiceType layer.
    Since atoms are already world predicates, [FFib] only changes the current
    world to the corresponding fiber; there is no syntactic atom-substitution
    parameter in the logic core. *)

Fixpoint res_models
    (m : WorldT)
    (φ : Formula) : Prop :=
  match φ with

  (** Basic connectives (Definition 1.8) *)

  | FTrue  => True

  | FFalse => False

  | FAtom a =>
      (** m ⊨ a iff the semantic atomic predicate holds of m. *)
      a m

  | FAnd p q =>
      res_models m p ∧ res_models m q

  | FOr p q =>
      res_models m p ∨ res_models m q

  | FImpl p q =>
      (** Kripke implication: ∀ m' ≥ m. m' ⊨ p → m' ⊨ q *)
      ∀ m' : WorldT, m ⊑ m' → res_models m' p → res_models m' q

  | FStar p q =>
      (** m ⊨ p ∗ q  iff  ∃ m1 m2. m1 × m2 ≤ m  ∧  m1 ⊨ p  ∧  m2 ⊨ q *)
      ∃ (m1 m2 : WorldT) (Hc : world_compat m1 m2),
        res_product m1 m2 Hc ⊑ m ∧
        res_models m1 p ∧
        res_models m2 q

  | FWand p q =>
      (** m ⊨ p −∗ q  iff  ∀ m'. m' ↑ m  →  m' ⊨ p  →  m' × m ⊨ q *)
      ∀ m' : WorldT,
        ∀ Hc : world_compat m' m,
        res_models m' p →
        res_models (res_product m' m Hc) q

  | FPlus p q =>
      (** m ⊨ p ⊕ q  iff  ∃ m1 m2. m1 + m2 ≤ m  ∧  m1 ⊨ p  ∧  m2 ⊨ q *)
      ∃ (m1 m2 : WorldT) (Hdef : raw_sum_defined m1 m2),
        res_sum m1 m2 Hdef ⊑ m ∧
        res_models m1 p ∧
        res_models m2 q

  | FForall x p =>
      (** m ⊨ ∀x.p iff every one-coordinate extension of m satisfies p. *)
      ∀ m' : WorldT,
        world_dom m' = world_dom m ∪ {[x]} →
        res_restrict m' (world_dom m) = m →
        res_models m' p

  | FExists x p =>
      (** m ⊨ ∃x.p iff some one-coordinate extension of m satisfies p. *)
      ∃ m' : WorldT,
        world_dom m' = world_dom m ∪ {[x]} ∧
        res_restrict m' (world_dom m) = m ∧
        res_models m' p

  (** Approximation modalities (Definition 1.9) *)

  | FOver p =>
      (** m ⊨ o p  iff  ∃ m' ⊇ m. m' ⊨ p  (over-approximation: superset) *)
      ∃ m' : WorldT, (∀ σ, m σ → m' σ) ∧ res_models m' p

  | FUnder p =>
      (** m ⊨ u p  iff  ∃ m' ⊆ m. m' ⊨ p  (under-approximation: subset) *)
      ∃ m' : WorldT, (∀ σ, m' σ → m σ) ∧ res_models m' p

  | FFib X p =>
      (** m ⊨ FFib X p iff every X-fiber of m satisfies p. *)
      ∀ σ (Hproj : res_restrict m X σ),
        res_models (res_fiber_from_projection m X σ Hproj) p

  end.

(** Entailment: φ ⊨ ψ holds when every world satisfying φ also satisfies ψ. *)
Definition entails (φ ψ : Formula) : Prop :=
  ∀ m, res_models m φ → res_models m ψ.

End ChoiceLogic.

(** After the section closes the section variables become explicit.
    Re-establish implicitness using positional underscores with [rename]
    to avoid name-mismatch errors. *)
Arguments FTrue  {_} {_} {_} {_} : rename.
Arguments FFalse {_} {_} {_} {_} : rename.
Arguments FAtom  {_} {_} {_} {_} _ : rename.
Arguments FAnd   {_} {_} {_} {_} _ _ : rename.
Arguments FOr    {_} {_} {_} {_} _ _ : rename.
Arguments FImpl  {_} {_} {_} {_} _ _ : rename.
Arguments FStar  {_} {_} {_} {_} _ _ : rename.
Arguments FWand  {_} {_} {_} {_} _ _ : rename.
Arguments FPlus  {_} {_} {_} {_} _ _ : rename.
Arguments FForall {_} {_} {_} {_} _ _ : rename.
Arguments FExists {_} {_} {_} {_} _ _ : rename.
Arguments FOver  {_} {_} {_} {_} _ : rename.
Arguments FUnder {_} {_} {_} {_} _ : rename.
Arguments FFib    {_} {_} {_} {_} _ _ : rename.
