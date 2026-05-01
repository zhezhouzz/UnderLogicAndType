From ChoiceLogic Require Import Prelude LogicQualifier.

(** * Choice Logic  (Definitions 1.8 and 1.9)

    We define the syntax of choice logic formulas and the satisfaction relation.

    Atomic propositions are logic qualifiers.
    Hence satisfaction does not need a separate interpretation function.

    The formula type [Formula] contains:
    - standard connectives (⊤, ⊥, atoms, ∧, ∨, ⇒)
    - separation logic connectives (∗, −∗)
    - choice sum (⊕)
    - approximation modalities (o = over, u = under)
    - ordinary quantifiers over fresh world coordinates
    - fiberwise modality [FFib x p]: for each σ_x in the x-projection of m,
      the well-formed fiber world models p under the extended store. *)

Section ChoiceLogic.

(** ** Formula syntax *)

Inductive Formula : Type :=
  | FTrue
  | FFalse
  | FAtom   (a : logic_qualifier)
  | FAnd    (p q : Formula)
  | FOr     (p q : Formula)
  | FImpl   (p q : Formula)                     (* Kripke implication *)
  | FStar   (p q : Formula)                     (* separating conjunction p ∗ q *)
  | FWand   (p q : Formula)                     (* magic wand p −∗ q *)
  | FPlus   (p q : Formula)                     (* choice sum p ⊕ q *)
  | FForall (x : atom) (p : Formula)            (* ordinary universal quantifier *)
  | FExists (x : atom) (p : Formula)            (* ordinary existential quantifier *)
  | FOver   (p : Formula)                       (* overapproximation  o p *)
  | FUnder  (p : Formula)                       (* underapproximation u p *)
  | FFib    (x : atom)                          (* fiberwise modality *)
            (p : Formula).

Fixpoint formula_fv (φ : Formula) : aset :=
  match φ with
  | FTrue | FFalse => ∅
  | FAtom q => stale q
  | FAnd p q | FOr p q | FImpl p q | FStar p q | FWand p q | FPlus p q =>
      formula_fv p ∪ formula_fv q
  | FForall x p | FExists x p => formula_fv p ∖ {[x]}
  | FOver p | FUnder p => formula_fv p
  | FFib x p => {[x]} ∪ formula_fv p
  end.

#[global] Instance stale_formula : Stale Formula := formula_fv.
Arguments stale_formula /.

(** ** Satisfaction relation

    [res_models m φ] is written [m ⊨ φ] by the ChoiceType layer.
    Since atoms are logic qualifiers, [FAtom] delegates to
    [logic_qualifier_denote].  [FFib] changes the current world to the
    corresponding fiber and extends the explicit store with the projection. *)

Fixpoint res_models_with_store
    (ρ : Store)
    (m : WfWorld)
    (φ : Formula) : Prop :=
  match φ with

  (** Basic connectives (Definition 1.8) *)

  | FTrue  => True

  | FFalse => False

  | FAtom a =>
      (** m ⊨ a iff the denotation of the logic qualifier holds of m. *)
      logic_qualifier_denote a ρ m

  | FAnd p q =>
      res_models_with_store ρ m p ∧ res_models_with_store ρ m q

  | FOr p q =>
      res_models_with_store ρ m p ∨ res_models_with_store ρ m q

  | FImpl p q =>
      (** Kripke implication: ∀ m' ≥ m. m' ⊨ p → m' ⊨ q *)
      ∀ m' : WfWorld,
        m ⊑ m' →
        res_models_with_store ρ m' p →
        res_models_with_store ρ m' q

  | FStar p q =>
      (** m ⊨ p ∗ q  iff  ∃ m1 m2. m1 × m2 ≤ m  ∧  m1 ⊨ p  ∧  m2 ⊨ q *)
      ∃ (m1 m2 : WfWorld) (Hc : world_compat m1 m2),
        res_product m1 m2 Hc ⊑ m ∧
        res_models_with_store ρ m1 p ∧
        res_models_with_store ρ m2 q

  | FWand p q =>
      (** m ⊨ p −∗ q  iff  ∀ m'. m' ↑ m  →  m' ⊨ p  →  m' × m ⊨ q *)
      ∀ m' : WfWorld,
        ∀ Hc : world_compat m' m,
        res_models_with_store ρ m' p →
        res_models_with_store ρ (res_product m' m Hc) q

  | FPlus p q =>
      (** m ⊨ p ⊕ q  iff  ∃ m1 m2. m1 + m2 ≤ m  ∧  m1 ⊨ p  ∧  m2 ⊨ q *)
      ∃ (m1 m2 : WfWorld) (Hdef : raw_sum_defined m1 m2),
        res_sum m1 m2 Hdef ⊑ m ∧
        res_models_with_store ρ m1 p ∧
        res_models_with_store ρ m2 q

  | FForall x p =>
      (** m ⊨ ∀x.p iff x is fresh for m and every one-coordinate extension
          of m at x models p. *)
      x ∉ world_dom m ∧
      ∀ m' : WfWorld,
          world_dom m' = world_dom m ∪ {[x]} →
          res_restrict m' (world_dom m) = m →
          res_models_with_store (delete x ρ) m' p

  | FExists x p =>
      (** m ⊨ ∃x.p iff x is fresh for m and some one-coordinate extension
          of m at x models p. *)
      x ∉ world_dom m ∧
      ∃ m' : WfWorld,
          world_dom m' = world_dom m ∪ {[x]} ∧
          res_restrict m' (world_dom m) = m ∧
          res_models_with_store (delete x ρ) m' p

  (** Approximation modalities (Definition 1.9) *)

  | FOver p =>
      (** m ⊨ o p  iff  ∃ m'. m ⊆ m' ∧ m' ⊨ p
          where subset compares worlds with the same domain. *)
      ∃ m' : WfWorld, res_subset m m' ∧ res_models_with_store ρ m' p

  | FUnder p =>
      (** m ⊨ u p  iff  ∃ m'. m' ⊆ m ∧ m' ⊨ p
          where subset compares worlds with the same domain. *)
      ∃ m' : WfWorld, res_subset m' m ∧ res_models_with_store ρ m' p

  | FFib x p =>
      (** m ⊨ FFib x p iff ρ is disjoint from x and every x-fiber of m
          models p under ρ ∪ σ_x. *)
      dom ρ ## {[x]} ∧
      ∀ σ (Hproj : res_restrict m {[x]} σ),
        res_models_with_store (ρ ∪ σ) (res_fiber_from_projection m {[x]} σ Hproj) p

  end.

(** [res_models m φ] is the empty-store instance of the substitution-aware
    satisfaction relation. *)
Definition res_models (m : WfWorld) (φ : Formula) : Prop :=
  res_models_with_store ∅ m φ.

(** Entailment: φ ⊨ ψ holds when every world modeling φ also models ψ. *)
Definition entails (φ ψ : Formula) : Prop :=
  ∀ m, res_models m φ → res_models m ψ.

End ChoiceLogic.
