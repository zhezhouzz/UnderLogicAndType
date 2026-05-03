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

Context {V : Type} `{ValueSig V}.

Local Notation StoreT := (gmap atom V) (only parsing).
Local Notation WfWorldT := (WfWorld (V := V)) (only parsing).
Local Notation LogicQualifierT := (logic_qualifier (V := V)) (only parsing).

(** ** Formula syntax *)

Inductive Formula : Type :=
  | FTrue
  | FFalse
  | FAtom   (a : LogicQualifierT)
  | FAnd    (p q : Formula)
  | FOr     (p q : Formula)
  | FImpl   (p q : Formula)                     (* Kripke implication *)
  | FStar   (p q : Formula)                     (* separating conjunction p ∗ q *)
  | FWand   (p q : Formula)                     (* magic wand p −∗ q *)
  | FPlus   (p q : Formula)                     (* choice sum p ⊕ q *)
  | FForall (p : Formula)                       (* ordinary universal quantifier *)
  | FExists (p : Formula)                       (* ordinary existential quantifier *)
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
  | FForall p | FExists p => formula_fv p
  | FOver p | FUnder p => formula_fv p
  | FFib x p => {[x]} ∪ formula_fv p
  end.

#[global] Instance stale_formula : Stale Formula := formula_fv.
Arguments stale_formula /.

Fixpoint formula_open (k : nat) (x : atom) (φ : Formula) : Formula :=
  match φ with
  | FTrue => FTrue
  | FFalse => FFalse
  | FAtom q => FAtom (qual_open_atom k x q)
  | FAnd p q => FAnd (formula_open k x p) (formula_open k x q)
  | FOr p q => FOr (formula_open k x p) (formula_open k x q)
  | FImpl p q => FImpl (formula_open k x p) (formula_open k x q)
  | FStar p q => FStar (formula_open k x p) (formula_open k x q)
  | FWand p q => FWand (formula_open k x p) (formula_open k x q)
  | FPlus p q => FPlus (formula_open k x p) (formula_open k x q)
  | FForall p => FForall (formula_open (S k) x p)
  | FExists p => FExists (formula_open (S k) x p)
  | FOver p => FOver (formula_open k x p)
  | FUnder p => FUnder (formula_open k x p)
  | FFib y p => FFib y (formula_open k x p)
  end.

Fixpoint formula_measure (φ : Formula) : nat :=
  match φ with
  | FTrue | FFalse | FAtom _ => 1
  | FAnd p q | FOr p q | FImpl p q | FStar p q | FWand p q | FPlus p q =>
      1 + formula_measure p + formula_measure q
  | FForall p | FExists p | FOver p | FUnder p | FFib _ p =>
      1 + formula_measure p
  end.

Lemma formula_open_preserves_measure φ k x :
  formula_measure (formula_open k x φ) = formula_measure φ.
Proof. induction φ in k |- *; simpl; eauto; lia. Qed.

(** ** Satisfaction relation

    [res_models m φ] is written [m ⊨ φ] by the ChoiceType layer.
    Since atoms are logic qualifiers, [FAtom] delegates to
    [logic_qualifier_denote].  [FFib] changes the current world to the
    corresponding fiber and extends the explicit store with the projection. *)

Fixpoint res_models_with_store_fuel
    (gas : nat)
    (ρ : StoreT)
    (m : WfWorldT)
    (φ : Formula) : Prop :=
  match gas with
  | 0 => False
  | S gas' =>
  match φ with

  (** Basic connectives (Definition 1.8) *)

  | FTrue  => True

  | FFalse => False

  | FAtom a =>
      (** m ⊨ a iff the denotation of the logic qualifier holds of m. *)
      qual_bvars a = ∅ ∧ logic_qualifier_denote a ∅ ρ m

  | FAnd p q =>
      res_models_with_store_fuel gas' ρ m p ∧
      res_models_with_store_fuel gas' ρ m q

  | FOr p q =>
      res_models_with_store_fuel gas' ρ m p ∨
      res_models_with_store_fuel gas' ρ m q

  | FImpl p q =>
      (** Kripke implication: ∀ m' ≥ m. m' ⊨ p → m' ⊨ q *)
      ∀ m' : WfWorldT,
        m ⊑ m' →
        res_models_with_store_fuel gas' ρ m' p →
        res_models_with_store_fuel gas' ρ m' q

  | FStar p q =>
      (** m ⊨ p ∗ q  iff  ∃ m1 m2. m1 × m2 ≤ m  ∧  m1 ⊨ p  ∧  m2 ⊨ q *)
      ∃ (m1 m2 : WfWorldT) (Hc : world_compat m1 m2),
        res_product m1 m2 Hc ⊑ m ∧
        res_models_with_store_fuel gas' ρ m1 p ∧
        res_models_with_store_fuel gas' ρ m2 q

  | FWand p q =>
      (** m ⊨ p −∗ q  iff  ∀ m'. m' ↑ m  →  m' ⊨ p  →  m' × m ⊨ q *)
      ∀ m' : WfWorldT,
        ∀ Hc : world_compat m' m,
        res_models_with_store_fuel gas' ρ m' p →
        res_models_with_store_fuel gas' ρ (res_product m' m Hc) q

  | FPlus p q =>
      (** m ⊨ p ⊕ q  iff  ∃ m1 m2. m1 + m2 ≤ m  ∧  m1 ⊨ p  ∧  m2 ⊨ q *)
      ∃ (m1 m2 : WfWorldT) (Hdef : raw_sum_defined m1 m2),
        res_sum m1 m2 Hdef ⊑ m ∧
        res_models_with_store_fuel gas' ρ m1 p ∧
        res_models_with_store_fuel gas' ρ m2 q

  | FForall p =>
      (** m ⊨ ∀x.p iff x is fresh for m and every one-coordinate extension
          of m at x models p. *)
      ∀ x : atom,
      x ∉ world_dom m →
      ∀ m' : WfWorldT,
          world_dom m' = world_dom m ∪ {[x]} →
          res_restrict m' (world_dom m) = m →
          res_models_with_store_fuel gas' (delete x ρ) m' (formula_open 0 x p)

  | FExists p =>
      (** m ⊨ ∃x.p iff x is fresh for m and some one-coordinate extension
          of m at x models p. *)
      ∃ x : atom,
      x ∉ world_dom m ∧
      ∃ m' : WfWorldT,
          world_dom m' = world_dom m ∪ {[x]} ∧
          res_restrict m' (world_dom m) = m ∧
          res_models_with_store_fuel gas' (delete x ρ) m' (formula_open 0 x p)

  (** Approximation modalities (Definition 1.9) *)

  | FOver p =>
      (** m ⊨ o p  iff  ∃ m'. m ⊆ m' ∧ m' ⊨ p
          where subset compares worlds with the same domain. *)
      ∃ m' : WfWorldT, res_subset m m' ∧
        res_models_with_store_fuel gas' ρ m' p

  | FUnder p =>
      (** m ⊨ u p  iff  ∃ m'. m' ⊆ m ∧ m' ⊨ p
          where subset compares worlds with the same domain. *)
      ∃ m' : WfWorldT, res_subset m' m ∧
        res_models_with_store_fuel gas' ρ m' p

  | FFib x p =>
      (** m ⊨ FFib x p iff ρ is disjoint from x and every x-fiber of m
          models p under ρ ∪ σ_x. *)
      dom ρ ## {[x]} ∧
      ∀ σ (Hproj : res_restrict m {[x]} σ),
        res_models_with_store_fuel gas' (ρ ∪ σ)
          (res_fiber_from_projection m {[x]} σ Hproj) p

  end
  end.

Definition res_models_with_store
    (ρ : StoreT)
    (m : WfWorldT)
    (φ : Formula) : Prop :=
  res_models_with_store_fuel (formula_measure φ) ρ m φ.

(** [res_models m φ] is the empty-store instance of the substitution-aware
    satisfaction relation. *)
Definition res_models (m : WfWorldT) (φ : Formula) : Prop :=
  res_models_with_store ∅ m φ.

(** Entailment: φ ⊨ ψ holds when every world modeling φ also models ψ. *)
Definition entails (φ ψ : Formula) : Prop :=
  ∀ m, res_models m φ → res_models m ψ.

End ChoiceLogic.
