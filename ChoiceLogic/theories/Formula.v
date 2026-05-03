From ChoiceLogic Require Import Prelude LogicQualifier.

(** * Choice Logic  (Definitions 1.8 and 1.9)

    Formulas are independent of the core language.  Core expressions are
    embedded into the logic by ChoiceType through ordinary logic qualifiers. *)

Section Formula.

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
  | FForall (x : atom) (p : Formula)            (* ordinary universal quantifier *)
  | FExists (x : atom) (p : Formula)            (* ordinary existential quantifier *)
  | FOver   (p : Formula)                       (* overapproximation  o p *)
  | FUnder  (p : Formula)                       (* underapproximation u p *)
  | FFib    (x : atom) (p : Formula).           (* fiberwise modality *)

Fixpoint formula_fv (φ : Formula) : aset :=
  match φ with
  | FTrue | FFalse => ∅
  | FAtom q => stale q
  | FAnd p q | FOr p q | FImpl p q | FStar p q | FWand p q | FPlus p q =>
      formula_fv p ∪ formula_fv q
  | FForall x p | FExists x p => {[x]} ∪ formula_fv p
  | FOver p | FUnder p => formula_fv p
  | FFib x p => {[x]} ∪ formula_fv p
  end.

#[global] Instance stale_formula : Stale Formula := formula_fv.
Arguments stale_formula /.

Fixpoint formula_measure (φ : Formula) : nat :=
  match φ with
  | FTrue | FFalse | FAtom _ => 1
  | FAnd p q | FOr p q | FImpl p q | FStar p q | FWand p q | FPlus p q =>
      1 + formula_measure p + formula_measure q
  | FForall _ p | FExists _ p | FOver p | FUnder p | FFib _ p =>
      1 + formula_measure p
  end.

(** ** Satisfaction relation *)

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
      logic_qualifier_denote a ρ m

  | FAnd p q =>
      res_models_with_store_fuel gas' ρ m p ∧
      res_models_with_store_fuel gas' ρ m q

  | FOr p q =>
      res_models_with_store_fuel gas' ρ m p ∨
      res_models_with_store_fuel gas' ρ m q

  | FImpl p q =>
      ∀ m' : WfWorldT,
        m ⊑ m' →
        res_models_with_store_fuel gas' ρ m' p →
        res_models_with_store_fuel gas' ρ m' q

  | FStar p q =>
      ∃ (m1 m2 : WfWorldT) (Hc : world_compat m1 m2),
        res_product m1 m2 Hc ⊑ m ∧
        res_models_with_store_fuel gas' ρ m1 p ∧
        res_models_with_store_fuel gas' ρ m2 q

  | FWand p q =>
      ∀ m' : WfWorldT,
        ∀ Hc : world_compat m' m,
        res_models_with_store_fuel gas' ρ m' p →
        res_models_with_store_fuel gas' ρ (res_product m' m Hc) q

  | FPlus p q =>
      ∃ (m1 m2 : WfWorldT) (Hdef : raw_sum_defined m1 m2),
        res_sum m1 m2 Hdef ⊑ m ∧
        res_models_with_store_fuel gas' ρ m1 p ∧
        res_models_with_store_fuel gas' ρ m2 q

  | FForall x p =>
      x ∉ world_dom m ∧ x ∉ dom ρ ∧
      ∀ m' : WfWorldT,
        world_dom m' = world_dom m ∪ {[x]} →
        res_restrict m' (world_dom m) = m →
        res_models_with_store_fuel gas' ρ m' p

  | FExists x p =>
      x ∉ world_dom m ∧ x ∉ dom ρ ∧
      ∃ m' : WfWorldT,
        world_dom m' = world_dom m ∪ {[x]} ∧
        res_restrict m' (world_dom m) = m ∧
        res_models_with_store_fuel gas' ρ m' p

  (** Approximation modalities (Definition 1.9) *)

  | FOver p =>
      ∃ m' : WfWorldT, res_subset m m' ∧
        res_models_with_store_fuel gas' ρ m' p

  | FUnder p =>
      ∃ m' : WfWorldT, res_subset m' m ∧
        res_models_with_store_fuel gas' ρ m' p

  | FFib x p =>
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

End Formula.
