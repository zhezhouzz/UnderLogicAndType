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

Fixpoint formula_stale (φ : Formula) : aset :=
  match φ with
  | FTrue | FFalse => ∅
  | FAtom q => stale q
  | FAnd p q | FOr p q | FImpl p q | FStar p q | FWand p q | FPlus p q =>
      formula_stale p ∪ formula_stale q
  | FForall x p | FExists x p => {[x]} ∪ formula_stale p
  | FOver p | FUnder p => formula_stale p
  | FFib x p => {[x]} ∪ formula_stale p
  end.

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

Fixpoint formula_rename_atom (x y : atom) (φ : Formula) : Formula :=
  match φ with
  | FTrue => FTrue
  | FFalse => FFalse
  | FAtom q => FAtom (lqual_rename_atom x y q)
  | FAnd p q => FAnd (formula_rename_atom x y p) (formula_rename_atom x y q)
  | FOr p q => FOr (formula_rename_atom x y p) (formula_rename_atom x y q)
  | FImpl p q => FImpl (formula_rename_atom x y p) (formula_rename_atom x y q)
  | FStar p q => FStar (formula_rename_atom x y p) (formula_rename_atom x y q)
  | FWand p q => FWand (formula_rename_atom x y p) (formula_rename_atom x y q)
  | FPlus p q => FPlus (formula_rename_atom x y p) (formula_rename_atom x y q)
  | FForall z p =>
      FForall (atom_rename x y z) (formula_rename_atom x y p)
  | FExists z p =>
      FExists (atom_rename x y z) (formula_rename_atom x y p)
  | FOver p => FOver (formula_rename_atom x y p)
  | FUnder p => FUnder (formula_rename_atom x y p)
  | FFib z p => FFib (atom_rename x y z) (formula_rename_atom x y p)
  end.

Fixpoint formula_measure (φ : Formula) : nat :=
  match φ with
  | FTrue | FFalse | FAtom _ => 1
  | FAnd p q | FOr p q | FImpl p q | FStar p q | FWand p q | FPlus p q =>
      1 + formula_measure p + formula_measure q
  | FForall _ p | FExists _ p | FOver p | FUnder p | FFib _ p =>
      1 + formula_measure p
  end.

Lemma formula_rename_preserves_measure x y φ :
  formula_measure (formula_rename_atom x y φ) = formula_measure φ.
Proof.
  induction φ; simpl; eauto; lia.
Qed.

Lemma formula_measure_pos (φ : Formula) :
  0 < formula_measure φ.
Proof. induction φ; simpl; lia. Qed.

(** [fresh_forall D body] chooses a syntactic representative for an explicit
    formula binder.  The representative is not semantically privileged:
    [FForall]'s satisfaction relation later renames it to every sufficiently
    fresh atom. *)
Definition fresh_forall (D : aset) (body : atom → Formula) : Formula :=
  let x := fresh_for D in
  FForall x (body x).

(** A formula can only be interpreted at worlds that already track every free
    coordinate it may inspect.  Explicit quantifiers remove their representative
    binder from this set; the bound coordinate is introduced by their semantic
    one-coordinate extension. *)
Definition formula_scoped_in_world
    (ρ : StoreT)
    (m : WfWorldT)
    (φ : Formula) : Prop :=
  dom ρ ∪ formula_fv φ ⊆ world_dom m.

Lemma formula_scoped_res_subset
    (ρ : StoreT) (m m' : WfWorldT) (φ : Formula) :
  formula_scoped_in_world ρ m φ →
  res_subset m m' →
  formula_scoped_in_world ρ m' φ.
Proof.
  unfold formula_scoped_in_world, res_subset.
  intros Hscope [Hdom _]. rewrite <- Hdom. exact Hscope.
Qed.

Lemma formula_scoped_world_dom_eq
    (ρ : StoreT) (m m' : WfWorldT) (φ : Formula) :
  world_dom m = world_dom m' →
  formula_scoped_in_world ρ m φ →
  formula_scoped_in_world ρ m' φ.
Proof.
  unfold formula_scoped_in_world. intros Hdom Hscope. rewrite <- Hdom.
  exact Hscope.
Qed.

(** ** Satisfaction relation *)

Fixpoint res_models_with_store_fuel
    (gas : nat)
    (ρ : StoreT)
    (m : WfWorldT)
    (φ : Formula) : Prop :=
  match gas with
  | 0 => False
  | S gas' =>
  formula_scoped_in_world ρ m φ ∧
  match φ with

  (** Basic connectives (Definition 1.8) *)

  | FTrue  => True

  | FFalse => False

  | FAtom a =>
      ∃ m0 : WfWorldT,
        logic_qualifier_denote a ρ m0 ∧ m0 ⊑ m

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
      ∃ L : aset,
        world_dom m ⊆ L ∧
        ∀ y : atom,
          y ∉ L →
          ∀ m' : WfWorldT,
            world_dom m' = world_dom m ∪ {[y]} →
            res_restrict m' (world_dom m) = m →
            res_models_with_store_fuel gas' ρ m' (formula_rename_atom x y p)

  | FExists x p =>
      ∃ L : aset,
        world_dom m ⊆ L ∧
        ∀ y : atom,
          y ∉ L →
          ∃ m' : WfWorldT,
            world_dom m' = world_dom m ∪ {[y]} ∧
            res_restrict m' (world_dom m) = m ∧
            res_models_with_store_fuel gas' ρ m' (formula_rename_atom x y p)

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

Lemma res_models_with_store_fuel_scoped
    (gas : nat) (ρ : StoreT) (m : WfWorldT) (φ : Formula) :
  res_models_with_store_fuel gas ρ m φ →
  formula_scoped_in_world ρ m φ.
Proof.
  destruct gas as [|gas']; simpl; [tauto | intros [Hscope _]; exact Hscope].
Qed.

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

(** The fuel-level spec records the intended meaning of [fresh_forall]:
    [fresh_for D] is only the body representative, while models checks all
    names outside a cofinite set by renaming that representative. *)
Lemma res_models_fresh_forall_fuel
    (gas : nat) (ρ : StoreT) (m : WfWorldT) (D : aset)
    (body : atom → Formula) :
  res_models_with_store_fuel (S gas) ρ m (fresh_forall D body) ↔
  formula_scoped_in_world ρ m (fresh_forall D body) ∧
  (∃ L : aset,
      world_dom m ⊆ L ∧
      ∀ y : atom,
        y ∉ L →
        ∀ m' : WfWorldT,
          world_dom m' = world_dom m ∪ {[y]} →
          res_restrict m' (world_dom m) = m →
          res_models_with_store_fuel gas ρ m'
            (formula_rename_atom (fresh_for D) y (body (fresh_for D)))).
Proof. reflexivity. Qed.

Lemma res_models_fresh_forall_intro
    (gas : nat) (ρ : StoreT) (m : WfWorldT) (D : aset)
    (body : atom → Formula) :
  formula_scoped_in_world ρ m (fresh_forall D body) →
  (∃ L : aset,
      world_dom m ⊆ L ∧
      ∀ y : atom,
        y ∉ L →
        ∀ m' : WfWorldT,
          world_dom m' = world_dom m ∪ {[y]} →
          res_restrict m' (world_dom m) = m →
          res_models_with_store_fuel gas ρ m'
            (formula_rename_atom (fresh_for D) y (body (fresh_for D)))) →
  res_models_with_store_fuel (S gas) ρ m (fresh_forall D body).
Proof. intros Hscope Hfresh. exact (conj Hscope Hfresh). Qed.

End Formula.
