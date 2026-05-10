From ChoiceLogic Require Import Prelude LogicQualifier Formula FormulaTactics.

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
Proof.
  unfold entails, sat, res_models, res_models_with_store in *.
  intros Hip m [Hscope [m' [Hsub Hp]]].
  pose proof (Hip m' Hp) as Hq.
  pose proof (res_models_with_store_fuel_scoped (formula_measure q) ∅ m' q Hq)
    as Hq_scope.
  split.
  - eapply formula_scoped_world_dom_eq; [| exact Hq_scope].
    destruct Hsub as [Hdom _]. symmetry. exact Hdom.
  - exists m'. split; [exact Hsub | exact Hq].
Qed.

Lemma under_mono (p q : FormulaT) :
  (p ⊫ q) → (FUnder p ⊫ FUnder q).
Proof.
  unfold entails, sat, res_models, res_models_with_store in *.
  intros Hip m [Hscope [m' [Hsub Hp]]].
  pose proof (Hip m' Hp) as Hq.
  pose proof (res_models_with_store_fuel_scoped (formula_measure q) ∅ m' q Hq)
    as Hq_scope.
  split.
  - eapply formula_scoped_world_dom_eq; [| exact Hq_scope].
    destruct Hsub as [Hdom _]. exact Hdom.
  - exists m'. split; [exact Hsub | exact Hq].
Qed.

(** Ordinary quantifiers are monotone. *)
Lemma forall_mono (x : atom) (p q : FormulaT) :
  (p ⊫ q) → (FForall x p ⊫ FForall x q).
Proof.
  unfold entails, sat, res_models, res_models_with_store in *.
  intros Hpq m [Hscope [L [HL Hforall]]].
  set (L' := L ∪ formula_fv p ∪ formula_fv q).
  split.
  - eapply formula_scoped_forall_from_renamed with (L := L').
    { unfold L'. set_solver. }
    intros y Hy m' Hdom Hrestr.
    assert (HyL : y ∉ L) by (unfold L' in Hy; set_solver).
    assert (Hyfresh : y ∉ formula_fv p ∪ formula_fv q)
      by (unfold L' in Hy; set_solver).
    pose proof (Hforall y HyL m' Hdom Hrestr) as Hp.
    assert (Hp_exact : res_models_with_store_fuel
        (formula_measure (formula_rename_atom x y p)) ∅ m'
        (formula_rename_atom x y p))
      by (rewrite formula_rename_preserves_measure; exact Hp).
    pose proof (entails_rename_atom_fresh_fuel x y p q m' Hyfresh Hpq Hp_exact) as Hq.
    exact (res_models_with_store_fuel_scoped
      (formula_measure (formula_rename_atom x y q)) ∅ m'
      (formula_rename_atom x y q) Hq).
  - exists L'. split; [unfold L'; set_solver |].
    intros y Hy m' Hdom Hrestr.
    assert (HyL : y ∉ L) by (unfold L' in Hy; set_solver).
    assert (Hyfresh : y ∉ formula_fv p ∪ formula_fv q)
      by (unfold L' in Hy; set_solver).
    pose proof (Hforall y HyL m' Hdom Hrestr) as Hp.
    assert (Hp_exact : res_models_with_store_fuel
        (formula_measure (formula_rename_atom x y p)) ∅ m'
        (formula_rename_atom x y p))
      by (rewrite formula_rename_preserves_measure; exact Hp).
    pose proof (entails_rename_atom_fresh_fuel x y p q m' Hyfresh Hpq Hp_exact) as Hq.
    rewrite formula_rename_preserves_measure in Hq. exact Hq.
Qed.

Lemma exists_mono (x : atom) (p q : FormulaT) :
  (p ⊫ q) → (FExists x p ⊫ FExists x q).
Proof.
  unfold entails, sat, res_models, res_models_with_store in *.
  intros Hpq m [Hscope [L [HL Hexists]]].
  set (L' := L ∪ formula_fv p ∪ formula_fv q).
  split.
  - eapply formula_scoped_exists_from_renamed with (L := L').
    { unfold L'. set_solver. }
    intros y Hy.
    assert (HyL : y ∉ L) by (unfold L' in Hy; set_solver).
    assert (Hyfresh : y ∉ formula_fv p ∪ formula_fv q)
      by (unfold L' in Hy; set_solver).
    destruct (Hexists y HyL) as [m' [Hdom [Hrestr Hp]]].
    exists m'. split; [exact Hdom |]. split; [exact Hrestr |].
    assert (Hp_exact : res_models_with_store_fuel
        (formula_measure (formula_rename_atom x y p)) ∅ m'
        (formula_rename_atom x y p))
      by (rewrite formula_rename_preserves_measure; exact Hp).
    pose proof (entails_rename_atom_fresh_fuel x y p q m' Hyfresh Hpq Hp_exact) as Hq.
    exact (res_models_with_store_fuel_scoped
      (formula_measure (formula_rename_atom x y q)) ∅ m'
      (formula_rename_atom x y q) Hq).
  - exists L'. split; [unfold L'; set_solver |].
    intros y Hy.
    assert (HyL : y ∉ L) by (unfold L' in Hy; set_solver).
    assert (Hyfresh : y ∉ formula_fv p ∪ formula_fv q)
      by (unfold L' in Hy; set_solver).
    destruct (Hexists y HyL) as [m' [Hdom [Hrestr Hp]]].
    exists m'. split; [exact Hdom |]. split; [exact Hrestr |].
    assert (Hp_exact : res_models_with_store_fuel
        (formula_measure (formula_rename_atom x y p)) ∅ m'
        (formula_rename_atom x y p))
      by (rewrite formula_rename_preserves_measure; exact Hp).
    pose proof (entails_rename_atom_fresh_fuel x y p q m' Hyfresh Hpq Hp_exact) as Hq.
    rewrite formula_rename_preserves_measure in Hq. exact Hq.
Qed.

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
Proof.
  intros m. unfold ext, under_closure, sat, res_models, res_models_with_store.
  simpl. split.
  - intros [_ [m' [Hsub Hp]]]. exists m'. split; [exact Hp | exact Hsub].
  - intros [m' [Hp Hsub]]. split.
    + pose proof (res_models_with_store_fuel_scoped (formula_measure p) ∅ m' p Hp)
        as Hscope.
      eapply formula_scoped_world_dom_eq; [| exact Hscope].
      destruct Hsub as [Hdom _]. symmetry. exact Hdom.
    + exists m'. split; [exact Hsub | exact Hp].
Qed.

(** FUnder p in m ↔ ∃ m' ⊆ m. m' ⊨ p, i.e., m lies in the *over*-closure of ext p. *)
Lemma under_ext_eq (p : FormulaT) :
  ∀ m, ext (FUnder p) m ↔ over_closure (ext p) m.
Proof.
  intros m. unfold ext, over_closure, sat, res_models, res_models_with_store.
  simpl. split.
  - intros [_ [m' [Hsub Hp]]]. exists m'. split; [exact Hp | exact Hsub].
  - intros [m' [Hp Hsub]]. split.
    + pose proof (res_models_with_store_fuel_scoped (formula_measure p) ∅ m' p Hp)
        as Hscope.
      eapply formula_scoped_world_dom_eq; [| exact Hscope].
      destruct Hsub as [Hdom _]. exact Hdom.
    + exists m'. split; [exact Hsub | exact Hp].
Qed.

(** ** Adjunction: ∗ and −∗ *)

Lemma star_wand_adjunction (p q r : FormulaT) :
  (FAnd (FStar p q) r ⊫ FStar p (FAnd q r)) →
  (p ⊫ FWand q r) →
  (FStar p q ⊫ r).
Proof.
  intros _ Hp_wand.
  unfold entails, sat, res_models, res_models_with_store in *.
  intros m [Hscope [m1 [m2 [Hc [Hprod [Hp Hq]]]]]].
  assert (Hp_exact : res_models_with_store_fuel (formula_measure p) ∅ m1 p).
  { models_fuel_irrel Hp. }
  pose proof (Hp_wand m1 Hp_exact) as Hwand.
  simpl in Hwand. destruct Hwand as [_ Hwand_body].
  destruct (res_product_comm_eq m1 m2 Hc) as [Hc' Hcomm].
  assert (Hq_wand :
      res_models_with_store_fuel (formula_measure q + formula_measure r) ∅ m2 q).
  { models_fuel_irrel Hq. }
  pose proof (Hwand_body m2 Hc' Hq_wand) as Hr_comm.
  assert (Hr_exact :
      res_models_with_store_fuel (formula_measure r) ∅ (res_product m2 m1 Hc') r).
  { models_fuel_irrel Hr_comm. }
  eapply res_models_with_store_fuel_kripke; [| exact Hr_exact].
  rewrite <- Hcomm. exact Hprod.
Qed.

End ChoiceLogicProps.
