(** * ContextLogic.FormulaConnectives

    Derived proof principles for Context Logic connectives. *)

From ContextLogic Require Import LogicQualifier FormulaSemantics.
From ContextAlgebra Require Import ResourceInterface ResourceCompat.
From ContextBase Require Import LogicVarOpenEnv.
From Stdlib Require Import Lia.

(** * ContextLogic.FormulaConnectives

    Derived proof principles for the store-free formula semantics.  This file
    keeps only statements that still describe useful structure under the new
    dependent-lqual and extension-based forall definitions. *)


Section FormulaConnectives.

Context {V : Type} `{ValueSig V}.

Local Notation WorldT := (World (V := V)) (only parsing).
Local Notation WfWorldT := (WfWorld (V := V)) (only parsing).
Local Notation StoreT := (Store (V := V)) (only parsing).
Local Notation LogicQualifierT := (logic_qualifier (V := V)) (only parsing).
Local Notation FormulaT := (Formula (V := V)) (only parsing).
Local Notation "m ⊨ φ" := (res_models m φ)
  (at level 70, format "m  ⊨  φ").

Lemma res_models_from_restrict_extension_on_fv
    (m n : WfWorldT) (X : aset) (φ : FormulaT) :
  formula_fv φ ⊆ X ->
  formula_fv φ ⊆ world_dom (m : WorldT) ->
  res_restrict m X ⊑ n ->
  n ⊨ φ ->
  m ⊨ φ.
Proof.
  intros HfvX Hfvm Hle Hn.
  eapply res_models_fuel_projection with (m := n); [| exact Hn].
  transitivity (res_restrict (res_restrict m X) (formula_fv φ)).
  - symmetry. eapply res_restrict_le_eq.
    + exact Hle.
    + set_solver.
  - rewrite res_restrict_restrict_eq.
    replace (X ∩ formula_fv φ) with (formula_fv φ) by set_solver.
    reflexivity.
Qed.

Lemma res_models_and_intro_from_models (m : WfWorldT) (φ ψ : FormulaT) :
  m ⊨ φ →
  m ⊨ ψ →
  m ⊨ FAnd φ ψ.
Proof.
  intros Hφ Hψ.
  eapply res_models_and_intro; [| exact Hφ | exact Hψ].
  apply (proj2 (formula_scoped_and_iff m φ ψ)).
  split; eapply res_models_fuel_scoped; eauto.
Qed.

Lemma res_models_and_iff (m : WfWorldT) (φ ψ : FormulaT) :
  m ⊨ FAnd φ ψ ↔ m ⊨ φ ∧ m ⊨ ψ.
Proof.
  split.
  - intros Hand. split.
    + eapply res_models_and_elim_l; exact Hand.
    + eapply res_models_and_elim_r; exact Hand.
  - intros [Hφ Hψ]. eapply res_models_and_intro_from_models; eauto.
Qed.

Lemma res_models_or_iff (m : WfWorldT) (φ ψ : FormulaT) :
  formula_scoped_in_world m (FOr φ ψ) ->
  m ⊨ FOr φ ψ ↔ m ⊨ φ ∨ m ⊨ ψ.
Proof.
  intros Hscope.
  split.
  - unfold res_models. simpl.
    intros [_ [Hφ|Hψ]].
    + left. eapply res_models_fuel_irrel; [| | exact Hφ]; lia.
    + right. eapply res_models_fuel_irrel; [| | exact Hψ]; lia.
  - intros [Hφ|Hψ].
    + eapply res_models_or_intro_l; [exact Hscope | exact Hφ].
    + eapply res_models_or_intro_r; [exact Hscope | exact Hψ].
Qed.

Lemma res_models_or_intro_l_from_model (m : WfWorldT) (φ ψ : FormulaT) :
  m ⊨ φ →
  formula_fv ψ ⊆ world_dom (m : WorldT) →
  m ⊨ FOr φ ψ.
Proof.
  intros Hφ Hψscope.
  eapply res_models_or_intro_l; [| exact Hφ].
  apply (proj2 (formula_scoped_or_iff m φ ψ)).
  split; [eapply res_models_fuel_scoped; eauto | exact Hψscope].
Qed.

Lemma res_models_or_intro_r_from_model (m : WfWorldT) (φ ψ : FormulaT) :
  formula_fv φ ⊆ world_dom (m : WorldT) →
  m ⊨ ψ →
  m ⊨ FOr φ ψ.
Proof.
  intros Hφscope Hψ.
  eapply res_models_or_intro_r; [| exact Hψ].
  apply (proj2 (formula_scoped_or_iff m φ ψ)).
  split; [exact Hφscope | eapply res_models_fuel_scoped; eauto].
Qed.

Lemma formula_scoped_star_from_models
    (m m1 m2 : WfWorldT) (φ ψ : FormulaT)
    (Hc : world_compat m1 m2) :
  res_product m1 m2 Hc ⊑ m →
  m1 ⊨ φ →
  m2 ⊨ ψ →
  formula_scoped_in_world m (FStar φ ψ).
Proof.
  intros Hle Hφ Hψ.
  pose proof (res_models_scoped m1 φ Hφ) as Hscopeφ.
  pose proof (res_models_scoped m2 ψ Hψ) as Hscopeψ.
  unfold formula_scoped_in_world in *.
  rewrite formula_fv_star.
  pose proof (raw_le_dom (res_product m1 m2 Hc : WorldT) (m : WorldT) Hle)
    as Hdom.
  intros z Hz. apply elem_of_union in Hz as [Hz | Hz].
  - apply Hdom.
    change (world_dom (res_product m1 m2 Hc : WorldT))
      with (world_dom (m1 : WorldT) ∪ world_dom (m2 : WorldT)).
    set_solver.
  - apply Hdom.
    change (world_dom (res_product m1 m2 Hc : WorldT))
      with (world_dom (m1 : WorldT) ∪ world_dom (m2 : WorldT)).
    set_solver.
Qed.

Lemma res_models_star_intro
    (m m1 m2 : WfWorldT) (φ ψ : FormulaT)
    (Hc : world_compat m1 m2) :
  res_product m1 m2 Hc ⊑ m →
  m1 ⊨ φ →
  m2 ⊨ ψ →
  m ⊨ FStar φ ψ.
Proof.
  intros Hle Hφ Hψ. unfold res_models. simpl.
  split; [eapply formula_scoped_star_from_models; eauto |].
  exists m1, m2, Hc. split; [exact Hle |]. split.
  - models_fuel_irrel Hφ.
  - models_fuel_irrel Hψ.
Qed.

Lemma res_models_star_iff (m : WfWorldT) (φ ψ : FormulaT) :
  (m ⊨ FStar φ ψ ↔
    ∃ (m1 m2 : WfWorldT) (Hc : world_compat m1 m2),
      res_product m1 m2 Hc ⊑ m ∧
      m1 ⊨ φ ∧ m2 ⊨ ψ).
Proof.
  split.
  - unfold res_models. simpl.
    intros [_ [m1 [m2 [Hc [Hle [Hφ Hψ]]]]]].
    exists m1, m2, Hc. repeat split; eauto;
      unfold res_models; models_fuel_irrel_auto.
  - intros [m1 [m2 [Hc [Hle [Hφ Hψ]]]]].
    eapply res_models_star_intro; eauto.
Qed.

Lemma formula_scoped_plus_from_models
    (m m1 m2 : WfWorldT) (φ ψ : FormulaT)
    (Hdef : raw_sum_defined m1 m2) :
  res_sum m1 m2 Hdef ⊑ m →
  m1 ⊨ φ →
  m2 ⊨ ψ →
  formula_scoped_in_world m (FPlus φ ψ).
Proof.
  intros Hle Hφ Hψ.
  pose proof (res_models_scoped m1 φ Hφ) as Hscopeφ.
  pose proof (res_models_scoped m2 ψ Hψ) as Hscopeψ.
  unfold formula_scoped_in_world in *.
  rewrite formula_fv_plus.
  pose proof (raw_le_dom (res_sum m1 m2 Hdef : WorldT) (m : WorldT) Hle)
    as Hdom.
  change (world_dom (m1 : WorldT) = world_dom (m2 : WorldT)) in Hdef.
  change (world_dom (m1 : WorldT) ⊆ world_dom (m : WorldT)) in Hdom.
  intros z Hz. apply elem_of_union in Hz as [Hz | Hz].
  - apply Hdom. exact (Hscopeφ z Hz).
  - apply Hdom. rewrite Hdef. exact (Hscopeψ z Hz).
Qed.

Lemma res_models_plus_intro
    (m m1 m2 : WfWorldT) (φ ψ : FormulaT)
    (Hdef : raw_sum_defined m1 m2) :
  res_sum m1 m2 Hdef ⊑ m →
  m1 ⊨ φ →
  m2 ⊨ ψ →
  m ⊨ FPlus φ ψ.
Proof.
  intros Hle Hφ Hψ. unfold res_models. simpl.
  split; [eapply formula_scoped_plus_from_models; eauto |].
  exists m1, m2, Hdef. split; [exact Hle |]. split.
  - models_fuel_irrel Hφ.
  - models_fuel_irrel Hψ.
Qed.

Lemma res_models_plus_iff (m : WfWorldT) (φ ψ : FormulaT) :
  (m ⊨ FPlus φ ψ ↔
    ∃ (m1 m2 : WfWorldT) (Hdef : raw_sum_defined m1 m2),
      res_sum m1 m2 Hdef ⊑ m ∧
      m1 ⊨ φ ∧ m2 ⊨ ψ).
Proof.
  split.
  - unfold res_models. simpl.
    intros [_ [m1 [m2 [Hdef [Hle [Hφ Hψ]]]]]].
    exists m1, m2, Hdef. repeat split; eauto;
      unfold res_models; models_fuel_irrel_auto.
  - intros [m1 [m2 [Hdef [Hle [Hφ Hψ]]]]].
    eapply res_models_plus_intro; eauto.
Qed.

Lemma res_models_over_intro_same (m : WfWorldT) (φ : FormulaT) :
  formula_scoped_in_world m (FOver φ) →
  m ⊨ φ →
  m ⊨ FOver φ.
Proof.
  unfold res_models.
  simpl. intros Hscope Hφ. split; [exact Hscope |].
  exists m. split; [apply res_subset_refl |].
  models_fuel_irrel Hφ.
Qed.

Lemma res_models_over_intro_same_from_model (m : WfWorldT) (φ : FormulaT) :
  m ⊨ φ →
  m ⊨ FOver φ.
Proof.
  intros Hφ.
  eapply res_models_over_intro_same; [| exact Hφ].
  apply (proj2 (formula_scoped_over_iff m φ)).
  eapply res_models_fuel_scoped; eauto.
Qed.

Lemma res_models_under_intro_same (m : WfWorldT) (φ : FormulaT) :
  formula_scoped_in_world m (FUnder φ) →
  m ⊨ φ →
  m ⊨ FUnder φ.
Proof.
  unfold res_models.
  simpl. intros Hscope Hφ. split; [exact Hscope |].
  exists m. split; [apply res_subset_refl |].
  models_fuel_irrel Hφ.
Qed.

Lemma res_models_under_intro_same_from_model (m : WfWorldT) (φ : FormulaT) :
  m ⊨ φ →
  m ⊨ FUnder φ.
Proof.
  intros Hφ.
  eapply res_models_under_intro_same; [| exact Hφ].
  apply (proj2 (formula_scoped_under_iff m φ)).
  eapply res_models_fuel_scoped; eauto.
Qed.

Lemma res_models_FFibVars_intro (m : WfWorldT) (D : lvset) (φ : FormulaT) :
	  formula_scoped_in_world m (FFibVars D φ) →
	  lc_lvars D →
	  (∀ (σ : Store (V := V)) (mfib : WfWorldT),
	    res_fiber_from_projection m (lvars_fv D) σ mfib →
	    mfib ⊨ formula_msubst_store σ φ) →
	  m ⊨ FFibVars D φ.
Proof.
  unfold res_models.
  simpl. intros Hscope Hlc Hfib. split; [exact Hscope |].
  split; [exact Hlc |].
	  intros σ mfib Hproj.
	  specialize (Hfib σ mfib Hproj).
	  models_fuel_irrel Hfib.
Qed.

End FormulaConnectives.

Ltac normalize_models_ands_in H :=
  repeat rewrite res_models_and_iff in H.

Ltac normalize_models_ands_goal :=
  repeat rewrite res_models_and_iff.

Ltac destruct_models_formula_hyps :=
  repeat match goal with
  | H : res_models _ (FAnd _ _) |- _ =>
      rewrite res_models_and_iff in H; destruct H
  | H : res_models _ _ /\ _ |- _ =>
      destruct H
  | H : _ /\ res_models _ _ |- _ =>
      destruct H
  end.

Ltac split_models_formula_goal :=
  repeat match goal with
  | |- res_models _ (FAnd _ _) =>
      rewrite res_models_and_iff; split
  | |- res_models _ _ /\ _ =>
      split
  | |- _ /\ res_models _ _ =>
      split
  end.

(** * ContextLogic.FormulaConnectives

    Derived proof principles for implication formulas. *)


Section FormulaConnectives.

Context {V : Type} `{ValueSig V}.

Local Notation WorldT := (World (V := V)) (only parsing).
Local Notation WfWorldT := (WfWorld (V := V)) (only parsing).
Local Notation LogicQualifierT := (logic_qualifier (V := V)) (only parsing).
Local Notation FormulaT := (Formula (V := V)) (only parsing).
Local Notation "m ⊨ φ" := (res_models m φ)
  (at level 70, format "m  ⊨  φ").

Lemma res_models_impl_future_iff_local (m : WfWorldT) (φ ψ : FormulaT) :
  formula_scoped_in_world m φ →
  formula_scoped_in_world m ψ →
  ((∀ m', m ⊑ m' →
      m' ⊨ φ →
      m' ⊨ ψ) ↔
   (m ⊨ φ → m ⊨ ψ)).
Proof.
  intros Hφscope Hψscope. split.
  - intros Hfuture Hφ. eapply Hfuture; [reflexivity | exact Hφ].
  - intros Hlocal m' Hle Hφ.
    assert (Hφ_base : m ⊨ φ).
    {
      pose proof (res_models_minimal_on (world_dom (m : WorldT)) m' φ)
        as Hminimal.
      assert (Hfv : formula_fv φ ⊆ world_dom (m : WorldT)).
      { exact Hφscope. }
      specialize (Hminimal Hfv).
      rewrite (res_restrict_eq_of_le m m' Hle) in Hminimal.
      apply (proj1 Hminimal). exact Hφ.
    }
    eapply res_models_kripke; [exact Hle |].
    eauto.
Qed.

Lemma models_impl_future_iff_of_scope
    (m : WfWorldT) (φ ψ : FormulaT) :
  formula_scoped_in_world m (FImpl φ ψ) →
  ((∀ m', m ⊑ m' →
      m' ⊨ φ →
      m' ⊨ ψ) ↔
   (m ⊨ φ → m ⊨ ψ)).
Proof.
  intros Hscope.
  eapply res_models_impl_future_iff_local;
    apply (proj1 (formula_scoped_impl_iff m φ ψ)) in Hscope;
    tauto.
Qed.

Lemma res_models_impl_intro_future (m : WfWorldT) (φ ψ : FormulaT) :
  formula_scoped_in_world m (FImpl φ ψ) →
  (∀ m', m ⊑ m' →
     m' ⊨ φ →
     m' ⊨ ψ) →
  m ⊨ FImpl φ ψ.
Proof.
  unfold res_models.
  simpl. intros Hscope Hfuture. split; [exact Hscope |].
  intros m' Hle Hφ.
  assert (Hφ_model : m' ⊨ φ).
  { unfold res_models. models_fuel_irrel Hφ. }
  pose proof (Hfuture m' Hle Hφ_model) as Hψ.
  models_fuel_irrel Hψ.
Qed.

Lemma res_models_impl_intro (m : WfWorldT) (φ ψ : FormulaT) :
  formula_scoped_in_world m (FImpl φ ψ) →
  (m ⊨ φ → m ⊨ ψ) →
  m ⊨ FImpl φ ψ.
Proof.
  intros Hscope Hlocal.
  eapply res_models_impl_intro_future; [exact Hscope |].
  apply (proj2 (models_impl_future_iff_of_scope
    m φ ψ Hscope)).
  exact Hlocal.
Qed.

Lemma res_models_impl_intro_scoped (m : WfWorldT) (φ ψ : FormulaT) :
  formula_scoped_in_world m φ →
  formula_scoped_in_world m ψ →
  (m ⊨ φ → m ⊨ ψ) →
  m ⊨ FImpl φ ψ.
Proof.
  intros Hφscope Hψscope Hlocal.
  eapply res_models_impl_intro.
  - apply (proj2 (formula_scoped_impl_iff m φ ψ)).
    split; assumption.
  - exact Hlocal.
Qed.

Lemma res_models_impl_elim_future (m n : WfWorldT) (φ ψ : FormulaT) :
  m ⊑ n →
  m ⊨ FImpl φ ψ →
  n ⊨ φ →
  n ⊨ ψ.
Proof.
  intros Hle Himpl Hφ.
  unfold res_models in Himpl.
  simpl in Himpl. destruct Himpl as [_ Himpl].
  assert (Hφ_fuel :
      res_models_fuel (formula_measure φ + formula_measure ψ) n φ).
  { models_fuel_irrel Hφ. }
  pose proof (Himpl n Hle Hφ_fuel) as Hψ.
  unfold res_models. models_fuel_irrel Hψ.
Qed.

Lemma res_models_impl_elim (m : WfWorldT) (φ ψ : FormulaT) :
  m ⊨ FImpl φ ψ →
  m ⊨ φ →
  m ⊨ ψ.
Proof.
  intros Himpl Hφ.
  eapply res_models_impl_elim_future; [reflexivity | exact Himpl | exact Hφ].
Qed.

Lemma res_models_impl2_intro
    (m : WfWorldT) (φ ψ χ : FormulaT) :
  formula_scoped_in_world m (FImpl φ (FImpl ψ χ)) →
  (m ⊨ φ → m ⊨ ψ → m ⊨ χ) →
  m ⊨ FImpl φ (FImpl ψ χ).
Proof.
  intros Hscope Hlocal.
  eapply res_models_impl_intro; [exact Hscope |].
  intros Hφ.
  eapply res_models_impl_intro.
  - eapply formula_scoped_impl_r. exact Hscope.
  - intros Hψ. exact (Hlocal Hφ Hψ).
Qed.

Lemma res_models_impl2_elim
    (m : WfWorldT) (φ ψ χ : FormulaT) :
  m ⊨ FImpl φ (FImpl ψ χ) →
  m ⊨ φ →
  m ⊨ ψ →
  m ⊨ χ.
Proof.
  intros Himpl Hφ Hψ.
  eapply res_models_impl_elim; [| exact Hψ].
  eapply res_models_impl_elim; eauto.
Qed.

Lemma res_models_impl2_map
    (m : WfWorldT)
    (φ1 φ2 ψ1 ψ2 χ1 χ2 : FormulaT) :
  formula_scoped_in_world m (FImpl φ2 (FImpl ψ2 χ2)) →
  (m ⊨ φ2 → m ⊨ φ1) →
  (m ⊨ ψ2 → m ⊨ ψ1) →
  (m ⊨ χ1 → m ⊨ χ2) →
  m ⊨ FImpl φ1 (FImpl ψ1 χ1) →
  m ⊨ FImpl φ2 (FImpl ψ2 χ2).
Proof.
  intros Hscope Hφ Hψ Hχ Himpl.
  eapply res_models_impl2_intro; [exact Hscope |].
  intros Hφ2 Hψ2.
  apply Hχ.
  eapply res_models_impl2_elim; [exact Himpl | |].
  - apply Hφ. exact Hφ2.
  - apply Hψ. exact Hψ2.
Qed.

Lemma res_models_impl2_map_dep
    (m : WfWorldT)
    (φ1 φ2 ψ1 ψ2 χ1 χ2 : FormulaT) :
  formula_scoped_in_world m (FImpl φ2 (FImpl ψ2 χ2)) →
  (m ⊨ φ2 → m ⊨ φ1) →
  (m ⊨ ψ2 → m ⊨ ψ1) →
  (m ⊨ φ2 → m ⊨ ψ2 → m ⊨ χ1 → m ⊨ χ2) →
  m ⊨ FImpl φ1 (FImpl ψ1 χ1) →
  m ⊨ FImpl φ2 (FImpl ψ2 χ2).
Proof.
  intros Hscope Hφ Hψ Hχ Himpl.
  eapply res_models_impl2_intro; [exact Hscope |].
  intros Hφ2 Hψ2.
  eapply Hχ; [exact Hφ2 | exact Hψ2 |].
  eapply res_models_impl2_elim; [exact Himpl | |].
  - apply Hφ. exact Hφ2.
  - apply Hψ. exact Hψ2.
Qed.

End FormulaConnectives.

Ltac use_models_impl H Hout :=
  lazymatch type of H with
  | res_models ?m (FImpl ?p ?q) =>
      let Harg := fresh "Harg" in
      assert (Harg : res_models m p);
      [ | pose proof (res_models_impl_elim m p q H Harg) as Hout;
          clear Harg ]
  | res_models ?m (formula_open ?k ?x (FImpl ?p ?q)) =>
      rewrite formula_open_impl in H;
      use_models_impl H Hout
  end.

(** * ContextLogic.FormulaConnectives

    Derived proof principles for binder-aware wand formulas. *)


Section FormulaConnectives.

Context {V : Type} `{ValueSig V}.

Local Notation WorldT := (World (V := V)) (only parsing).
Local Notation WfWorldT := (WfWorld (V := V)) (only parsing).
Local Notation LogicQualifierT := (logic_qualifier (V := V)) (only parsing).
Local Notation FormulaT := (Formula (V := V)) (only parsing).
Local Notation "m ⊨ φ" := (res_models m φ)
  (at level 70, format "m  ⊨  φ").

Lemma res_models_fbwand_intro (m : WfWorldT) d (φ ψ : FormulaT) :
  formula_scoped_in_world m (FBWand d φ ψ) →
  (exists L : aset,
    ∀ η (m' : WfWorldT)
      (Hc : world_compat m' m),
      open_env_binds d η →
      open_env_atoms η ## L →
      world_dom (res_product m' m Hc : WorldT) =
        world_dom (m : WorldT) ∪ open_env_atoms η →
      m' ⊨ formula_open_env η φ →
      res_product m' m Hc ⊨ formula_open_env η ψ) →
  m ⊨ FBWand d φ ψ.
Proof.
  unfold res_models.
  simpl. intros Hscope [L Hwand]. split; [exact Hscope |].
  exists L.
  intros η m' Hc Hbind Hfresh Hdom Hφ.
  assert (Hφ_model : m' ⊨ formula_open_env η φ).
  { unfold res_models. models_fuel_irrel Hφ. }
  pose proof (Hwand η m' Hc Hbind Hfresh Hdom Hφ_model) as Hψ.
  models_fuel_irrel Hψ.
Qed.

Lemma res_models_fbwand_rev
    (m : WfWorldT) d
    (φ ψ : FormulaT) :
  m ⊨ FBWand d φ ψ ->
  exists L : aset,
    forall (η : gmap nat atom) (m' : WfWorldT)
      (Hc : world_compat m' m),
      open_env_binds d η ->
      open_env_atoms η ## L ->
      world_dom (res_product m' m Hc : WorldT) =
        world_dom (m : WorldT) ∪ open_env_atoms η ->
      m' ⊨ formula_open_env η φ ->
      res_product m' m Hc ⊨ formula_open_env η ψ.
Proof.
  unfold res_models. simpl. intros [_ [L Hwand]].
  exists L.
  intros η m' Hc Hbind Hfresh Hdom Hφ.
  assert (Hφ_fuel :
      res_models_fuel (formula_measure φ + formula_measure ψ) m'
        (formula_open_env η φ)).
  { models_fuel_irrel Hφ. }
  pose proof (Hwand η m' Hc Hbind Hfresh Hdom Hφ_fuel) as Hψ.
  models_fuel_irrel Hψ.
Qed.

(** Reviewer-facing sanity theorem.

    [FBWand] has product-domain semantics: the semantic clause only invokes the
    body when the product of the argument resource and closure resource
    introduces exactly the atoms opened for the binder block.  Reviewers may
    reasonably ask how this relates to the ordinary BI wand rule.  The theorem
    below records that a well-formed [FBWand] supports the usual BI-style use:
    any compatible argument resource that provides the opened binder atoms and
    satisfies the opened antecedent entails the opened consequent on the product
    world.

    This theorem is intentionally not used by type denotation, minimality, or
    Fundamental.  It is metatheory explaining the binder-aware connective, so do
    not delete it as an apparently unused wrapper during cleanup. *)
Theorem res_models_fbwand_bi_of_wf
    (m : WfWorldT) d (φ ψ : FormulaT) :
  formula_wf (FBWand d φ ψ) ->
  m ⊨ FBWand d φ ψ ->
  exists L : aset,
    forall (η : gmap nat atom) (n : WfWorldT)
      (Hc : world_compat n m),
      open_env_binds d η ->
      open_env_atoms η ## L ->
      open_env_atoms η ⊆ world_dom (n : WorldT) ->
      n ⊨ formula_open_env η φ ->
      res_product n m Hc ⊨ formula_open_env η ψ.
Proof.
  intros Hwf Hmodel.
  destruct Hwf as [_ [_ _]].
  pose proof (res_models_scoped _ _ Hmodel) as Hscope.
  pose proof (res_models_fbwand_rev _ _ _ _ Hmodel) as [L Hwand].
  exists (L ∪ world_dom (m : WorldT)).
  intros η n Hc Hbind Hfresh Hηn Hφ.
  set (A := open_env_atoms η).
  set (X := world_dom (m : WorldT) ∪ A).
  assert (Hfresh_L : A ## L) by (subst A; set_solver).
  assert (HφX : formula_fv (formula_open_env η φ) ⊆ X).
  {
    subst X A.
    pose proof (formula_open_env_fv_subset η φ) as Hopen.
    assert (Hφm : formula_fv φ ⊆ world_dom (m : WorldT)).
    {
      intros z Hz. apply Hscope.
      rewrite formula_fv_fbwand.
      rewrite (formula_lvars_at_fv d φ), (formula_lvars_at_fv d ψ).
      set_solver.
    }
    set_solver.
  }
  assert (Hc_small : world_compat (res_restrict n X) m).
  {
    assert (Hc_full : world_compat n (res_restrict m (world_dom (m : WorldT)))).
    {
      rewrite (res_restrict_eq_of_le m m (raw_le_refl m)).
      exact Hc.
    }
    pose proof (world_compat_restrict_overlap n m X (world_dom (m : WorldT))
      (world_dom (m : WorldT)) ltac:(set_solver) Hc_full) as Htmp.
    rewrite (res_restrict_eq_of_le m m (raw_le_refl m)) in Htmp.
    exact Htmp.
  }
  assert (Hdom_small :
      world_dom (res_product (res_restrict n X) m Hc_small : WorldT) =
        world_dom (m : WorldT) ∪ A).
  {
    apply set_eq. intros z.
    change (z ∈ world_dom (res_restrict n X : WorldT) ∪
      world_dom (m : WorldT) ↔
      z ∈ world_dom (m : WorldT) ∪ A).
    rewrite res_restrict_dom.
    subst X A. set_solver.
  }
  assert (Hφ_small :
      res_restrict n X ⊨ formula_open_env η φ).
  {
    apply (proj1 (res_models_minimal_on X n
      (formula_open_env η φ) HφX)).
    exact Hφ.
  }
  pose proof (Hwand η (res_restrict n X) Hc_small
    Hbind Hfresh_L Hdom_small Hφ_small) as Hψ_small.
  eapply res_models_kripke; [| exact Hψ_small].
  eapply res_product_le_mono.
  - apply res_restrict_le.
  - apply raw_le_refl.
Qed.

End FormulaConnectives.

(** * ContextLogic.FormulaConnectives

    Derived proof principles for forall under the extension-based formula
    semantics. *)


Section FormulaConnectives.

Context {V : Type} `{ValueSig V}.

Local Notation WorldT := (World (V := V)) (only parsing).
Local Notation WfWorldT := (WfWorld (V := V)) (only parsing).
Local Notation FormulaT := (Formula (V := V)) (only parsing).
Local Notation "m ⊨ φ" := (res_models m φ)
  (at level 70, format "m  ⊨  φ").

Definition res_extend_by_input_widened_to
    (m : WfWorldT) (F : fiber_extension) (X : aset) (my : WfWorldT) : Prop :=
  ∃ Fwide : fiber_extension,
    F ~>i Fwide ∧
    ext_in Fwide = X ∧
    res_extend_by m Fwide my.

Lemma res_models_forall_intro (m : WfWorldT) (φ : FormulaT) :
  formula_scoped_in_world m (FForall φ) →
  (∃ L : aset,
    ∀ y : atom, y ∉ L →
    ∀ F : fiber_extension,
      ext_in F = formula_fv φ →
      ext_out F = {[y]} →
      ∀ my : WfWorldT,
        res_extend_by m F my →
        my ⊨ formula_open 0 y φ) →
  m ⊨ FForall φ.
Proof.
  unfold res_models.
  simpl. intros Hscope [L Hforall]. split; [exact Hscope |].
  exists L. intros y Hy F HFin HFout my Hext.
  pose proof (Hforall y Hy F HFin HFout my Hext) as Hbody.
  models_fuel_irrel Hbody.
Qed.

Lemma res_models_forall_iff (m : WfWorldT) (φ : FormulaT) :
  formula_scoped_in_world m (FForall φ) →
  (m ⊨ FForall φ ↔
    ∃ L : aset,
      ∀ y : atom, y ∉ L →
      ∀ F : fiber_extension,
        ext_in F = formula_fv φ →
        ext_out F = {[y]} →
        ∀ my : WfWorldT,
          res_extend_by m F my →
          my ⊨ formula_open 0 y φ).
Proof.
  intros Hscope. split.
  - unfold res_models. simpl.
    intros [_ [L Hforall]]. exists L.
    intros y Hy F HFin HFout my Hext.
    specialize (Hforall y Hy F HFin HFout my Hext).
    unfold res_models. models_fuel_irrel Hforall.
  - intros Hforall.
    eapply res_models_forall_intro; eauto.
Qed.

Lemma res_models_forall_rev
    (m : WfWorldT) (φ : FormulaT) :
  m ⊨ FForall φ ->
  exists L : aset,
    forall y : atom, y ∉ L ->
      forall my : WfWorldT,
        world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
        res_restrict my (world_dom (m : WorldT)) = m ->
        my ⊨ formula_open 0 y φ.
Proof.
  intros Hforall.
  pose proof (res_models_scoped m (FForall φ) Hforall) as Hscope.
  pose proof (proj1 (res_models_forall_iff m φ Hscope) Hforall)
    as [L Hbody].
  exists (L ∪ world_dom (m : WorldT)).
  intros y Hy my Hdom Hrestrict.
  assert (HyL : y ∉ L) by set_solver.
  assert (Hym : y ∉ world_dom (m : WorldT)) by set_solver.
  assert (Hfv : formula_fv φ ⊆ world_dom (m : WorldT)).
  { eapply formula_scoped_forall_body. exact Hscope. }
  destruct (forall_extension_from_world_dom_projection
    m my (formula_fv φ) y Hfv Hym Hdom Hrestrict)
    as [F [n [HFin [HFout [Hext Hproj]]]]].
  pose proof (Hbody y HyL F HFin HFout n Hext) as Hn.
  assert (Hopen_fv :
      formula_fv (formula_open 0 y φ) ⊆ formula_fv φ ∪ {[y]}).
  { apply formula_open_fv_subset. }
  apply (proj2 (res_models_minimal_on (formula_fv φ ∪ {[y]}) my
    (formula_open 0 y φ) Hopen_fv)).
  rewrite <- Hproj.
  apply (proj1 (res_models_minimal_on (formula_fv φ ∪ {[y]}) n
    (formula_open 0 y φ) Hopen_fv)).
  exact Hn.
Qed.

Lemma res_models_forall_rev_intro
    (m : WfWorldT) (φ : FormulaT) :
  formula_scoped_in_world m (FForall φ) ->
  (exists L : aset,
    forall y : atom, y ∉ L ->
      forall my : WfWorldT,
        world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
        res_restrict my (world_dom (m : WorldT)) = m ->
        my ⊨ formula_open 0 y φ) ->
  m ⊨ FForall φ.
Proof.
  intros Hscope [L Hfull].
  eapply res_models_forall_intro; [exact Hscope |].
  exists L. intros y Hy F HFin HFout my Hext.
  eapply Hfull; [exact Hy | |].
  - pose proof (res_extend_by_dom m F my Hext) as Hdom.
    unfold ext_out in HFout.
    rewrite Hdom, HFout. reflexivity.
  - eapply res_extend_by_restrict_base; exact Hext.
Qed.

Lemma res_models_forall_full_world_map
    (m : WfWorldT) (φ ψ : FormulaT) :
  (** This is the "full-world" view of [FForall].  The primitive semantics
      only asks extensions to read [formula_fv φ], but nested denotation
      transports often open a formula under several binders and then need to
      compare witnesses whose input domain is the whole current world.  The
      proof converts [FForall φ] to that full-world form with
      [res_models_forall_rev], maps the opened body there, and packages the
      result back with [res_models_forall_rev_intro].  This is intentionally
      independent of any [formula_fv φ = formula_fv ψ] side condition; the
      world-domain restriction/restrict-back hypotheses carry the alignment. *)
  formula_scoped_in_world m (FForall ψ) ->
  (∃ L : aset,
    forall y : atom, y ∉ L ->
      forall my : WfWorldT,
        world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
        res_restrict my (world_dom (m : WorldT)) = m ->
        my ⊨ formula_open 0 y φ ->
        my ⊨ formula_open 0 y ψ) ->
  m ⊨ FForall φ ->
  m ⊨ FForall ψ.
Proof.
  intros Hscope [Lmap Hmap] Hforall.
  destruct (res_models_forall_rev m φ Hforall) as [Lsrc Hsrc].
  eapply res_models_forall_rev_intro; [exact Hscope |].
  exists (Lmap ∪ Lsrc).
  intros y Hy my Hdom Hrestrict.
  eapply Hmap.
  - set_solver.
  - exact Hdom.
  - exact Hrestrict.
  - eapply Hsrc.
    + set_solver.
    + exact Hdom.
    + exact Hrestrict.
Qed.

Lemma res_models_forall_full_world_impl2_map
    (m : WfWorldT)
    (A1 A2 B1 B2 C1 C2 : FormulaT) :
  formula_scoped_in_world m (FForall (FImpl A2 (FImpl B2 C2))) ->
  (∃ L : aset,
    forall y : atom, y ∉ L ->
      forall my : WfWorldT,
        world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
        res_restrict my (world_dom (m : WorldT)) = m ->
        (my ⊨ formula_open 0 y A2 -> my ⊨ formula_open 0 y A1) /\
        (my ⊨ formula_open 0 y B2 -> my ⊨ formula_open 0 y B1) /\
        (my ⊨ formula_open 0 y C1 -> my ⊨ formula_open 0 y C2)) ->
  m ⊨ FForall (FImpl A1 (FImpl B1 C1)) ->
  m ⊨ FForall (FImpl A2 (FImpl B2 C2)).
Proof.
  intros Hscope [L Hmap] Hforall.
  eapply res_models_forall_full_world_map; [exact Hscope | | exact Hforall].
  exists L.
  intros y Hy my Hdom Hrestrict Hopened.
  assert (Htarget_scope :
      formula_scoped_in_world my
        (formula_open 0 y (FImpl A2 (FImpl B2 C2)))).
  {
    eapply formula_scoped_forall_open_res_le.
    - exact Hscope.
    - rewrite <- Hrestrict. apply res_restrict_le.
    - rewrite Hdom. set_solver.
  }
  rewrite !formula_open_impl in Hopened |- *.
  rewrite !formula_open_impl in Htarget_scope.
  destruct (Hmap y Hy my Hdom Hrestrict) as [HA [HB HC]].
  eapply res_models_impl2_map; [| exact HA | exact HB | exact HC | exact Hopened].
  exact Htarget_scope.
Qed.

Lemma res_models_forall_full_world_impl2_map_dep
    (m : WfWorldT)
    (A1 A2 B1 B2 C1 C2 : FormulaT) :
  formula_scoped_in_world m (FForall (FImpl A2 (FImpl B2 C2))) ->
  (∃ L : aset,
    forall y : atom, y ∉ L ->
      forall my : WfWorldT,
        world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
        res_restrict my (world_dom (m : WorldT)) = m ->
        (my ⊨ formula_open 0 y A2 -> my ⊨ formula_open 0 y A1) /\
        (my ⊨ formula_open 0 y B2 -> my ⊨ formula_open 0 y B1) /\
        (my ⊨ formula_open 0 y A2 ->
         my ⊨ formula_open 0 y B2 ->
         my ⊨ formula_open 0 y C1 ->
         my ⊨ formula_open 0 y C2)) ->
  m ⊨ FForall (FImpl A1 (FImpl B1 C1)) ->
  m ⊨ FForall (FImpl A2 (FImpl B2 C2)).
Proof.
  intros Hscope [L Hmap] Hforall.
  eapply res_models_forall_full_world_map; [exact Hscope | | exact Hforall].
  exists L.
  intros y Hy my Hdom Hrestrict Hopened.
  assert (Htarget_scope :
      formula_scoped_in_world my
        (formula_open 0 y (FImpl A2 (FImpl B2 C2)))).
  {
    eapply formula_scoped_forall_open_res_le.
    - exact Hscope.
    - rewrite <- Hrestrict. apply res_restrict_le.
    - rewrite Hdom. set_solver.
  }
  rewrite !formula_open_impl in Hopened |- *.
  rewrite !formula_open_impl in Htarget_scope.
  destruct (Hmap y Hy my Hdom Hrestrict) as [HA [HB HC]].
  eapply res_models_impl2_map_dep; [| exact HA | exact HB | exact HC | exact Hopened].
  exact Htarget_scope.
Qed.

End FormulaConnectives.

(** * ContextLogic.FormulaConnectives

    High-level algebraic properties of the store-free formula semantics. *)


Section FormulaConnectives.

Context {V : Type} `{ValueSig V}.

Local Notation WfWorldT := (WfWorld (V := V)) (only parsing).
Local Notation FormulaT := (Formula (V := V)) (only parsing).

Notation "φ ⊫ ψ" := (entails φ ψ)
  (at level 85, ψ at level 84, no associativity).

(** Over and under remain monotone.  Ordinary forall monotonicity is no longer
    exported as a separate lemma: the extension-form map lemmas are the useful
    interface under the new semantics. *)
Definition ext (φ : FormulaT) : WfWorldT → Prop :=
  λ m, res_models m φ.

Definition over_closure (R : WfWorldT → Prop) : WfWorldT → Prop :=
  λ m', ∃ m, R m ∧ res_subset m m'.

Definition under_closure (R : WfWorldT → Prop) : WfWorldT → Prop :=
  λ m', ∃ m, R m ∧ res_subset m' m.

End FormulaConnectives.
