(** * ContextLogic.FormulaConnectivesHigher

    Higher connective proof principles for implication, FBWand, forall, and
    closure helpers.  The basic connective and fiber lemmas live in
    [FormulaConnectives]. *)

From ContextLogic Require Import FormulaAtom FormulaSemantics FormulaConnectives.
From ContextAlgebra Require Import ResourceInterface ResourceCompat.
From ContextBase Require Import LogicVarOpenEnv.
From Stdlib Require Import Lia Logic.ProofIrrelevance.

(** * ContextLogic.FormulaConnectivesHigher

    Derived proof principles for implication formulas. *)


Section FormulaConnectives.

Context {V : Type} `{ValueSig V}.

Local Notation WorldT := (World (V := V)) (only parsing).
Local Notation WfWorldT := (WfWorld (V := V)) (only parsing).
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

Lemma res_models_impl_map
    (m : WfWorldT)
    (φ1 φ2 ψ1 ψ2 : FormulaT) :
  formula_scoped_in_world m (FImpl φ2 ψ2) →
  (m ⊨ φ2 → m ⊨ φ1) →
  (m ⊨ ψ1 → m ⊨ ψ2) →
  m ⊨ FImpl φ1 ψ1 →
  m ⊨ FImpl φ2 ψ2.
Proof.
  intros Hscope Hφ Hψ Himpl.
  eapply res_models_impl_intro; [exact Hscope |].
  intros Hφ2.
  apply Hψ.
  eapply res_models_impl_elim; [exact Himpl |].
  apply Hφ. exact Hφ2.
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

(** * ContextLogic.FormulaConnectivesHigher

    Derived proof principles for binder-aware wand formulas. *)


Section FormulaConnectives.

Context {V : Type} `{ValueSig V}.

Local Notation WorldT := (World (V := V)) (only parsing).
Local Notation WfWorldT := (WfWorld (V := V)) (only parsing).
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

Lemma res_models_fbwand_open_one_named_fresh
    (m n : WfWorldT) x (φ ψ : FormulaT)
    (Hc : world_compat n m) :
  m ⊨ FBWand 1 φ ψ ->
  x ∉ world_dom (m : WorldT) ->
  world_dom (res_product n m Hc : WorldT) =
    world_dom (m : WorldT) ∪ {[x]} ->
  n ⊨ formula_open 0 x φ ->
  res_product n m Hc ⊨ formula_open 0 x ψ.
Proof.
  intros Hwand Hxm Hdom Harg.
  destruct (res_models_fbwand_rev m 1 φ ψ Hwand) as [L Hrev].
  pose proof (res_models_scoped m (FBWand 1 φ ψ) Hwand) as Hscope.
  pose proof (formula_scoped_fbwand_l m 1 φ ψ Hscope) as Hscope_arg.
  pose proof (formula_scoped_fbwand_r m 1 φ ψ Hscope) as Hscope_res.
  set (y := fresh_for
    (L ∪ world_dom (res_product n m Hc : WorldT) ∪
      formula_fv φ ∪ formula_fv ψ ∪ {[x]})).
  pose proof (fresh_for_not_in
    (L ∪ world_dom (res_product n m Hc : WorldT) ∪
      formula_fv φ ∪ formula_fv ψ ∪ {[x]})) as Hyfresh.
  assert (HyL : y ∉ L) by better_set_solver.
  assert (Hym : y ∉ world_dom (m : WorldT)).
  { intros Hy. apply Hyfresh. rewrite Hdom. better_set_solver. }
  assert (Hyprod : y ∉ world_dom (res_product n m Hc : WorldT))
    by better_set_solver.
  assert (Hxfv_arg : x ∉ formula_fv φ).
  { intros Hbad. exact (Hxm (Hscope_arg x Hbad)). }
  assert (Hyfv_arg : y ∉ formula_fv φ) by better_set_solver.
  assert (Hxfv_res : x ∉ formula_fv ψ).
  { intros Hbad. exact (Hxm (Hscope_res x Hbad)). }
  assert (Hyfv_res : y ∉ formula_fv ψ) by better_set_solver.
  set (η := <[0 := y]> (∅ : gmap nat atom)).
  assert (Hbind : open_env_binds 1 η).
  {
    unfold open_env_binds. split.
    { unfold η. apply open_env_values_inj_singleton. }
    intros k. destruct k as [|k].
    { unfold η. rewrite lookup_insert.
      split; [intros _; eexists; reflexivity | intros _; lia]. }
    unfold η. rewrite lookup_insert_ne by lia. rewrite lookup_empty.
    split; [lia | intros [? Hnone]; inversion Hnone].
  }
  assert (Hatoms : open_env_atoms η = {[y]}).
  {
    unfold η. rewrite open_env_atoms_insert by apply lookup_empty.
    rewrite open_env_atoms_empty. better_set_solver.
  }
  pose proof (world_compat_atom_swap x y n m Hc) as Hc_sw0.
  assert (Hm_sw : res_atom_swap x y m = m).
  { apply res_atom_swap_fresh; assumption. }
  assert (Hc_sw : world_compat (res_atom_swap x y n) m).
  { rewrite <- Hm_sw. exact Hc_sw0. }
  assert (Hprod_sw :
      res_product (res_atom_swap x y n) m Hc_sw =
      res_atom_swap x y (res_product n m Hc)).
  {
    transitivity (res_product (res_atom_swap x y n)
      (res_atom_swap x y m) Hc_sw0).
    - eapply res_product_r_eq. symmetry. exact Hm_sw.
    - apply res_product_atom_swap_eq.
  }
  assert (Hdom_sw :
      world_dom (res_product (res_atom_swap x y n) m Hc_sw : WorldT) =
        world_dom (m : WorldT) ∪ open_env_atoms η).
  {
    rewrite Hprod_sw, world_dom_res_atom_swap, Hdom, Hatoms.
    rewrite set_swap_union.
    rewrite set_swap_fresh by (exact Hxm || exact Hym).
    rewrite set_swap_singleton, swap_l. reflexivity.
  }
  assert (Harg_sw :
      res_atom_swap x y n ⊨ formula_open_env η φ).
  {
    unfold η. rewrite formula_open_env_singleton.
    rewrite <- (formula_atom_swap_open_fresh x y φ)
      by (exact Hxfv_arg || exact Hyfv_arg).
    exact (proj2 (res_models_atom_swap n (formula_open 0 x φ) x y) Harg).
  }
  pose proof (Hrev η (res_atom_swap x y n) Hc_sw Hbind
    ltac:(rewrite Hatoms; better_set_solver) Hdom_sw Harg_sw) as Hres_sw.
  unfold η in Hres_sw. rewrite formula_open_env_singleton in Hres_sw.
  apply (proj1 (res_models_atom_swap (res_product n m Hc)
    (formula_open 0 x ψ) x y)).
  rewrite formula_atom_swap_open_fresh by (exact Hxfv_res || exact Hyfv_res).
  rewrite <- Hprod_sw. exact Hres_sw.
Qed.

End FormulaConnectives.

(** * ContextLogic.FormulaConnectivesHigher

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

Lemma res_models_forall_open_named_fresh
    (m my : WfWorldT) x φ :
  m ⊨ FForall φ ->
  x ∉ world_dom (m : WorldT) ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[x]} ->
  res_restrict my (world_dom (m : WorldT)) = m ->
  my ⊨ formula_open 0 x φ.
Proof.
  intros Hforall Hx Hdom Hrestrict.
  destruct (res_models_forall_rev m φ Hforall) as [L Hrev].
  pose proof (res_models_scoped m (FForall φ) Hforall) as Hscope.
  pose proof (formula_scoped_forall_body m φ Hscope) as Hscope_body.
  set (y := fresh_for (L ∪ world_dom (my : WorldT) ∪ formula_fv φ ∪ {[x]})).
  pose proof (fresh_for_not_in
    (L ∪ world_dom (my : WorldT) ∪ formula_fv φ ∪ {[x]})) as Hyfresh.
  assert (HyL : y ∉ L) by better_set_solver.
  assert (Hym : y ∉ world_dom (m : WorldT)).
  { intros Hym.
    apply Hyfresh.
    rewrite Hdom.
    better_set_solver.
  }
  set (my_y := res_atom_swap x y my).
  assert (Hdom_y :
      world_dom (my_y : WorldT) = world_dom (m : WorldT) ∪ {[y]}).
  {
    unfold my_y.
    rewrite world_dom_res_atom_swap, Hdom, set_swap_union.
    rewrite set_swap_fresh by (exact Hx || exact Hym).
    rewrite set_swap_singleton, swap_l. reflexivity.
  }
  assert (Hrestrict_y : res_restrict my_y (world_dom (m : WorldT)) = m).
  {
    unfold my_y.
    rewrite <- (set_swap_fresh x y (world_dom (m : WorldT))) by
      (exact Hx || exact Hym).
    rewrite res_restrict_atom_swap, Hrestrict.
    apply res_atom_swap_fresh; [exact Hx | exact Hym].
  }
  pose proof (Hrev y HyL my_y Hdom_y Hrestrict_y) as Hbody_y.
  assert (Hxfv : x ∉ formula_fv φ).
  { intros Hbad. exact (Hx (Hscope_body x Hbad)). }
  assert (Hyfv : y ∉ formula_fv φ) by better_set_solver.
  apply (proj1 (res_models_atom_swap my (formula_open 0 x φ) x y)).
  rewrite formula_atom_swap_open_fresh by (exact Hxfv || exact Hyfv).
  exact Hbody_y.
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

Lemma res_models_forall_full_world_impl_map
    (m : WfWorldT)
    (A1 A2 B1 B2 : FormulaT) :
  formula_scoped_in_world m (FForall (FImpl A2 B2)) ->
  (∃ L : aset,
    forall y : atom, y ∉ L ->
      forall my : WfWorldT,
        world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
        res_restrict my (world_dom (m : WorldT)) = m ->
        (my ⊨ formula_open 0 y A2 -> my ⊨ formula_open 0 y A1) /\
        (my ⊨ formula_open 0 y B1 -> my ⊨ formula_open 0 y B2)) ->
  m ⊨ FForall (FImpl A1 B1) ->
  m ⊨ FForall (FImpl A2 B2).
Proof.
  intros Hscope [L Hmap] Hforall.
  eapply res_models_forall_full_world_map; [exact Hscope | | exact Hforall].
  exists L.
  intros y Hy my Hdom Hrestrict Hopened.
  assert (Htarget_scope :
      formula_scoped_in_world my
        (formula_open 0 y (FImpl A2 B2))).
  {
    eapply formula_scoped_forall_open_res_le.
    - exact Hscope.
    - rewrite <- Hrestrict. apply res_restrict_le.
    - rewrite Hdom. set_solver.
  }
  rewrite !formula_open_impl in Hopened |- *.
  rewrite !formula_open_impl in Htarget_scope.
  destruct (Hmap y Hy my Hdom Hrestrict) as [HA HB].
  eapply res_models_impl_map; [| exact HA | exact HB | exact Hopened].
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

(** * ContextLogic.FormulaConnectivesHigher

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

(** * Persistent formulas *)

Section FormulaPersistent.

Context {V : Type} `{ValueSig V}.

Local Notation WfWorldT := (WfWorld (V := V)) (only parsing).
Local Notation WorldT := (World (V := V)) (only parsing).
Local Notation FormulaT := (Formula (V := V)) (only parsing).
Local Notation "m ⊨ φ" := (res_models m φ)
  (at level 70, format "m  ⊨  φ").

Notation "φ ⊫ ψ" := (entails φ ψ)
  (at level 85, ψ at level 84, no associativity).

Definition formula_equiv (φ ψ : FormulaT) : Prop :=
  (φ ⊫ ψ) /\ (ψ ⊫ φ).

Notation "φ ⊣⊢ ψ" := (formula_equiv φ ψ)
  (at level 84, no associativity).

Definition persistent_formula (φ : FormulaT) : Prop :=
  φ ⊫ FPersist φ.

Lemma persist_elim_entails (φ : FormulaT) :
  FPersist φ ⊫ φ.
Proof.
  intros m Hpersist. exact (res_models_persist_elim m φ Hpersist).
Qed.

Lemma persistent_formula_persist (φ : FormulaT) :
  persistent_formula (FPersist φ).
Proof.
  unfold persistent_formula, entails. intros m Hpersist.
  apply res_models_persist_iff in Hpersist
    as [σ [Hdomσ [Hrestrict Hsingle]]].
  eapply res_models_persist_intro with (σ := σ).
  - rewrite formula_fv_persist. exact Hdomσ.
  - rewrite formula_fv_persist. exact Hrestrict.
  - eapply res_models_persist_intro with (σ := σ).
    + exact Hdomσ.
    + rewrite <- Hdomσ.
      change (res_restrict
        (exist _ (singleton_world σ) (wf_singleton_world σ) : WfWorldT)
        (world_dom
          ((exist _ (singleton_world σ) (wf_singleton_world σ) : WfWorldT)
            : WorldT)) =
        (exist _ (singleton_world σ) (wf_singleton_world σ) : WfWorldT)).
      apply res_restrict_eq_of_le. reflexivity.
    + exact Hsingle.
Qed.

Lemma persistent_formula_equiv_persist (φ : FormulaT) :
  persistent_formula φ ->
  φ ⊣⊢ FPersist φ.
Proof.
  intros Hpersist. split.
  - exact Hpersist.
  - apply persist_elim_entails.
Qed.

Lemma persistent_star_and (φ ψ : FormulaT) :
  persistent_formula φ ->
  FStar φ ψ ⊣⊢ FAnd φ ψ.
Proof.
  intros Hpersist. split.
  - intros m Hstar.
    apply res_models_star_iff in Hstar
      as [m1 [m2 [Hc [Hle [Hφ Hψ]]]]].
    apply res_models_and_intro_from_models.
    + eapply res_models_kripke; [| exact Hφ].
      etransitivity; [apply res_product_le_l | exact Hle].
    + eapply res_models_kripke; [| exact Hψ].
      etransitivity; [apply res_product_le_r | exact Hle].
  - intros m Hand.
    apply res_models_and_iff in Hand as [Hφm Hψm].
    pose proof (Hpersist m Hφm) as Hpersistm.
    apply res_models_persist_iff in Hpersistm
      as [σ [Hdomσ [Hrestrict Hφsingle]]].
    pose proof (singleton_projection_compat
      m (formula_fv φ) σ Hdomσ Hrestrict) as Hc.
    eapply res_models_star_intro
      with (m1 := (exist _ (singleton_world σ) (wf_singleton_world σ)
        : WfWorldT)) (m2 := m) (Hc := Hc).
    + rewrite (res_product_singleton_projection_eq
        m (formula_fv φ) σ Hc Hdomσ Hrestrict).
      reflexivity.
    + exact Hφsingle.
    + exact Hψm.
Qed.

Lemma persistent_star_self (φ : FormulaT) :
  persistent_formula φ ->
  FStar φ φ ⊣⊢ φ.
Proof.
  intros Hpersist. split.
  - intros m Hstar.
    pose proof (proj1 (persistent_star_and φ φ Hpersist) m Hstar)
      as Hand.
    apply res_models_and_iff in Hand as [Hφ _]. exact Hφ.
  - intros m Hφ.
    apply (proj2 (persistent_star_and φ φ Hpersist) m).
    apply res_models_and_intro_from_models; exact Hφ.
Qed.

Lemma persistent_formula_and_covered_l (φ ψ : FormulaT) :
  formula_fv φ ⊆ formula_fv ψ ->
  persistent_formula ψ ->
  persistent_formula (FAnd φ ψ).
Proof.
  intros Hfv Hpersist m Hand.
  apply res_models_and_iff in Hand as [Hφ Hψ].
  pose proof (Hpersist m Hψ) as Hpersistψ.
  apply res_models_persist_iff in Hpersistψ
    as [σ [Hdomσ [Hrestrict Hsingleψ]]].
  eapply res_models_persist_intro with (σ := σ).
  - rewrite formula_fv_and. set_solver.
  - rewrite formula_fv_and.
    replace (formula_fv φ ∪ formula_fv ψ) with (formula_fv ψ)
      by set_solver.
    exact Hrestrict.
  - rewrite res_models_and_iff. split.
    + rewrite <- Hrestrict.
      exact (proj1 (res_models_minimal_on (formula_fv ψ) m φ
        ltac:(set_solver)) Hφ).
    + exact Hsingleψ.
Qed.

End FormulaPersistent.
