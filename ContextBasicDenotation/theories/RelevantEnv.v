(** * BasicDenotation.RelevantEnv

    Syntactic relevant-environment support for denotation guards.

    These definitions do not depend on the recursive context-type denotation:
    they only restrict an lvar-keyed type environment to the lvars mentioned by
    a context type and a term. *)

From ContextBasicDenotation Require Import Notation StoreTyping TermOpen
  BasicTypingFormula.
From ContextBase Require Import BaseTactics.

Section RelevantEnv.

Local Notation "m ⊨ φ" := (res_models m φ)
  (at level 70, format "m  ⊨  φ").

Definition lty_env_restrict_lvars (Σ : lty_env) (D : lvset) : lty_env :=
  storeA_restrict Σ D.

Definition denot_relevant_lvars (τ : context_ty) (e : tm) : lvset :=
  context_ty_lvars τ ∪ tm_lvars e.

Definition denot_relevant_env (Σ : lty_env) (τ : context_ty) (e : tm)
    : lty_env :=
  lty_env_restrict_lvars Σ (denot_relevant_lvars τ e).

Lemma denot_relevant_env_dom_subset_direct (Σ : lty_env) τ e :
  dom (denot_relevant_env Σ τ e : lty_env) ⊆
  dom (Σ : gmap logic_var ty).
Proof.
  intros v Hv.
  apply elem_of_dom in Hv as [T Hlookup].
  unfold denot_relevant_env, lty_env_restrict_lvars in Hlookup.
  apply storeA_restrict_lookup_some in Hlookup as [_ Hlookup].
  eapply elem_of_dom_2. exact Hlookup.
Qed.

Lemma denot_relevant_env_lookup_mono_context
    (Σ : lty_env) τsmall τbig e v T :
  context_ty_lvars τsmall ⊆ context_ty_lvars τbig ->
  denot_relevant_env Σ τsmall e !! v = Some T ->
  denot_relevant_env Σ τbig e !! v = Some T.
Proof.
  intros Hτ Hlookup.
  unfold denot_relevant_env, lty_env_restrict_lvars,
    denot_relevant_lvars in Hlookup |- *.
  apply storeA_restrict_lookup_some in Hlookup as [Hv HΣ].
  apply storeA_restrict_lookup_some_2; [exact HΣ | set_solver].
Qed.

Lemma denot_relevant_env_dom_mono_context
    (Σ : lty_env) τsmall τbig e :
  context_ty_lvars τsmall ⊆ context_ty_lvars τbig ->
  dom (denot_relevant_env Σ τsmall e) ⊆
  dom (denot_relevant_env Σ τbig e).
Proof.
  intros Hτ v Hv.
  apply elem_of_dom in Hv as [T Hlookup].
  apply elem_of_dom. exists T.
  eapply denot_relevant_env_lookup_mono_context; eauto.
Qed.

Lemma basic_world_formula_denot_relevant_mono_context
    (Σ : lty_env) τsmall τbig e (m : WfWorldT) :
  context_ty_lvars τsmall ⊆ context_ty_lvars τbig ->
  m ⊨ basic_world_formula (denot_relevant_env Σ τbig e) ->
  m ⊨ basic_world_formula (denot_relevant_env Σ τsmall e).
Proof.
  intros Hτ Hworld.
  apply basic_world_formula_models_iff in Hworld
    as [Hlc_big [Hscope_big Htyped_big]].
  apply basic_world_formula_models_iff.
  pose proof (denot_relevant_env_dom_mono_context Σ τsmall τbig e Hτ)
    as Hdom.
  split.
  - intros v Hv. apply Hlc_big. exact (Hdom v Hv).
  - split.
    + intros a Ha.
      apply Hscope_big.
      apply lvars_fv_elem in Ha.
      apply lvars_fv_elem. exact (Hdom (LVFree a) Ha).
    + unfold lworld_has_type, worldA_has_type in Htyped_big |- *.
      destruct Htyped_big as [Hdom_big Hstores_big].
      split.
      * intros v Hv. apply Hdom_big. exact (Hdom v Hv).
      * intros σ Hσ v T val HΣv Hσv.
        eapply Hstores_big; [exact Hσ| |exact Hσv].
        eapply denot_relevant_env_lookup_mono_context; eauto.
Qed.

Lemma denot_relevant_lvars_open k y τ e :
  y ∉ fv_tm e ->
  lvars_open k y (denot_relevant_lvars τ e) =
  denot_relevant_lvars (cty_open k y τ) (open_tm k (vfvar y) e).
Proof.
  intros Hy.
  unfold denot_relevant_lvars.
  rewrite lvars_open_union.
  rewrite cty_open_vars.
  rewrite tm_lvars_open by exact Hy.
  reflexivity.
Qed.

Lemma denot_relevant_env_open_one k y Σ τ e :
  y ∉ fv_tm e ->
  lty_env_open_one k y (denot_relevant_env Σ τ e) =
  denot_relevant_env (lty_env_open_one k y Σ)
    (cty_open k y τ) (open_tm k (vfvar y) e).
Proof.
  intros Hy.
  unfold denot_relevant_env, lty_env_restrict_lvars, lty_env_open_one.
  rewrite <- denot_relevant_lvars_open by exact Hy.
  symmetry. apply storeA_restrict_swap.
Qed.

Lemma denot_relevant_lvars_open_env η τ e :
  open_env_fresh_for_lvars η (denot_relevant_lvars τ e) ->
  denot_relevant_lvars (open_cty_env η τ) (open_tm_env η e) =
  lvars_open_env η (denot_relevant_lvars τ e).
Proof.
  intros Hfresh.
  unfold denot_relevant_lvars.
  rewrite context_ty_lvars_open_cty_env.
  2:{
    apply (open_env_fresh_for_lvars_mono η
      (context_ty_lvars τ) (denot_relevant_lvars τ e)).
    - unfold denot_relevant_lvars. set_solver.
    - exact Hfresh.
  }
  rewrite tm_lvars_open_tm_env.
  2:{
    apply (open_env_fresh_for_lvars_mono η
      (tm_lvars e) (denot_relevant_lvars τ e)).
    - unfold denot_relevant_lvars. set_solver.
    - exact Hfresh.
  }
  better_base_solver.
Qed.

Lemma denot_relevant_env_open_env η Σ τ e :
  open_env_fresh_for_lvars η (dom Σ ∪ denot_relevant_lvars τ e) ->
  open_env_values_inj η ->
  lty_env_open_lvars η (denot_relevant_env Σ τ e) =
  denot_relevant_env (lty_env_open_lvars η Σ)
    (open_cty_env η τ) (open_tm_env η e).
Proof.
  revert Σ τ e.
  induction η as [|k x η Hnone Hfold IH] using fin_maps.map_fold_ind.
  - intros Σ τ e _ _.
    rewrite lty_env_open_lvars_empty, open_cty_env_empty.
    rewrite (lty_env_open_lvars_empty Σ).
    rewrite map_fold_empty. reflexivity.
  - intros Σ τ e Hfresh Hinj.
    pose proof (open_env_values_inj_insert_inv η k x Hnone Hinj)
      as [Hinjη Havoid].
    assert (Hfreshη :
      open_env_fresh_for_lvars η (dom Σ ∪ denot_relevant_lvars τ e)).
    { eapply open_env_fresh_for_lvars_insert_tail; eassumption. }
    rewrite lty_env_open_lvars_insert_fresh.
    2: exact Hnone.
    2: exact Havoid.
    2:{
      eapply open_env_fresh_for_lvars_mono; [|exact Hfresh].
      unfold denot_relevant_env, lty_env_restrict_lvars.
      intros v Hv.
      apply elem_of_dom in Hv as [Tv Hlook].
      apply storeA_restrict_lookup_some in Hlook as [Hvrel HΣv].
      apply elem_of_union.
      left. eapply elem_of_dom_2. exact HΣv.
    }
    rewrite IH by (exact Hfreshη || exact Hinjη).
    rewrite open_cty_env_insert_fresh by (exact Hnone || exact Havoid || exact Hinjη).
    rewrite open_tm_env_insert_fresh_plain by exact Hnone.
    rewrite lty_env_open_lvars_insert_fresh.
    2: exact Hnone.
    2: exact Havoid.
    2:{
      eapply open_env_fresh_for_lvars_mono; [|exact Hfresh].
      intros v Hv. set_solver.
    }
    rewrite denot_relevant_env_open_one.
    + reflexivity.
    + rewrite <- tm_lvars_fv.
      rewrite tm_lvars_open_tm_env.
      * pose proof (open_env_fresh_for_lvars_insert_head η k x
          (dom Σ ∪ denot_relevant_lvars τ e) Hnone Hfresh) as Hhead.
        intros Hbad. apply Hhead.
        eapply lvars_fv_mono; [|exact Hbad].
        apply lvars_open_env_mono.
        unfold denot_relevant_lvars. set_solver.
      * eapply open_env_fresh_for_lvars_mono; [|exact Hfreshη].
        unfold denot_relevant_lvars. set_solver.
Qed.

Lemma lty_env_restrict_lvars_closed Σ D :
  lty_env_closed Σ ->
  lty_env_closed (lty_env_restrict_lvars Σ D).
Proof.
  intros Hclosed.
  unfold lty_env_closed in *.
  intros v Hv.
  unfold lty_env_restrict_lvars in Hv.
  pose proof (storeA_restrict_dom (Σ : lty_env) D) as Hdom_restrict.
  rewrite Hdom_restrict in Hv.
  apply elem_of_intersection in Hv as [Hv _].
  exact (Hclosed v Hv).
Qed.

Lemma denot_relevant_env_closed Σ τ e :
  lty_env_closed Σ ->
  lty_env_closed (denot_relevant_env Σ τ e).
Proof.
  apply lty_env_restrict_lvars_closed.
Qed.

Lemma lty_env_to_atom_env_restrict_lvars_lookup Σ D x :
  LVFree x ∈ D ->
  lty_env_to_atom_env (lty_env_restrict_lvars Σ D) !! x =
  lty_env_to_atom_env Σ !! x.
Proof.
  intros HxD.
  rewrite !lvar_store_to_atom_store_lookup.
  unfold lty_env_restrict_lvars.
  destruct ((Σ : gmap logic_var ty) !! LVFree x) as [T|] eqn:HΣ.
  - apply storeA_restrict_lookup_some_2; assumption.
  - apply storeA_restrict_lookup_none_l. exact HΣ.
Qed.

Lemma basic_typing_lty_env_to_atom_env_restrict_lvars Σ D e T :
  tm_lvars e ⊆ D ->
  lty_env_to_atom_env Σ ⊢ₑ e ⋮ T ->
  lty_env_to_atom_env (lty_env_restrict_lvars Σ D) ⊢ₑ e ⋮ T.
Proof.
  intros Hsub Hty.
  eapply basic_typing_env_agree_tm; [exact Hty |].
  intros x Hx.
  apply lty_env_to_atom_env_restrict_lvars_lookup.
  apply Hsub.
  apply lvars_fv_elem.
  rewrite tm_lvars_fv. exact Hx.
Qed.

Lemma basic_typing_lty_env_to_atom_env_denot_relevant_env Σ τ e T :
  lty_env_to_atom_env Σ ⊢ₑ e ⋮ T ->
  lty_env_to_atom_env (denot_relevant_env Σ τ e) ⊢ₑ e ⋮ T.
Proof.
  intros Hty.
  unfold denot_relevant_env, denot_relevant_lvars.
  eapply basic_typing_lty_env_to_atom_env_restrict_lvars; [|exact Hty].
  set_solver.
Qed.

Lemma lty_env_restrict_lvars_fv_subset Σ D :
  lvars_fv (dom (lty_env_restrict_lvars Σ D)) ⊆ lvars_fv D.
Proof.
  unfold lty_env_restrict_lvars.
  rewrite storeA_restrict_dom.
  apply lvars_fv_mono. set_solver.
Qed.

Lemma lty_env_restrict_lvars_fv_dom_subset Σ D :
  lvars_fv (dom (lty_env_restrict_lvars Σ D)) ⊆ lvars_fv (dom Σ).
Proof.
  unfold lty_env_restrict_lvars.
  rewrite storeA_restrict_dom.
  apply lvars_fv_mono. set_solver.
Qed.

Lemma lty_env_restrict_lvars_insert_fresh Σ D x T :
  LVFree x ∉ D ->
  lty_env_restrict_lvars (<[LVFree x := T]> Σ) D =
  lty_env_restrict_lvars Σ D.
Proof.
  intros HxD.
  unfold lty_env_restrict_lvars.
  apply storeA_restrict_insert_notin. exact HxD.
Qed.

Lemma denot_relevant_env_fv_subset Σ τ e :
  lvars_fv (dom (denot_relevant_env Σ τ e)) ⊆
  fv_cty τ ∪ fv_tm e.
Proof.
  unfold denot_relevant_env, denot_relevant_lvars.
  transitivity (lvars_fv (context_ty_lvars τ ∪ tm_lvars e)).
  - apply lty_env_restrict_lvars_fv_subset.
  - rewrite lvars_fv_union, context_ty_lvars_fv, tm_lvars_fv.
    set_solver.
Qed.

Lemma denot_relevant_env_eq_of_tm_lvars_eq
    (Σ : lty_env) τ e e' :
  tm_lvars e = tm_lvars e' ->
  denot_relevant_env Σ τ e = denot_relevant_env Σ τ e'.
Proof.
  intros Heq.
  unfold denot_relevant_env, denot_relevant_lvars, lty_env_restrict_lvars.
  rewrite Heq. reflexivity.
Qed.

Lemma denot_relevant_basic_world_typing_wfworld_closed_on_term_of_lvars_eq
    (Σ : lty_env) τ e_src e_tgt (m : WfWorldT) :
  tm_lvars e_tgt = tm_lvars e_src ->
  m ⊨ basic_world_formula (denot_relevant_env Σ τ e_src) ->
  m ⊨ expr_basic_typing_formula
    (denot_relevant_env Σ τ e_src) e_src (erase_ty τ) ->
  wfworld_closed_on (fv_tm e_tgt) m.
Proof.
  intros Hlvars Hworld Hbasic.
  eapply basic_world_formula_wfworld_closed_on_atoms; [|exact Hworld].
  unfold denot_relevant_env, denot_relevant_lvars, lty_env_restrict_lvars.
  rewrite storeA_restrict_dom.
  intros v Hv.
  unfold lvars_of_atoms in Hv.
  apply elem_of_map in Hv as [a [-> Ha]].
  apply elem_of_intersection. split.
  - pose proof (expr_basic_typing_formula_basic_ltype _ _ _ _ Hbasic)
      as [Hsub _].
    assert (Ha_lvars : LVFree a ∈ tm_lvars e_src).
    {
      rewrite <- Hlvars.
      apply lvars_fv_elem. rewrite tm_lvars_fv. exact Ha.
    }
    specialize (Hsub _ Ha_lvars).
    unfold denot_relevant_env, denot_relevant_lvars,
      lty_env_restrict_lvars in Hsub.
    rewrite storeA_restrict_dom in Hsub.
    apply elem_of_intersection in Hsub as [HaΣ _].
    exact HaΣ.
  - apply elem_of_union_r.
    rewrite <- Hlvars.
    apply lvars_fv_elem. rewrite tm_lvars_fv. exact Ha.
Qed.

Lemma denot_relevant_basic_world_typing_wfworld_closed_on_term
    (Σ : lty_env) τ e (m : WfWorldT) :
  m ⊨ basic_world_formula (denot_relevant_env Σ τ e) ->
  m ⊨ expr_basic_typing_formula
    (denot_relevant_env Σ τ e) e (erase_ty τ) ->
  wfworld_closed_on (fv_tm e) m.
Proof.
  eapply denot_relevant_basic_world_typing_wfworld_closed_on_term_of_lvars_eq.
  reflexivity.
Qed.

Lemma denot_relevant_lvars_insert_fresh x τ e :
  LVFree x ∉ context_ty_lvars τ ->
  x ∉ fv_tm e ->
  LVFree x ∉ denot_relevant_lvars τ e.
Proof.
  intros Hxτ Hxe.
  unfold denot_relevant_lvars.
  pose proof (tm_lvars_free_notin_of_fv x e Hxe).
  set_solver.
Qed.

Lemma denot_relevant_env_insert_fresh Σ τ e x T :
  LVFree x ∉ context_ty_lvars τ ->
  x ∉ fv_tm e ->
  denot_relevant_env (<[LVFree x := T]> Σ) τ e =
  denot_relevant_env Σ τ e.
Proof.
  intros Hxτ Hxe.
  unfold denot_relevant_env, lty_env_restrict_lvars.
  apply storeA_restrict_insert_notin.
  apply denot_relevant_lvars_insert_fresh; assumption.
Qed.

Lemma lty_env_restrict_lvars_insert_denot_relevant_env_eq
    Σ τ e X y T :
  X ∖ {[LVFree y]} ⊆ denot_relevant_lvars τ e ->
  lty_env_restrict_lvars
    (<[LVFree y := T]> (denot_relevant_env Σ τ e)) X =
  lty_env_restrict_lvars (<[LVFree y := T]> Σ) X.
Proof.
  intros Hsub.
  unfold lty_env_restrict_lvars, denot_relevant_env.
  apply storeA_map_eq. intros v.
  change ((storeA_restrict
    (<[LVFree y := T]>
      (storeA_restrict (Σ : gmap logic_var ty) (denot_relevant_lvars τ e)
        : gmap logic_var ty)) X : gmap logic_var ty) !! v =
    (storeA_restrict (<[LVFree y := T]> (Σ : gmap logic_var ty)) X
      : gmap logic_var ty) !! v).
  rewrite (storeA_restrict_lookup
    (<[LVFree y := T]>
      (storeA_restrict (Σ : gmap logic_var ty) (denot_relevant_lvars τ e)
        : gmap logic_var ty)) X v).
  rewrite (storeA_restrict_lookup
    (<[LVFree y := T]> (Σ : gmap logic_var ty)) X v).
  destruct (decide (v ∈ X)) as [HvX|HvX]; [|reflexivity].
  destruct (decide (v = LVFree y)) as [->|Hvy].
  - rewrite !lookup_insert_eq. reflexivity.
  - rewrite !lookup_insert_ne by congruence.
    unfold lty_env_restrict_lvars.
    rewrite storeA_restrict_lookup.
    destruct (decide (v ∈ denot_relevant_lvars τ e)) as [_|Hvrel].
    + reflexivity.
    + exfalso. apply Hvrel. apply Hsub. set_solver.
Qed.

End RelevantEnv.
