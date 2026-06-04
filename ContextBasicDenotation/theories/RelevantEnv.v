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

Lemma denot_relevant_lvars_fv τ e :
  lvars_fv (denot_relevant_lvars τ e) = fv_cty τ ∪ fv_tm e.
Proof.
  unfold denot_relevant_lvars.
  rewrite lvars_fv_union, context_ty_lvars_fv, tm_lvars_fv.
  set_solver.
Qed.

Lemma denot_relevant_env_empty (Σ : lty_env) τ e :
  denot_relevant_lvars τ e = (∅ : lvset) ->
  denot_relevant_env Σ τ e = (∅ : lty_env).
Proof.
  intros Hempty.
  unfold denot_relevant_env, lty_env_restrict_lvars.
  rewrite Hempty.
  apply storeA_restrict_empty_set.
Qed.

Lemma denot_relevant_env_fresh_free (Σ : lty_env) τ e x :
  x ∉ fv_cty τ ->
  x ∉ fv_tm e ->
  LVFree x ∉ dom (denot_relevant_env Σ τ e : lty_env).
Proof.
  intros Hxτ Hxe Hbad.
  unfold denot_relevant_env, lty_env_restrict_lvars in Hbad.
  rewrite storeA_restrict_dom in Hbad.
  apply elem_of_intersection in Hbad as [_ Hrel].
  apply lvars_fv_elem in Hrel.
  rewrite denot_relevant_lvars_fv in Hrel.
  set_solver.
Qed.

Lemma denot_relevant_env_arrow_fresh_free
    (Σ : lty_env) τx τr e x :
  x ∉ fv_cty τx ->
  x ∉ fv_cty τr ->
  x ∉ fv_tm e ->
  LVFree x ∉ dom (denot_relevant_env Σ (CTArrow τx τr) e : lty_env).
Proof.
  intros Hxτx Hxτr Hxe.
  apply denot_relevant_env_fresh_free; [|exact Hxe].
  unfold fv_cty, context_ty_lvars.
  cbn [context_ty_lvars_at].
  rewrite lvars_fv_union, !context_ty_lvars_fv_at.
  set_solver.
Qed.

Lemma denot_relevant_env_wand_fresh_free
    (Σ : lty_env) τx τr e x :
  x ∉ fv_cty τx ->
  x ∉ fv_cty τr ->
  x ∉ fv_tm e ->
  LVFree x ∉ dom (denot_relevant_env Σ (CTWand τx τr) e : lty_env).
Proof.
  intros Hxτx Hxτr Hxe.
  change (denot_relevant_env Σ (CTWand τx τr) e)
    with (denot_relevant_env Σ (CTArrow τx τr) e).
  eapply denot_relevant_env_arrow_fresh_free; eauto.
Qed.

Lemma lvars_of_atoms_empty :
  lvars_of_atoms (∅ : aset) = (∅ : lvset).
Proof.
  unfold lvars_of_atoms.
  rewrite set_map_empty. reflexivity.
Qed.

Lemma denot_relevant_lvars_basic_ret_fvar_subset x τ :
  basic_context_ty ∅ τ ->
  denot_relevant_lvars τ (tret (vfvar x)) ⊆ {[LVFree x]}.
Proof.
  intros Hbasic v Hv.
  pose proof (basic_context_ty_to_lvars _ _ Hbasic) as [Hτ _].
  rewrite lvars_of_atoms_empty in Hτ.
  unfold denot_relevant_lvars in Hv.
  cbn [tm_lvars tm_lvars_at value_lvars_at lvar_value_keys] in Hv.
  set_solver.
Qed.

Lemma denot_relevant_lvars_ret_fvar_subset_singleton x τ :
  basic_context_ty {[x]} τ ->
  denot_relevant_lvars τ (tret (vfvar x)) ⊆ {[LVFree x]}.
Proof.
  intros Hbasic v Hv.
  pose proof (basic_context_ty_to_lvars _ _ Hbasic) as [Hτ _].
  unfold denot_relevant_lvars in Hv.
  cbn [tm_lvars tm_lvars_at value_lvars_at lvar_value_keys] in Hv.
  unfold lvars_of_atoms in Hτ.
  set_solver.
Qed.

Lemma denot_relevant_lvars_basic_open_tprim_fvar_subset op x τ :
  basic_context_ty ∅ τ ->
  denot_relevant_lvars ({0 ~> x} τ) (tprim op (vfvar x)) ⊆ {[LVFree x]}.
Proof.
  intros Hbasic v Hv.
  pose proof (basic_context_ty_to_lvars _ _ Hbasic) as [Hτ _].
  rewrite lvars_of_atoms_empty in Hτ.
  assert (Hempty : context_ty_lvars τ = (∅ : lvset)) by set_solver.
  unfold denot_relevant_lvars in Hv.
  rewrite cty_open_vars in Hv.
  unfold context_ty_open_lvars in Hv.
  rewrite Hempty, set_swap_empty in Hv.
  cbn [tm_lvars tm_lvars_at value_lvars_at lvar_value_keys] in Hv.
  set_solver.
Qed.

Lemma atom_env_to_lty_env_restrict_singleton_lookup_eq
    (Δ1 Δ2 : gmap atom ty) x T :
  Δ1 !! x = Some T ->
  Δ2 !! x = Some T ->
  lty_env_restrict_lvars (atom_env_to_lty_env Δ1) ({[LVFree x]}) =
  lty_env_restrict_lvars (atom_env_to_lty_env Δ2) ({[LVFree x]}).
Proof.
  intros Hlookup1 Hlookup2.
  unfold lty_env_restrict_lvars.
  rewrite (storeA_restrict_singleton_lookup
    (atom_env_to_lty_env Δ1 : gmap logic_var ty) (LVFree x) T).
  2:{ rewrite atom_store_to_lvar_store_lookup_free. exact Hlookup1. }
  rewrite (storeA_restrict_singleton_lookup
    (atom_env_to_lty_env Δ2 : gmap logic_var ty) (LVFree x) T).
  2:{ rewrite atom_store_to_lvar_store_lookup_free. exact Hlookup2. }
  reflexivity.
Qed.

Lemma atom_env_to_lty_env_restrict_singleton_lookup
    (Δ : gmap atom ty) x T :
  Δ !! x = Some T ->
  lty_env_restrict_lvars (atom_env_to_lty_env Δ) ({[LVFree x]}) =
  lty_env_restrict_lvars
    (atom_env_to_lty_env (<[x := T]> (∅ : gmap atom ty))) ({[LVFree x]}).
Proof.
  intros Hlookup.
  eapply (atom_env_to_lty_env_restrict_singleton_lookup_eq
    Δ (<[x := T]> (∅ : gmap atom ty)) x T);
    [exact Hlookup|].
  exact (map_lookup_insert (∅ : gmap atom ty) x T).
Qed.

Lemma atom_env_to_lty_env_insert_restrict_singleton
    (Δ : gmap atom ty) x T :
  lty_env_restrict_lvars (atom_env_to_lty_env (<[x := T]> Δ))
    ({[LVFree x]}) =
  lty_env_restrict_lvars
    (atom_env_to_lty_env (<[x := T]> (∅ : gmap atom ty))) ({[LVFree x]}).
Proof.
  apply atom_env_to_lty_env_restrict_singleton_lookup.
  apply map_lookup_insert.
Qed.

Lemma atom_env_to_lty_env_dom_free_notin
    (Δ : gmap atom ty) x :
  x ∉ dom Δ ->
  LVFree x ∉ dom (atom_env_to_lty_env Δ).
Proof.
  intros Hx Hbad.
  rewrite atom_store_to_lvar_store_dom in Hbad.
  unfold lvars_of_atoms in Hbad.
  apply elem_of_map in Hbad as [y [Heq Hy]].
  inversion Heq. subst y.
  exact (Hx Hy).
Qed.

Lemma basic_world_formula_atom_env_dom_subset
    (Δ : gmap atom ty) (m : WfWorldT) :
  m ⊨ basic_world_formula (atom_env_to_lty_env Δ) ->
  dom Δ ⊆ world_dom (m : WorldT).
Proof.
  intros Hworld.
  apply basic_world_formula_models_iff in Hworld as [_ [Hdom _]].
  rewrite atom_store_to_lvar_store_dom, lvars_fv_of_atoms in Hdom.
  exact Hdom.
Qed.

Lemma atom_env_to_lty_env_erase_ctx_union_subenv
    (Σ : gmap atom ty) Γ v T :
  basic_ctx (dom Σ) Γ ->
  atom_env_to_lty_env (erase_ctx Γ) !! v = Some T ->
  atom_env_to_lty_env (Σ ∪ erase_ctx Γ) !! v = Some T.
Proof.
  intros Hbasic Hlook.
  pose proof (basic_ctx_erase_dom (dom Σ) Γ Hbasic) as HdomΓ.
  pose proof (basic_ctx_dom_fresh (dom Σ) Γ Hbasic) as HfreshΓ.
  destruct v as [k|x].
  - rewrite atom_store_to_lvar_store_lookup_bound_none in Hlook.
    discriminate.
  - rewrite atom_store_to_lvar_store_lookup_free in Hlook.
    rewrite atom_store_to_lvar_store_lookup_free.
    apply map_lookup_union_Some_raw. right.
    split; [|exact Hlook].
    apply not_elem_of_dom.
    apply elem_of_dom_2 in Hlook.
    rewrite HdomΓ in Hlook.
    better_set_solver.
Qed.

Lemma erase_ctx_union_lookup_local_of_basic_ctx
    (Σ : gmap atom ty) Γ x :
  basic_ctx (dom Σ) Γ ->
  x ∈ dom (erase_ctx Γ) ->
  (erase_ctx Γ : gmap atom ty) !! x =
  (Σ ∪ erase_ctx Γ : gmap atom ty) !! x.
Proof.
  intros Hbasic HxΓ.
  pose proof (basic_ctx_erase_dom (dom Σ) Γ Hbasic) as HdomΓ.
  pose proof (basic_ctx_dom_fresh (dom Σ) Γ Hbasic) as HfreshΓ.
  symmetry.
  apply lookup_union_r.
  apply not_elem_of_dom. intros HxΣ.
  rewrite HdomΓ in HxΓ.
  better_set_solver.
Qed.

Lemma denot_relevant_env_erase_ctx_union_subenv
    (Σ : gmap atom ty) Γ τ e v T :
  basic_ctx (dom Σ) Γ ->
  denot_relevant_env (atom_env_to_lty_env (erase_ctx Γ)) τ e !! v = Some T ->
  atom_env_to_lty_env (Σ ∪ erase_ctx Γ) !! v = Some T.
Proof.
  intros Hbasic Hlook.
  unfold denot_relevant_env, lty_env_restrict_lvars in Hlook.
  apply storeA_restrict_lookup_some in Hlook as [_ Hlook].
  eapply atom_env_to_lty_env_erase_ctx_union_subenv; eauto.
Qed.

Lemma lty_env_singleton_subenv_denot_relevant_env_ret_fvar
    (Σ : lty_env) τ y T v U :
  (<[LVFree y := T]> (∅ : lty_env)) !! v = Some U ->
  denot_relevant_env (<[LVFree y := T]> Σ) τ (tret (vfvar y)) !! v = Some U.
Proof.
  intros Hv.
  change (((<[LVFree y := T]> (∅ : gmap logic_var ty))
    : gmap logic_var ty) !! v = Some U) in Hv.
  destruct v as [k|z].
  - rewrite lookup_insert_ne in Hv by discriminate.
    rewrite lookup_empty in Hv. discriminate.
  - destruct (decide (z = y)) as [->|Hzy].
    + change ((<[LVFree y := T]> (∅ : gmap logic_var ty) : gmap logic_var ty)
          !! LVFree y = Some U) in Hv.
      rewrite lookup_insert_eq in Hv. inversion Hv. subst U.
      unfold denot_relevant_env, lty_env_restrict_lvars.
      apply storeA_restrict_lookup_some_2.
      * apply map_lookup_insert.
      * unfold denot_relevant_lvars.
        cbn [tm_lvars tm_lvars_at value_lvars value_lvars_at].
        set_solver.
    + rewrite lookup_insert_ne in Hv by congruence.
      rewrite lookup_empty in Hv. discriminate.
Qed.

Lemma lty_env_restrict_lvars_twice_same (Σ : lty_env) D :
  lty_env_restrict_lvars (lty_env_restrict_lvars Σ D) D =
  lty_env_restrict_lvars Σ D.
Proof.
  unfold lty_env_restrict_lvars.
  apply storeA_restrict_twice_same.
Qed.

Lemma lty_env_restrict_lvars_twice_subset (Σ : lty_env) X Y :
  Y ⊆ X ->
  lty_env_restrict_lvars (lty_env_restrict_lvars Σ X) Y =
  lty_env_restrict_lvars Σ Y.
Proof.
  intros HYX.
  unfold lty_env_restrict_lvars.
  apply storeA_restrict_twice_subset. exact HYX.
Qed.

Lemma denot_relevant_env_idemp (Σ : lty_env) τ e :
  denot_relevant_env (denot_relevant_env Σ τ e) τ e =
  denot_relevant_env Σ τ e.
Proof.
  unfold denot_relevant_env.
  apply lty_env_restrict_lvars_twice_same.
Qed.

Lemma denot_relevant_env_restrict_subset (Σ : lty_env) τ e X :
  X ⊆ denot_relevant_lvars τ e ->
  lty_env_restrict_lvars (denot_relevant_env Σ τ e) X =
  lty_env_restrict_lvars Σ X.
Proof.
  unfold denot_relevant_env.
  apply lty_env_restrict_lvars_twice_subset.
Qed.

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

Lemma basic_context_ty_lvars_denot_relevant_env Σ τ e :
  basic_context_ty_lvars (dom Σ) τ ->
  basic_context_ty_lvars (dom (denot_relevant_env Σ τ e)) τ.
Proof.
  intros [Hvars Hshape]. split; [|exact Hshape].
  intros v Hv.
  unfold denot_relevant_env, lty_env_restrict_lvars, denot_relevant_lvars.
  rewrite storeA_restrict_dom.
  apply elem_of_intersection. split; [apply Hvars; exact Hv|set_solver].
Qed.

Lemma basic_context_ty_atom_env_denot_relevant_env
    (Δ : gmap atom ty) τ e :
  basic_context_ty (dom Δ) τ ->
  basic_context_ty_lvars
    (dom (denot_relevant_env (atom_env_to_lty_env Δ) τ e)) τ.
Proof.
  intros Hτ.
  apply basic_context_ty_lvars_denot_relevant_env.
  rewrite atom_store_to_lvar_store_dom.
  apply basic_context_ty_to_lvars. exact Hτ.
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

Lemma lty_env_restrict_lvars_msubst_store_agree
    Σ σ1 σ2 R R' :
  R' ⊆ R ->
  storeA_restrict σ1 (lvars_fv R) =
  storeA_restrict σ2 (lvars_fv R) ->
  lty_env_restrict_lvars (lty_env_msubst_store σ1 Σ) R' =
  lty_env_restrict_lvars (lty_env_msubst_store σ2 Σ) R'.
Proof.
  intros HR Hagree.
  apply storeA_map_eq. intros v.
  unfold lty_env_restrict_lvars, lty_env_msubst_store.
  rewrite !storeA_restrict_lookup.
  destruct (decide (v ∈ R')) as [HvR'|HvR']; [|reflexivity].
  assert (HvR : v ∈ R) by set_solver.
  destruct ((Σ : gmap logic_var ty) !! v) as [T|] eqn:HΣv.
  2:{ repeat destruct decide; reflexivity. }
  destruct v as [k|x].
  - assert (Hb1 : LVBound k ∉ lvars_of_atoms (dom (σ1 : gmap atom value))).
    {
      intros Hbad. unfold lvars_of_atoms in Hbad.
      apply elem_of_map in Hbad as [a [Hbad _]]. discriminate.
    }
    assert (Hb2 : LVBound k ∉ lvars_of_atoms (dom (σ2 : gmap atom value))).
    {
      intros Hbad. unfold lvars_of_atoms in Hbad.
      apply elem_of_map in Hbad as [a [Hbad _]]. discriminate.
    }
    destruct decide; destruct decide; set_solver.
  - assert (HxR : x ∈ lvars_fv R).
    { apply lvars_fv_elem. exact HvR. }
    destruct ((σ1 : gmap atom value) !! x) as [v1|] eqn:Hσ1;
      destruct ((σ2 : gmap atom value) !! x) as [v2|] eqn:Hσ2.
    + assert (Hσ1dom : LVFree x ∈ lvars_of_atoms (dom (σ1 : gmap atom value))).
      { unfold lvars_of_atoms. apply elem_of_map. exists x.
        split; [reflexivity|apply elem_of_dom; eauto]. }
      assert (Hσ2dom : LVFree x ∈ lvars_of_atoms (dom (σ2 : gmap atom value))).
      { unfold lvars_of_atoms. apply elem_of_map. exists x.
        split; [reflexivity|apply elem_of_dom; eauto]. }
      destruct decide; destruct decide; set_solver.
    + exfalso.
      pose proof (storeA_restrict_lookup_transport σ1 σ2
        (lvars_fv R) x v1 HxR Hagree Hσ1) as Hσ2'.
      replace ((σ2 : gmap atom value) !! x) with (@None value) in Hσ2'
        by (symmetry; exact Hσ2).
      discriminate Hσ2'.
    + exfalso.
      pose proof (storeA_restrict_lookup_transport σ2 σ1
        (lvars_fv R) x v2 HxR (eq_sym Hagree) Hσ2) as Hσ1'.
      replace ((σ1 : gmap atom value) !! x) with (@None value) in Hσ1'
        by (symmetry; exact Hσ1).
      discriminate Hσ1'.
    + assert (Hσ1dom : LVFree x ∉ lvars_of_atoms (dom (σ1 : gmap atom value))).
      {
        intros Hbad. unfold lvars_of_atoms in Hbad.
        apply elem_of_map in Hbad as [a [Ha Hdom]].
        inversion Ha; subst.
        apply not_elem_of_dom in Hσ1. exact (Hσ1 Hdom).
      }
      assert (Hσ2dom : LVFree x ∉ lvars_of_atoms (dom (σ2 : gmap atom value))).
      {
        intros Hbad. unfold lvars_of_atoms in Hbad.
        apply elem_of_map in Hbad as [a [Ha Hdom]].
        inversion Ha; subst.
        apply not_elem_of_dom in Hσ2. exact (Hσ2 Hdom).
      }
      destruct decide; destruct decide; set_solver.
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

Lemma denot_relevant_lvars_msubst_store σ τ e :
  store_closed σ ->
  denot_relevant_lvars (context_ty_msubst_store σ τ)
    (lstore_instantiate_tm (lstore_lift_free σ) e) =
  denot_relevant_lvars τ e ∖ dom (lstore_lift_free σ : LStoreT).
Proof.
  intros Hclosed.
  unfold denot_relevant_lvars.
  rewrite context_ty_lvars_msubst_store.
  rewrite (tm_lvars_lstore_instantiate_lift_free_closed σ e Hclosed).
  rewrite dom_lstore_lift_free. set_solver.
Qed.

Lemma denot_relevant_env_msubst_store σ Σ τ e :
  store_closed σ ->
  lty_env_msubst_store σ (denot_relevant_env Σ τ e) =
  denot_relevant_env (lty_env_msubst_store σ Σ)
    (context_ty_msubst_store σ τ)
    (lstore_instantiate_tm (lstore_lift_free σ) e).
Proof.
  intros Hclosed.
  unfold denot_relevant_env, lty_env_restrict_lvars, lty_env_msubst_store.
  rewrite denot_relevant_lvars_msubst_store by exact Hclosed.
  rewrite dom_lstore_lift_free.
  apply storeA_map_eq. intros v.
  destruct ((Σ : gmap logic_var ty) !! v) as [T|] eqn:HΣv.
  - destruct (decide (v ∈ denot_relevant_lvars τ e)) as [HvR|HvR];
      destruct (decide (v ∈ lvars_of_atoms (dom (σ : gmap atom value)))) as [HvF|HvF].
    + transitivity (@None ty).
      * apply storeA_restrict_lookup_none_r.
        rewrite storeA_restrict_dom. set_solver.
      * symmetry. apply storeA_restrict_lookup_none_l.
        apply storeA_restrict_lookup_none_r. set_solver.
    + transitivity (Some T).
      * assert (Hinner :
            storeA_restrict Σ (denot_relevant_lvars τ e) !! v = Some T).
        { apply storeA_restrict_lookup_some_2; [exact HΣv|exact HvR]. }
        apply storeA_restrict_lookup_some_2; [exact Hinner|].
        apply elem_of_difference. split.
        -- eapply elem_of_dom_2. exact Hinner.
        -- exact HvF.
      * assert (Hinner :
            storeA_restrict Σ
              (dom (Σ : gmap logic_var ty)
                ∖ lvars_of_atoms (dom (σ : gmap atom value))) !! v = Some T).
        {
          apply storeA_restrict_lookup_some_2; [exact HΣv|].
          apply elem_of_difference. split; [eapply elem_of_dom_2; exact HΣv|exact HvF].
        }
        symmetry. apply storeA_restrict_lookup_some_2; [exact Hinner|set_solver].
    + transitivity (@None ty).
      * apply storeA_restrict_lookup_none_l.
        apply storeA_restrict_lookup_none_r. exact HvR.
      * symmetry. apply storeA_restrict_lookup_none_r. set_solver.
    + transitivity (@None ty).
      * apply storeA_restrict_lookup_none_l.
        apply storeA_restrict_lookup_none_r. exact HvR.
      * symmetry. apply storeA_restrict_lookup_none_r. set_solver.
  - transitivity (@None ty).
    + apply storeA_restrict_lookup_none_l.
      apply storeA_restrict_lookup_none_l. exact HΣv.
    + symmetry. apply storeA_restrict_lookup_none_l.
      apply storeA_restrict_lookup_none_l. exact HΣv.
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
      as Hbasic_ltype.
    pose proof (basic_tm_has_ltype_lvars _ _ _ Hbasic_ltype) as Hsub.
    assert (Ha_lvars : LVFree a ∈ lvars_of_atoms (fv_tm e_src)).
    {
      unfold lvars_of_atoms.
      apply elem_of_map. exists a. split; [reflexivity|].
      rewrite <- (tm_lvars_fv e_src).
      rewrite <- Hlvars.
      rewrite (tm_lvars_fv e_tgt).
      exact Ha.
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

Lemma arrow_body_relevant_lvars_subset
    τx τr e_src e_body y :
  context_ty_lvars (cty_open 0 y τr) ∖ {[LVFree y]} ⊆
    context_ty_lvars_at 1 τr ->
  tm_lvars e_body ∖ {[LVFree y]} ⊆ tm_lvars e_src ->
  denot_relevant_lvars (cty_open 0 y τr) e_body ∖ {[LVFree y]} ⊆
  denot_relevant_lvars (CTArrow τx τr) e_src.
Proof.
  intros Hτ He.
  unfold denot_relevant_lvars.
  cbn [context_ty_lvars context_ty_lvars_at].
  set_solver.
Qed.

Lemma arrow_body_relevant_env_agree
    (Σsrc : lty_env) Ty y τx τr e_src e_body :
  context_ty_lvars (cty_open 0 y τr) ∖ {[LVFree y]} ⊆
    context_ty_lvars_at 1 τr ->
  tm_lvars e_body ∖ {[LVFree y]} ⊆ tm_lvars e_src ->
  lty_env_restrict_lvars
    (<[LVFree y := Ty]>
      (denot_relevant_env Σsrc (CTArrow τx τr) e_src))
    (denot_relevant_lvars (cty_open 0 y τr) e_body) =
  lty_env_restrict_lvars (<[LVFree y := Ty]> Σsrc)
    (denot_relevant_lvars (cty_open 0 y τr) e_body).
Proof.
  intros Hτ He.
  apply lty_env_restrict_lvars_insert_denot_relevant_env_eq.
  eapply arrow_body_relevant_lvars_subset; eauto.
Qed.

Lemma arrow_body_relevant_env_agree_from_basic_context_ty
    (Σsrc : lty_env) Ty y τx τr e_src e_body :
  lc_lvars (dom (Σsrc : gmap logic_var ty) : gset logic_var) ->
  LVFree y ∉ (dom (Σsrc : gmap logic_var ty) : gset logic_var) ->
  basic_context_ty_lvars
    (dom (Σsrc : gmap logic_var ty) : gset logic_var) (CTArrow τx τr) ->
  tm_lvars e_body ∖ {[LVFree y]} ⊆ tm_lvars e_src ->
  lty_env_restrict_lvars
    (<[LVFree y := Ty]>
      (denot_relevant_env Σsrc (CTArrow τx τr) e_src))
    (denot_relevant_lvars (cty_open 0 y τr) e_body) =
  lty_env_restrict_lvars (<[LVFree y := Ty]> Σsrc)
    (denot_relevant_lvars (cty_open 0 y τr) e_body).
Proof.
  intros Hlc HyΣ Hbasic He.
  apply arrow_body_relevant_env_agree; [|exact He].
  apply context_ty_lvars_open_body_without_fresh_closed
    with (D := (dom (Σsrc : gmap logic_var ty) : gset logic_var)).
  - exact Hlc.
  - exact HyΣ.
  - destruct Hbasic as [Hvars _].
    cbn [context_ty_lvars context_ty_lvars_at] in Hvars.
    set_solver.
Qed.

Lemma wand_body_relevant_env_agree_from_basic_context_ty
    (Σsrc : lty_env) Ty y τx τr e_src e_body :
  lc_lvars (dom (Σsrc : gmap logic_var ty) : gset logic_var) ->
  LVFree y ∉ (dom (Σsrc : gmap logic_var ty) : gset logic_var) ->
  basic_context_ty_lvars
    (dom (Σsrc : gmap logic_var ty) : gset logic_var) (CTWand τx τr) ->
  tm_lvars e_body ∖ {[LVFree y]} ⊆ tm_lvars e_src ->
  lty_env_restrict_lvars
    (<[LVFree y := Ty]>
      (denot_relevant_env Σsrc (CTWand τx τr) e_src))
    (denot_relevant_lvars (cty_open 0 y τr) e_body) =
  lty_env_restrict_lvars (<[LVFree y := Ty]> Σsrc)
    (denot_relevant_lvars (cty_open 0 y τr) e_body).
Proof.
  intros Hlc HyΣ Hbasic He.
  change (denot_relevant_env Σsrc (CTWand τx τr) e_src)
    with (denot_relevant_env Σsrc (CTArrow τx τr) e_src).
  apply arrow_body_relevant_env_agree_from_basic_context_ty.
  - exact Hlc.
  - exact HyΣ.
  - change (basic_context_ty_lvars
      (dom (Σsrc : gmap logic_var ty) : gset logic_var) (CTArrow τx τr)).
    exact Hbasic.
  - exact He.
Qed.

Lemma arrow_arg_relevant_env_agree
    (Σsrc : lty_env) Ty y τx τr e_src :
  lc_lvars (dom (Σsrc : gmap logic_var ty) : gset logic_var) ->
  lty_env_restrict_lvars
    (<[LVFree y := Ty]>
      (denot_relevant_env Σsrc (CTArrow τx τr) e_src))
    (denot_relevant_lvars (cty_open 0 y (cty_shift 0 τx))
      (tret (vfvar y))) =
  lty_env_restrict_lvars (<[LVFree y := Ty]> Σsrc)
    (denot_relevant_lvars (cty_open 0 y (cty_shift 0 τx))
      (tret (vfvar y))).
Proof.
  intros Hlc.
  set (X := denot_relevant_lvars (cty_open 0 y (cty_shift 0 τx))
    (tret (vfvar y))).
  apply storeA_map_eq. intros v.
  unfold lty_env_restrict_lvars.
  change ((storeA_restrict
    (<[LVFree y := Ty]>
      (denot_relevant_env Σsrc (CTArrow τx τr) e_src)) X) !! v =
    (storeA_restrict (<[LVFree y := Ty]> (Σsrc : gmap logic_var ty)) X)
      !! v).
  rewrite (storeA_restrict_lookup
    (<[LVFree y := Ty]>
      (denot_relevant_env Σsrc (CTArrow τx τr) e_src)) X v).
  rewrite (storeA_restrict_lookup
    (<[LVFree y := Ty]> (Σsrc : gmap logic_var ty)) X v).
  destruct (decide (v ∈ X)) as [HvX|HvX]; [|reflexivity].
  destruct v as [k|z].
  - rewrite !lookup_insert_ne by discriminate.
    unfold denot_relevant_env, lty_env_restrict_lvars.
    rewrite storeA_restrict_lookup.
    assert (Hbd : LVBound k ∉ dom (Σsrc : gmap logic_var ty)).
    { intros Hdom. exact (Hlc (LVBound k) Hdom). }
    apply not_elem_of_dom in Hbd.
    destruct (decide (LVBound k ∈ denot_relevant_lvars
      (CTArrow τx τr) e_src)); [reflexivity|symmetry; exact Hbd].
  - destruct (decide (z = y)) as [->|Hzy].
    + rewrite !lookup_insert_eq. reflexivity.
    + rewrite !lookup_insert_ne by congruence.
      unfold denot_relevant_env, lty_env_restrict_lvars.
      rewrite storeA_restrict_lookup.
      destruct (decide (LVFree z ∈ denot_relevant_lvars
        (CTArrow τx τr) e_src)) as [Hzrel|Hzrel]; [reflexivity|].
      exfalso. apply Hzrel.
      unfold denot_relevant_lvars in *.
      cbn [context_ty_lvars context_ty_lvars_at tm_lvars tm_lvars_at
        value_lvars_at] in *.
      apply elem_of_union in HvX as [Hzopen|Hztm].
      * destruct (decide (LVFree z ∈ context_ty_lvars τx)) as [Hzτ|Hzτ].
        { set_solver. }
        exfalso.
        eapply context_ty_lvars_open_shift_fresh in Hzτ; [|exact Hzy].
        exact (Hzτ Hzopen).
      * set_solver.
Qed.

Lemma wand_arg_relevant_env_agree
    (Σsrc : lty_env) Ty y τx τr e_src :
  lc_lvars (dom (Σsrc : gmap logic_var ty) : gset logic_var) ->
  lty_env_restrict_lvars
    (<[LVFree y := Ty]>
      (denot_relevant_env Σsrc (CTWand τx τr) e_src))
    (denot_relevant_lvars (cty_open 0 y (cty_shift 0 τx))
      (tret (vfvar y))) =
  lty_env_restrict_lvars (<[LVFree y := Ty]> Σsrc)
    (denot_relevant_lvars (cty_open 0 y (cty_shift 0 τx))
      (tret (vfvar y))).
Proof.
  intros Hlc.
  change (denot_relevant_env Σsrc (CTWand τx τr) e_src)
    with (denot_relevant_env Σsrc (CTArrow τx τr) e_src).
  apply arrow_arg_relevant_env_agree. exact Hlc.
Qed.

Lemma basic_world_formula_arrow_body_from_source_and_arg
    (Σsrc : lty_env) Ty y τx τr e_src e_body (m : WfWorldT) :
  lc_lvars (dom (Σsrc : gmap logic_var ty) : gset logic_var) ->
  LVFree y ∉ (dom (Σsrc : gmap logic_var ty) : gset logic_var) ->
  basic_context_ty_lvars
    (dom (Σsrc : gmap logic_var ty) : gset logic_var) (CTArrow τx τr) ->
  tm_lvars e_body ∖ {[LVFree y]} ⊆ tm_lvars e_src ->
  m ⊨ basic_world_formula (denot_relevant_env Σsrc (CTArrow τx τr) e_src) ->
  m ⊨ basic_world_formula
    ((<[LVFree y := Ty]> (∅ : gmap logic_var ty)) : lty_env) ->
  m ⊨ basic_world_formula
    (denot_relevant_env (<[LVFree y := Ty]> Σsrc)
      (cty_open 0 y τr) e_body).
Proof.
  intros Hlc HyΣ Hbasic He Hsrc Hy.
  pose proof (basic_world_formula_union
    (denot_relevant_env Σsrc (CTArrow τx τr) e_src)
    ((<[LVFree y := Ty]> (∅ : gmap logic_var ty)) : lty_env)
    m Hsrc Hy) as Hunion.
  eapply basic_world_formula_subenv; [|exact Hunion].
  intros v Tv Hlook.
  pose proof (arrow_body_relevant_env_agree_from_basic_context_ty
    Σsrc Ty y τx τr e_src e_body Hlc HyΣ Hbasic He) as Hagree.
  change ((lty_env_restrict_lvars (<[LVFree y := Ty]> Σsrc)
    (denot_relevant_lvars (cty_open 0 y τr) e_body) : lty_env) !!
    v = Some Tv) in Hlook.
  rewrite <- Hagree in Hlook.
  unfold lty_env_restrict_lvars in Hlook.
  change ((storeA_restrict
    (<[LVFree y := Ty]>
      (denot_relevant_env Σsrc (CTArrow τx τr) e_src))
    (denot_relevant_lvars (cty_open 0 y τr) e_body)
    : gmap logic_var ty) !! v = Some Tv) in Hlook.
  apply storeA_restrict_lookup_some in Hlook as [_ Hlook].
  assert (Hyrel : LVFree y ∉ dom
    (denot_relevant_env Σsrc (CTArrow τx τr) e_src : lty_env)).
  {
    intros Hyrel.
    change (LVFree y ∈ dom
      ((denot_relevant_env Σsrc (CTArrow τx τr) e_src : lty_env)
        : gmap logic_var ty)) in Hyrel.
    apply elem_of_dom in Hyrel as [Ty' Hrel].
    unfold denot_relevant_env, lty_env_restrict_lvars in Hrel.
    change ((storeA_restrict Σsrc
      (denot_relevant_lvars (CTArrow τx τr) e_src)
      : gmap logic_var ty) !! LVFree y = Some Ty') in Hrel.
    apply storeA_restrict_lookup_some in Hrel as [_ HΣ].
    apply HyΣ. eapply elem_of_dom_2. exact HΣ.
  }
  change ((((denot_relevant_env Σsrc (CTArrow τx τr) e_src : lty_env)
    : gmap logic_var ty) ∪
    (<[LVFree y := Ty]> (∅ : gmap logic_var ty))) !! v = Some Tv).
  change (<[LVFree y := Ty]> (∅ : gmap logic_var ty))
    with ({[LVFree y := Ty]} : gmap logic_var ty).
  rewrite storeA_union_singleton_insert_fresh by exact Hyrel.
  exact Hlook.
Qed.

Lemma basic_world_formula_wand_body_from_source_and_arg
    (Σsrc : lty_env) Ty y τx τr e_src e_body (m : WfWorldT) :
  lc_lvars (dom (Σsrc : gmap logic_var ty) : gset logic_var) ->
  LVFree y ∉ (dom (Σsrc : gmap logic_var ty) : gset logic_var) ->
  basic_context_ty_lvars
    (dom (Σsrc : gmap logic_var ty) : gset logic_var) (CTWand τx τr) ->
  tm_lvars e_body ∖ {[LVFree y]} ⊆ tm_lvars e_src ->
  m ⊨ basic_world_formula (denot_relevant_env Σsrc (CTWand τx τr) e_src) ->
  m ⊨ basic_world_formula
    ((<[LVFree y := Ty]> (∅ : gmap logic_var ty)) : lty_env) ->
  m ⊨ basic_world_formula
    (denot_relevant_env (<[LVFree y := Ty]> Σsrc)
      (cty_open 0 y τr) e_body).
Proof.
  intros Hlc HyΣ Hbasic He Hsrc Hy.
  change (denot_relevant_env Σsrc (CTWand τx τr) e_src)
    with (denot_relevant_env Σsrc (CTArrow τx τr) e_src) in Hsrc.
  eapply basic_world_formula_arrow_body_from_source_and_arg; eauto.
Qed.

Lemma tm_lvars_opened_tapp_shift_bvar0_without_y e y :
  lc_tm e ->
  tm_lvars (open_tm 0 (vfvar y)
    (tapp_tm (tm_shift 0 e) (vbvar 0))) ∖ {[LVFree y]} ⊆
  tm_lvars e.
Proof.
  intros Hlc.
  rewrite open_tapp_tm_shift_bvar0_lc by exact Hlc.
  apply tm_lvars_tapp_tm_fvar_without_arg.
Qed.

Lemma wand_body_relevant_env_agree_open_one_core
    (Σsrc : lty_env) Ty y τx τr e_src e_body :
  y ∉ fv_cty τr ->
  tm_lvars e_body ∖ {[LVFree y]} ⊆ lvars_shift_from 0 (tm_lvars e_src) ->
  lty_env_restrict_lvars
    (lty_env_open_one 0 y
      (typed_lty_env_bind
        (denot_relevant_env Σsrc (CTWand τx τr) e_src) Ty))
    (denot_relevant_lvars (cty_open 0 y τr) e_body) =
  lty_env_restrict_lvars
    (lty_env_open_one 0 y (typed_lty_env_bind Σsrc Ty))
    (denot_relevant_lvars (cty_open 0 y τr) e_body).
Proof.
  intros Hyτr He.
  set (X := denot_relevant_lvars (cty_open 0 y τr) e_body).
  apply storeA_map_eq. intros v.
  unfold lty_env_restrict_lvars.
  rewrite !storeA_restrict_lookup.
  destruct (decide (v ∈ X)) as [HvX|HvX]; [|reflexivity].
  unfold lty_env_open_one, lvar_store_open_one.
  replace v with (logic_var_open 0 y (logic_var_open 0 y v))
    by exact (logic_var_open_involutive 0 y v).
  rewrite !storeA_rekey_lookup by apply swap_inj.
  unfold typed_lty_env_bind, lvar_store_bind.
  set (u := logic_var_open 0 y v).
  fold u.
  destruct u as [k|z] eqn:Hu.
  - destruct k as [|k].
    + rewrite !lookup_insert_eq. reflexivity.
    + cbn [insert].
      rewrite !lookup_insert_ne by discriminate.
      assert (Hv_eq : v = LVBound (S k)).
      {
        unfold u in Hu.
        pose proof (f_equal (logic_var_open 0 y) Hu) as Hopen.
        change (swap (LVBound 0) (LVFree y)
          (swap (LVBound 0) (LVFree y) v) =
          swap (LVBound 0) (LVFree y) (LVBound (S k))) in Hopen.
        rewrite swap_involutive in Hopen.
        unfold swap in Hopen.
        repeat destruct decide; try lia; try congruence.
      }
      subst v.
      unfold lty_env_shift, lvar_store_shift, lvar_store_shift_from.
      replace (LVBound (S k)) with (logic_var_shift_from 0 (LVBound k))
        by reflexivity.
      rewrite !storeA_rekey_lookup by apply logic_var_shift_from_inj.
      unfold denot_relevant_env, lty_env_restrict_lvars.
      rewrite storeA_restrict_lookup.
      destruct (decide (LVBound k ∈ denot_relevant_lvars
        (CTWand τx τr) e_src)) as [Hrel|Hrel]; [reflexivity|].
      exfalso. apply Hrel.
      subst X.
      unfold denot_relevant_lvars in *.
      cbn [tm_lvars tm_lvars_at value_lvars_at] in *.
      apply elem_of_union in HvX as [Hτopen|Hebody].
      * assert (Hbody : LVBound k ∈ context_ty_lvars_at 1 τr).
        {
          rewrite <- (context_ty_lvars_depth τr 1).
          apply lvars_at_depth_elem.
          exists (LVBound (S k)). split.
          - rewrite cty_open_vars in Hτopen.
            unfold context_ty_open_lvars in Hτopen.
            rewrite set_swap_elem in Hτopen.
            rewrite (swap_fresh (LVBound 0) (LVFree y) (LVBound (S k)))
              in Hτopen by congruence.
            exact Hτopen.
          - cbn [logic_var_at_depth].
            rewrite decide_True by lia.
            replace (S k - 1) with k by lia.
            reflexivity.
        }
        cbn [denot_relevant_lvars context_ty_lvars context_ty_lvars_at].
        set_solver.
      * assert (Hbody : LVBound k ∈ tm_lvars e_src).
        {
          assert (Hshift : LVBound (S k) ∈ lvars_shift_from 0 (tm_lvars e_src)).
          {
            apply He. apply elem_of_difference. split; [exact Hebody|].
            set_solver.
          }
          unfold lvars_shift_from in Hshift.
          apply elem_of_map in Hshift as [w [Hwshift Hw]].
          destruct w as [n|a]; cbn [logic_var_shift_from] in Hwshift.
          - destruct (decide (0 <= n)); [|lia].
            inversion Hwshift. subst n. exact Hw.
          - discriminate.
        }
        cbn [denot_relevant_lvars context_ty_lvars context_ty_lvars_at].
        set_solver.
  - destruct (decide (z = y)) as [->|Hzy].
    + exfalso.
      unfold u in Hu.
      assert (Hv_eq : v = LVBound 0).
      {
        pose proof (f_equal (logic_var_open 0 y) Hu) as Hopen.
        change (swap (LVBound 0) (LVFree y)
          (swap (LVBound 0) (LVFree y) v) =
          swap (LVBound 0) (LVFree y) (LVFree y)) in Hopen.
        rewrite swap_involutive in Hopen.
        unfold swap in Hopen.
        repeat destruct decide; try lia; try congruence.
      }
      subst v.
      subst X.
      unfold denot_relevant_lvars in *.
      cbn [tm_lvars tm_lvars_at value_lvars_at] in *.
      apply elem_of_union in HvX as [Hτopen|Hebody].
      * apply Hyτr.
        change (y ∈ lvars_fv (context_ty_lvars τr)).
        rewrite context_ty_lvars_fv.
        apply lvars_fv_elem.
        rewrite cty_open_vars in Hτopen.
        unfold context_ty_open_lvars in Hτopen.
        rewrite set_swap_elem in Hτopen.
        rewrite swap_l in Hτopen.
        exact Hτopen.
      * assert (Hshift : LVBound 0 ∈ lvars_shift_from 0 (tm_lvars e_src)).
        {
          apply He. apply elem_of_difference. split; [exact Hebody|].
          set_solver.
        }
        unfold lvars_shift_from in Hshift.
        apply elem_of_map in Hshift as [w [Hwshift _]].
        destruct w as [n|a]; cbn [logic_var_shift_from] in Hwshift.
        -- destruct (decide (0 <= n)); [|lia].
           inversion Hwshift.
        -- discriminate.
    + rewrite !lookup_insert_ne by congruence.
      assert (Hv_eq : v = LVFree z).
      {
        unfold u in Hu.
        pose proof (f_equal (logic_var_open 0 y) Hu) as Hopen.
        change (swap (LVBound 0) (LVFree y)
          (swap (LVBound 0) (LVFree y) v) =
          swap (LVBound 0) (LVFree y) (LVFree z)) in Hopen.
        rewrite swap_involutive in Hopen.
        unfold swap in Hopen.
        repeat destruct decide; try lia; try congruence.
      }
      subst v.
      unfold lty_env_shift, lvar_store_shift, lvar_store_shift_from.
      replace (LVFree z) with (logic_var_shift_from 0 (LVFree z))
        by reflexivity.
      rewrite !storeA_rekey_lookup by apply logic_var_shift_from_inj.
      unfold denot_relevant_env, lty_env_restrict_lvars.
      rewrite storeA_restrict_lookup.
      destruct (decide (LVFree z ∈ denot_relevant_lvars
        (CTWand τx τr) e_src)) as [Hrel|Hrel]; [reflexivity|].
      exfalso. apply Hrel.
      subst X.
      unfold denot_relevant_lvars in *.
      cbn [tm_lvars tm_lvars_at value_lvars_at] in *.
      apply elem_of_union in HvX as [Hτopen|Hebody].
      * assert (Hbody : LVFree z ∈ context_ty_lvars_at 1 τr).
        {
          rewrite <- (context_ty_lvars_depth τr 1).
          apply lvars_at_depth_elem.
          exists (LVFree z). split.
          - rewrite cty_open_vars in Hτopen.
            unfold context_ty_open_lvars in Hτopen.
            rewrite set_swap_elem in Hτopen.
            rewrite (swap_fresh (LVBound 0) (LVFree y) (LVFree z))
              in Hτopen by congruence.
            exact Hτopen.
          - reflexivity.
        }
        cbn [denot_relevant_lvars context_ty_lvars context_ty_lvars_at].
        set_solver.
      * assert (Hbody : LVFree z ∈ tm_lvars e_src).
        {
          assert (Hshift : LVFree z ∈ lvars_shift_from 0 (tm_lvars e_src)).
          {
            apply He. apply elem_of_difference. split; [exact Hebody|].
            set_solver.
          }
          unfold lvars_shift_from in Hshift.
          apply elem_of_map in Hshift as [w [Hwshift Hw]].
          destruct w as [n|a]; cbn [logic_var_shift_from] in Hwshift.
          - destruct (decide (0 <= n)); discriminate.
          - inversion Hwshift. subst a. exact Hw.
        }
        cbn [denot_relevant_lvars context_ty_lvars context_ty_lvars_at].
        set_solver.
Qed.

Lemma arrow_body_relevant_env_agree_open_one_core
    (Σsrc : lty_env) Ty y τx τr e_src e_body :
  y ∉ fv_cty τr ->
  tm_lvars e_body ∖ {[LVFree y]} ⊆ lvars_shift_from 0 (tm_lvars e_src) ->
  lty_env_restrict_lvars
    (lty_env_open_one 0 y
      (typed_lty_env_bind
        (denot_relevant_env Σsrc (CTArrow τx τr) e_src) Ty))
    (denot_relevant_lvars (cty_open 0 y τr) e_body) =
  lty_env_restrict_lvars
    (lty_env_open_one 0 y (typed_lty_env_bind Σsrc Ty))
    (denot_relevant_lvars (cty_open 0 y τr) e_body).
Proof.
  intros Hyτr He.
  change (denot_relevant_env Σsrc (CTArrow τx τr) e_src)
    with (denot_relevant_env Σsrc (CTWand τx τr) e_src).
  apply wand_body_relevant_env_agree_open_one_core; assumption.
Qed.

Lemma lvars_at_depth_denot_relevant_env_subset d Σ τ e :
  lvars_at_depth d (dom (denot_relevant_env Σ τ e)) ⊆
  lvars_at_depth d (dom Σ) ∪ context_ty_lvars_at d τ ∪ tm_lvars_at d e.
Proof.
  unfold denot_relevant_env, lty_env_restrict_lvars, denot_relevant_lvars.
  change (lvars_at_depth d
    (dom (storeA_restrict (Σ : gmap logic_var ty)
      (context_ty_lvars τ ∪ tm_lvars e))) ⊆
    lvars_at_depth d (dom Σ) ∪ context_ty_lvars_at d τ ∪ tm_lvars_at d e).
  rewrite storeA_restrict_dom.
  transitivity (lvars_at_depth d (dom Σ ∩ (context_ty_lvars τ ∪ tm_lvars e))).
  { reflexivity. }
  transitivity (lvars_at_depth d (dom Σ) ∩
    lvars_at_depth d (context_ty_lvars τ ∪ tm_lvars e)).
  - intros v Hv.
    apply lvars_at_depth_elem in Hv as [u [Hu Huv]].
    apply elem_of_intersection in Hu as [HuΣ HuD].
    apply elem_of_intersection. split; apply lvars_at_depth_elem;
      exists u; split; assumption.
  - rewrite lvars_at_depth_union, context_ty_lvars_depth, tm_lvars_depth.
    set_solver.
Qed.

Lemma lvars_at_depth_denot_relevant_env_subset_relevant d Σ τ e :
  lvars_at_depth d (dom (denot_relevant_env Σ τ e)) ⊆
  context_ty_lvars_at d τ ∪ tm_lvars_at d e.
Proof.
  unfold denot_relevant_env, lty_env_restrict_lvars, denot_relevant_lvars.
  change (lvars_at_depth d
    (dom (storeA_restrict (Σ : gmap logic_var ty)
      (context_ty_lvars τ ∪ tm_lvars e))) ⊆
    context_ty_lvars_at d τ ∪ tm_lvars_at d e).
  rewrite storeA_restrict_dom.
  transitivity (lvars_at_depth d (context_ty_lvars τ ∪ tm_lvars e)).
  - apply lvars_at_depth_mono. set_solver.
  - rewrite lvars_at_depth_union, context_ty_lvars_depth, tm_lvars_depth.
    set_solver.
Qed.

Lemma lvars_at_depth_denot_relevant_typed_bind_subset d Σ T τ e :
  lvars_at_depth (S d)
    (dom (denot_relevant_env (typed_lty_env_bind Σ T) τ e)) ⊆
  lvars_at_depth d (dom Σ).
Proof.
  unfold denot_relevant_env, lty_env_restrict_lvars.
  change (lvars_at_depth (S d)
    (dom (storeA_restrict
      (typed_lty_env_bind Σ T : gmap logic_var ty)
      (denot_relevant_lvars τ e))) ⊆
    lvars_at_depth d (dom Σ)).
  rewrite storeA_restrict_dom.
  transitivity (lvars_at_depth (S d) (dom (typed_lty_env_bind Σ T))).
  - apply lvars_at_depth_mono. intros v Hv.
    apply elem_of_intersection in Hv as [Hv _]. exact Hv.
  - rewrite lvars_at_depth_typed_lty_env_bind. reflexivity.
Qed.

Lemma lvars_at_depth_arrow_arg_lift_support_subset Σ τx τr e :
  lvars_at_depth 1
    (dom (typed_lty_env_bind
      (denot_relevant_env Σ (CTArrow τx τr) e) (erase_ty τx)) ∪
     denot_relevant_lvars (cty_shift 0 τx) (tret (vbvar 0))) ⊆
  dom Σ ∪ denot_relevant_lvars (CTArrow τx τr) e.
Proof.
  rewrite lvars_at_depth_union.
  rewrite lvars_at_depth_typed_lty_env_bind.
  pose proof (lvars_at_depth_denot_relevant_env_subset_relevant
    0 Σ (CTArrow τx τr) e) as Hrel.
  unfold denot_relevant_lvars.
  rewrite lvars_at_depth_union, context_ty_lvars_depth, tm_lvars_depth.
  rewrite context_ty_lvars_at_shift_under by lia.
  rewrite tm_lvars_at_tret_bound0_under.
  cbn [context_ty_lvars context_ty_lvars_at].
  set_solver.
Qed.

Lemma lvars_at_depth_arrow_body_lift_support_subset Σ τx τr e :
  lvars_at_depth 1
    (dom (typed_lty_env_bind
      (denot_relevant_env Σ (CTArrow τx τr) e) (erase_ty τx)) ∪
     denot_relevant_lvars τr (tapp_tm (tm_shift 0 e) (vbvar 0))) ⊆
  dom Σ ∪ denot_relevant_lvars (CTArrow τx τr) e.
Proof.
  rewrite lvars_at_depth_union.
  rewrite lvars_at_depth_typed_lty_env_bind.
  pose proof (lvars_at_depth_denot_relevant_env_subset_relevant
    0 Σ (CTArrow τx τr) e) as Hrel.
  pose proof (tm_lvars_at_tapp_shift0_bound0 e 0) as Htapp.
  unfold denot_relevant_lvars.
  rewrite lvars_at_depth_union, context_ty_lvars_depth, tm_lvars_depth.
  cbn [context_ty_lvars context_ty_lvars_at].
  set_solver.
Qed.

Lemma lvars_at_depth_wand_arg_lift_support_subset Σ τx τr e :
  lvars_at_depth 1
    (dom (typed_lty_env_bind
      (denot_relevant_env Σ (CTWand τx τr) e) (erase_ty τx)) ∪
     denot_relevant_lvars (cty_shift 0 τx) (tret (vbvar 0))) ⊆
  dom Σ ∪ denot_relevant_lvars (CTWand τx τr) e.
Proof.
  rewrite lvars_at_depth_union.
  rewrite lvars_at_depth_typed_lty_env_bind.
  pose proof (lvars_at_depth_denot_relevant_env_subset_relevant
    0 Σ (CTWand τx τr) e) as Hrel.
  unfold denot_relevant_lvars.
  rewrite lvars_at_depth_union, context_ty_lvars_depth, tm_lvars_depth.
  rewrite context_ty_lvars_at_shift_under by lia.
  rewrite tm_lvars_at_tret_bound0_under.
  cbn [context_ty_lvars context_ty_lvars_at].
  set_solver.
Qed.

Lemma lvars_at_depth_wand_body_lift_support_subset Σ τx τr e :
  lvars_at_depth 1
    (dom (typed_lty_env_bind
      (denot_relevant_env Σ (CTWand τx τr) e) (erase_ty τx)) ∪
     denot_relevant_lvars τr (tapp_tm (tm_shift 0 e) (vbvar 0))) ⊆
  dom Σ ∪ denot_relevant_lvars (CTWand τx τr) e.
Proof.
  rewrite lvars_at_depth_union.
  rewrite lvars_at_depth_typed_lty_env_bind.
  pose proof (lvars_at_depth_denot_relevant_env_subset_relevant
    0 Σ (CTWand τx τr) e) as Hrel.
  pose proof (tm_lvars_at_tapp_shift0_bound0 e 0) as Htapp.
  unfold denot_relevant_lvars.
  rewrite lvars_at_depth_union, context_ty_lvars_depth, tm_lvars_depth.
  cbn [context_ty_lvars context_ty_lvars_at].
  set_solver.
Qed.

Lemma lvars_at_depth_restrict_typed_bind_subset d Σ T D :
  lvars_at_depth (S d)
    (dom (lty_env_restrict_lvars (typed_lty_env_bind Σ T) D)) ⊆
  lvars_at_depth d (dom Σ).
Proof.
  unfold lty_env_restrict_lvars.
  change (lvars_at_depth (S d)
    (dom (storeA_restrict
      (typed_lty_env_bind Σ T : gmap logic_var ty) D)) ⊆
    lvars_at_depth d (dom Σ)).
  rewrite storeA_restrict_dom.
  transitivity (lvars_at_depth (S d) (dom (typed_lty_env_bind Σ T))).
  - apply lvars_at_depth_mono. intros v Hv.
    apply elem_of_intersection in Hv as [Hv _]. exact Hv.
  - rewrite lvars_at_depth_typed_lty_env_bind. reflexivity.
Qed.

Lemma lvars_at_depth_dom_singleton_bound0_succ d T :
  lvars_at_depth (S d) (dom (<[LVBound 0 := T]> (∅ : lty_env))) = ∅.
Proof.
  rewrite dom_insert_L, dom_empty_L, lvars_at_depth_union.
  rewrite lvars_at_depth_singleton_bound0_succ, lvars_at_depth_empty.
  set_solver.
Qed.

Lemma lty_env_open_one_denot_relevant_bind_under k y Σ τ e T :
  y ∉ lvars_fv (dom Σ) ->
  y ∉ fv_tm e ->
  lty_env_open_one (S k) y
    (typed_lty_env_bind (denot_relevant_env Σ τ e) T) =
  typed_lty_env_bind
    (denot_relevant_env (lty_env_open_one k y Σ)
      (cty_open k y τ) (open_tm k (vfvar y) e))
    T.
Proof.
  intros HΣ Hy.
  rewrite typed_lty_env_bind_open_under.
  - rewrite denot_relevant_env_open_one by exact Hy.
    reflexivity.
  - intros Hbad.
    apply HΣ.
    eapply lty_env_restrict_lvars_fv_dom_subset.
    apply lvars_fv_elem. exact Hbad.
Qed.

Lemma wand_arg_relevant_env_agree_open_one_core
    (Σsrc : lty_env) Ty y τx τr e_src :
  y ∉ fv_cty τx ->
  lty_env_restrict_lvars
    (lty_env_open_one 0 y
      (typed_lty_env_bind
        (denot_relevant_env Σsrc (CTWand τx τr) e_src) Ty))
    (denot_relevant_lvars (cty_open 0 y (cty_shift 0 τx))
      (tret (vfvar y))) =
  lty_env_restrict_lvars
    (lty_env_open_one 0 y (typed_lty_env_bind Σsrc Ty))
    (denot_relevant_lvars (cty_open 0 y (cty_shift 0 τx))
      (tret (vfvar y))).
Proof.
  intros Hyτx.
  set (X := denot_relevant_lvars (cty_open 0 y (cty_shift 0 τx))
    (tret (vfvar y))).
  apply storeA_map_eq. intros v.
  unfold lty_env_restrict_lvars.
  rewrite !storeA_restrict_lookup.
  destruct (decide (v ∈ X)) as [HvX|HvX]; [|reflexivity].
  unfold lty_env_open_one, lvar_store_open_one.
  replace v with (logic_var_open 0 y (logic_var_open 0 y v))
    by exact (logic_var_open_involutive 0 y v).
  rewrite !storeA_rekey_lookup by apply swap_inj.
  unfold typed_lty_env_bind, lvar_store_bind.
  set (u := logic_var_open 0 y v).
  fold u.
  destruct u as [k|z] eqn:Hu.
  - destruct k as [|k].
    + rewrite !lookup_insert_eq. reflexivity.
    + cbn [insert].
      rewrite !lookup_insert_ne by discriminate.
      assert (Hv_eq : v = LVBound (S k)).
      {
        unfold u in Hu.
        pose proof (f_equal (logic_var_open 0 y) Hu) as Hopen.
        change (swap (LVBound 0) (LVFree y)
          (swap (LVBound 0) (LVFree y) v) =
          swap (LVBound 0) (LVFree y) (LVBound (S k))) in Hopen.
        rewrite swap_involutive in Hopen.
        unfold swap in Hopen.
        repeat destruct decide; try lia; try congruence.
      }
      subst v.
      unfold lty_env_shift, lvar_store_shift, lvar_store_shift_from.
      replace (LVBound (S k)) with (logic_var_shift_from 0 (LVBound k))
        by reflexivity.
      rewrite !storeA_rekey_lookup by apply logic_var_shift_from_inj.
      unfold denot_relevant_env, lty_env_restrict_lvars.
      rewrite storeA_restrict_lookup.
      destruct (decide (LVBound k ∈ denot_relevant_lvars (CTWand τx τr) e_src))
        as [Hrel|Hrel]; [reflexivity|].
      exfalso. apply Hrel.
      subst X.
      unfold denot_relevant_lvars in *.
      cbn [context_ty_lvars context_ty_lvars_at
        tm_lvars tm_lvars_at value_lvars_at] in *.
      rewrite cty_open_vars in HvX.
      unfold context_ty_open_lvars in HvX.
      rewrite cty_shift_vars in HvX.
      unfold context_ty_shift_lvars in HvX.
      cbn [context_ty_lvars context_ty_lvars_at] in *.
      apply elem_of_union_l.
      apply elem_of_union_l.
      apply elem_of_union in HvX as [Hopen|Hret].
      2:{ set_solver. }
      rewrite set_swap_elem in Hopen.
      rewrite (swap_fresh (LVBound 0) (LVFree y) (LVBound (S k))) in Hopen
        by congruence.
      unfold lvars_shift_from in Hopen.
      apply elem_of_map in Hopen as [w [Hwshift Hw]].
      destruct w as [n|a]; cbn [logic_var_shift_from] in Hwshift;
        repeat destruct decide; inversion Hwshift; subst; try lia.
      exact Hw.
  - destruct (decide (z = y)) as [->|Hzy].
    + exfalso.
      unfold u in Hu.
      assert (Hv_eq : v = LVBound 0).
      {
        unfold u in Hu.
        pose proof (f_equal (logic_var_open 0 y) Hu) as Hopen.
        change (swap (LVBound 0) (LVFree y)
          (swap (LVBound 0) (LVFree y) v) =
          swap (LVBound 0) (LVFree y) (LVFree y)) in Hopen.
        rewrite swap_involutive in Hopen.
        unfold swap in Hopen.
        repeat destruct decide; try lia; try congruence.
      }
      subst v.
      subst X.
      unfold denot_relevant_lvars in *.
      cbn [context_ty_lvars context_ty_lvars_at
        tm_lvars tm_lvars_at value_lvars_at] in *.
      rewrite cty_open_vars in HvX.
      unfold context_ty_open_lvars in HvX.
      rewrite cty_shift_vars in HvX.
      unfold context_ty_shift_lvars in HvX.
      cbn [context_ty_lvars context_ty_lvars_at] in *.
      apply elem_of_union in HvX as [Hopen|Hret].
      { rewrite set_swap_elem in Hopen.
        rewrite swap_l in Hopen.
        apply Hyτx.
        change (y ∈ lvars_fv (context_ty_lvars τx)).
        rewrite <- (lvars_shift_from_fv 0 (context_ty_lvars τx)).
        apply lvars_fv_elem. exact Hopen. }
      { set_solver. }
    + rewrite !lookup_insert_ne by congruence.
      assert (Hv_eq : v = LVFree z).
      {
        unfold u in Hu.
        pose proof (f_equal (logic_var_open 0 y) Hu) as Hopen.
        change (swap (LVBound 0) (LVFree y)
          (swap (LVBound 0) (LVFree y) v) =
          swap (LVBound 0) (LVFree y) (LVFree z)) in Hopen.
        rewrite swap_involutive in Hopen.
        unfold swap in Hopen.
        repeat destruct decide; try lia; try congruence.
      }
      subst v.
      unfold lty_env_shift, lvar_store_shift, lvar_store_shift_from.
      replace (LVFree z) with (logic_var_shift_from 0 (LVFree z))
        by reflexivity.
      rewrite !storeA_rekey_lookup by apply logic_var_shift_from_inj.
      unfold denot_relevant_env, lty_env_restrict_lvars.
      rewrite storeA_restrict_lookup.
      destruct (decide (LVFree z ∈ denot_relevant_lvars (CTWand τx τr) e_src))
        as [Hrel|Hrel]; [reflexivity|].
      exfalso. apply Hrel.
      subst X.
      unfold denot_relevant_lvars in *.
      cbn [context_ty_lvars context_ty_lvars_at
        tm_lvars tm_lvars_at value_lvars_at] in *.
      rewrite cty_open_vars in HvX.
      unfold context_ty_open_lvars in HvX.
      rewrite cty_shift_vars in HvX.
      unfold context_ty_shift_lvars in HvX.
      cbn [context_ty_lvars context_ty_lvars_at] in *.
      apply elem_of_union in HvX as [Hopen|Hret].
      { rewrite set_swap_elem in Hopen.
        rewrite (swap_fresh (LVBound 0) (LVFree y) (LVFree z)) in Hopen
          by congruence.
        unfold lvars_shift_from in Hopen.
        apply elem_of_map in Hopen as [w [Hwshift Hw]].
        destruct w as [n|a]; cbn [logic_var_shift_from] in Hwshift;
          repeat destruct decide; inversion Hwshift; subst; try lia.
        apply elem_of_union_l. apply elem_of_union_l. exact Hw. }
      { set_solver. }
Qed.

Lemma arrow_arg_relevant_env_agree_open_one_core
    (Σsrc : lty_env) Ty y τx τr e_src :
  y ∉ fv_cty τx ->
  lty_env_restrict_lvars
    (lty_env_open_one 0 y
      (typed_lty_env_bind
        (denot_relevant_env Σsrc (CTArrow τx τr) e_src) Ty))
    (denot_relevant_lvars (cty_open 0 y (cty_shift 0 τx))
      (tret (vfvar y))) =
  lty_env_restrict_lvars
    (lty_env_open_one 0 y (typed_lty_env_bind Σsrc Ty))
    (denot_relevant_lvars (cty_open 0 y (cty_shift 0 τx))
      (tret (vfvar y))).
Proof.
  intros Hyτx.
  change (denot_relevant_env Σsrc (CTArrow τx τr) e_src)
    with (denot_relevant_env Σsrc (CTWand τx τr) e_src).
  apply wand_arg_relevant_env_agree_open_one_core. exact Hyτx.
Qed.

End RelevantEnv.
