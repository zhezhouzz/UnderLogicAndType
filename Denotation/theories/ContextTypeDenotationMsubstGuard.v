(** * Denotation.ContextTypeDenotationMsubstGuard

    Split from ContextTypeDenotationMsubst for incremental compilation. *)

From Denotation Require Import Notation ContextTypeDenotationDefinition
  ContextTypeDenotationLvars ContextTypeDenotationMsubstCore.

Section ContextTypeDenotationMsubst.

Lemma expr_total_formula_msubst_store_singleton_iff
    σ Σ e (m : WfWorldT) :
  atom_store_has_ltype Σ σ ->
  m ⊨ formula_msubst_store σ (expr_total_formula e) <->
  m ⊨ expr_total_formula
    (lstore_instantiate_tm (lstore_lift_free σ) e).
Proof.
  intros Hσty. split.
  - apply expr_total_formula_msubst_store_models with (Σ := Σ).
    exact Hσty.
  - apply expr_total_formula_msubst_store_models_back with (Σ := Σ).
    exact Hσty.
Qed.

Lemma context_ty_wf_formula_msubst_store_fixed_scope_iff
    σ Σ τ e (m : WfWorldT) :
  basic_context_ty_lvars (dom Σ) τ ->
  tm_lvars e ⊆ dom Σ ->
  atom_store_has_ltype Σ σ ->
  dom (σ : StoreT) ∩ lvars_fv (denot_relevant_lvars τ e) ⊆
    world_dom (m : WorldT) ->
  m ⊨ formula_msubst_store σ
    (context_ty_wf_formula (denot_relevant_env Σ τ e) τ) <->
  m ⊨ context_ty_wf_formula
    (denot_relevant_env Σ τ
      (lstore_instantiate_tm (lstore_lift_free σ) e)) τ.
Proof.
  intros Hwf He Hσty Hscope_fixed.
  pose proof (atom_store_has_ltype_closed _ _ Hσty) as Hclosed.
  set (R := denot_relevant_lvars τ e).
  set (e' := lstore_instantiate_tm (lstore_lift_free σ) e).
  set (Σg := denot_relevant_env Σ τ e).
  set (Σg' := denot_relevant_env Σ τ e').
  assert (HdomΣg : dom (Σg : lty_env) = dom (Σ : lty_env) ∩ R).
  {
    subst Σg. unfold denot_relevant_env, lty_env_restrict_lvars.
    rewrite storeA_restrict_dom. reflexivity.
  }
  assert (HR' : denot_relevant_lvars τ e' =
      context_ty_lvars τ ∪ (tm_lvars e ∖ dom (lstore_lift_free σ : LStoreT))).
  {
    subst e'. unfold denot_relevant_lvars.
    rewrite (tm_lvars_lstore_instantiate_lift_free_closed σ e Hclosed).
    reflexivity.
  }
  assert (HdomΣg' : dom (Σg' : lty_env) =
      dom (Σ : lty_env) ∩ denot_relevant_lvars τ e').
  {
    subst Σg'. unfold denot_relevant_env, lty_env_restrict_lvars.
    rewrite storeA_restrict_dom. reflexivity.
  }
  split.
  - intros Hsrc.
    change (formula_msubst_store σ (context_ty_wf_formula Σg τ))
      with (FAtom (lqual_msubst_store σ (context_ty_wf_lqual Σg τ))) in Hsrc.
    unfold res_models in Hsrc.
    cbn [formula_measure res_models_fuel] in Hsrc.
    destruct Hsrc as [_ Hden].
    unfold lqual_msubst_store, context_ty_wf_lqual,
      lqual_mlsubst, logic_qualifier_denote in Hden.
    cbn [lqual_dom lqual_prop] in Hden.
    destruct Hden as [Hlc_res [Hsub_res _]].
    rewrite dom_lstore_lift_free in Hlc_res, Hsub_res.
    apply context_ty_wf_formula_models_iff.
    split.
    + intros v Hv.
      destruct v as [k|x]; [|exact I].
      apply Hlc_res.
      rewrite HdomΣg', HR' in Hv.
      rewrite HdomΣg.
      change (LVBound k ∈ dom (Σ : lty_env) ∩ R ∖
        lvars_of_atoms (dom (σ : StoreT))).
      apply elem_of_intersection in Hv as [HvΣ Hvrel_res].
      apply elem_of_difference. split.
      * apply elem_of_intersection. split; [exact HvΣ|].
        subst R. unfold denot_relevant_lvars.
        apply elem_of_union in Hvrel_res as [Hvτ|Hve].
        -- apply elem_of_union_l. exact Hvτ.
        -- apply elem_of_union_r.
           apply elem_of_difference in Hve as [Hve _].
           exact Hve.
      * unfold lvars_of_atoms. rewrite elem_of_map.
        intros (a & Heq & _). inversion Heq.
    + split.
      * intros x Hx.
        apply lvars_fv_elem in Hx as Hv.
        rewrite HdomΣg', HR' in Hv.
        apply elem_of_intersection in Hv as [HvΣ Hvrel_res].
        assert (Hvrel : LVFree x ∈ context_ty_lvars τ ∪ tm_lvars e).
        {
          apply elem_of_union in Hvrel_res as [Hvτ|Hve].
          - apply elem_of_union_l. exact Hvτ.
          - apply elem_of_union_r.
            apply elem_of_difference in Hve as [Hve _].
            exact Hve.
        }
        destruct (decide (x ∈ dom (σ : StoreT))) as [Hxσ|Hxσ].
        -- apply Hscope_fixed.
           apply elem_of_intersection. split; [exact Hxσ|].
           subst R. unfold denot_relevant_lvars.
           apply lvars_fv_elem. exact Hvrel.
        -- apply Hsub_res.
           rewrite HdomΣg.
           apply lvars_fv_elem.
           change (LVFree x ∈ dom (Σ : lty_env) ∩ R ∖
             lvars_of_atoms (dom (σ : StoreT))).
           apply elem_of_difference. split.
           ++ apply elem_of_intersection. split.
              ** exact HvΣ.
              ** subst R. unfold denot_relevant_lvars.
                 exact Hvrel.
           ++ unfold lvars_of_atoms. rewrite elem_of_map.
              intros (a & Heq & Ha). inversion Heq; subst. exact (Hxσ Ha).
      * subst Σg'. apply basic_context_ty_lvars_denot_relevant_env.
        exact Hwf.
  - intros Htgt.
    apply context_ty_wf_formula_models_iff in Htgt as
      [Hlc_tgt [Hsub_tgt Hbasic_tgt]].
    apply res_models_atom_intro.
    unfold context_ty_wf_formula, context_ty_wf_lqual,
      lqual_msubst_store, lqual_mlsubst, logic_qualifier_denote.
    cbn [lqual_dom lqual_prop].
    change (atom_store_to_lvar_store σ) with (lstore_lift_free σ).
    rewrite dom_lstore_lift_free.
    assert (Hlc_res : lc_lvars (dom Σg ∖ lvars_of_atoms (dom (σ : StoreT)))).
    {
      intros v Hv.
      destruct v as [k|x]; [|exact I].
      apply Hlc_tgt.
      rewrite HdomΣg', HR'.
      rewrite HdomΣg in Hv.
      change (LVBound k ∈ dom (Σ : lty_env) ∩ R ∖
        lvars_of_atoms (dom (σ : StoreT))) in Hv.
      apply elem_of_difference in Hv as [Hvdom _].
      apply elem_of_intersection in Hvdom as [HvΣ Hvrel].
      apply elem_of_intersection. split; [exact HvΣ|].
      subst R. unfold denot_relevant_lvars in Hvrel.
      apply elem_of_union in Hvrel as [Hvτ|Hve].
      * apply elem_of_union_l. exact Hvτ.
      * apply elem_of_union_r.
        apply elem_of_difference. split; [exact Hve|].
        rewrite dom_lstore_lift_free.
        unfold lvars_of_atoms. rewrite elem_of_map.
        intros (a & Heq & _). inversion Heq.
    }
    assert (Hsub_res :
      lvars_fv (dom Σg ∖ lvars_of_atoms (dom (σ : StoreT))) ⊆
      world_dom (m : WorldT)).
    {
      intros x Hx.
      apply Hsub_tgt.
      apply lvars_fv_elem.
      apply lvars_fv_elem in Hx as Hv.
      rewrite HdomΣg', HR'.
      rewrite HdomΣg in Hv.
      change (LVFree x ∈ dom (Σ : lty_env) ∩ R ∖
        lvars_of_atoms (dom (σ : StoreT))) in Hv.
      apply elem_of_difference in Hv as [Hvdom Hnotσ].
      apply elem_of_intersection in Hvdom as [HvΣ Hvrel].
      apply elem_of_intersection. split; [exact HvΣ|].
      subst R. unfold denot_relevant_lvars in Hvrel.
      apply elem_of_union in Hvrel as [Hvτ|Hve].
      * apply elem_of_union_l. exact Hvτ.
      * apply elem_of_union_r.
        apply elem_of_difference. split; [exact Hve|].
        rewrite dom_lstore_lift_free.
        unfold lvars_of_atoms. rewrite elem_of_map.
        intros (a & Heq & Ha). inversion Heq; subst.
        apply Hnotσ.
        unfold lvars_of_atoms. rewrite elem_of_map.
        eexists. split; [reflexivity|exact Ha].
    }
    exists Hlc_res, Hsub_res.
    subst Σg. apply basic_context_ty_lvars_denot_relevant_env.
    exact Hwf.
Qed.

Lemma context_ty_wf_formula_msubst_store_singleton_iff
    σ Σ τ e (m : WfWorldT) :
  basic_context_ty_lvars (dom Σ) τ ->
  tm_lvars e ⊆ dom Σ ->
  atom_store_has_ltype Σ σ ->
  (res_restrict m (lvars_fv (denot_relevant_lvars τ e)) : WorldT) =
    singleton_world (store_restrict σ (lvars_fv (denot_relevant_lvars τ e))) ->
  m ⊨ formula_msubst_store σ
    (context_ty_wf_formula (denot_relevant_env Σ τ e) τ) <->
  m ⊨ context_ty_wf_formula
    (denot_relevant_env Σ τ
      (lstore_instantiate_tm (lstore_lift_free σ) e)) τ.
Proof.
  intros Hwf He Hσty Hsingle.
  eapply context_ty_wf_formula_msubst_store_fixed_scope_iff; eauto.
  pose proof (f_equal world_dom Hsingle) as Hdom.
  simpl in Hdom.
  rewrite storeA_restrict_dom in Hdom.
  set_solver.
Qed.

Lemma basic_world_formula_msubst_store_fixed_singleton_iff
    σ Σ τ e (m : WfWorldT) :
  basic_context_ty_lvars (dom Σ) τ ->
  tm_lvars e ⊆ dom Σ ->
  atom_store_has_ltype Σ σ ->
  (res_restrict m
    (lvars_fv (denot_relevant_lvars τ e ∩
      lvars_of_atoms (dom (σ : StoreT)))) : WorldT) =
    singleton_world
      (store_restrict σ
        (lvars_fv (denot_relevant_lvars τ e ∩
          lvars_of_atoms (dom (σ : StoreT))))) ->
  m ⊨ formula_msubst_store σ
    (basic_world_formula (denot_relevant_env Σ τ e)) <->
  m ⊨ basic_world_formula
    (denot_relevant_env Σ τ
      (lstore_instantiate_tm (lstore_lift_free σ) e)).
Proof.
  intros Hwf He Hσty Hfixed_singleton.
  pose proof (atom_store_has_ltype_closed _ _ Hσty) as Hclosed.
  set (R := denot_relevant_lvars τ e).
  set (e' := lstore_instantiate_tm (lstore_lift_free σ) e).
  set (Σg := denot_relevant_env Σ τ e).
  set (Σg' := denot_relevant_env Σ τ e').
  set (σR := store_restrict σ (lvars_fv R)).
  assert (HR' : denot_relevant_lvars τ e' =
      context_ty_lvars τ ∪ (tm_lvars e ∖ dom (lstore_lift_free σ : LStoreT))).
  {
    subst e'. unfold denot_relevant_lvars.
    rewrite (tm_lvars_lstore_instantiate_lift_free_closed σ e Hclosed).
    reflexivity.
  }
  assert (HσRty : atom_store_has_ltype Σg σR).
  {
    subst σR Σg R.
    apply atom_store_has_ltype_denot_relevant_env.
    - intros v Hv.
      unfold denot_relevant_lvars.
      unfold lvars_of_atoms in Hv.
      apply elem_of_map in Hv as [x [-> Hx]].
      apply elem_of_dom in Hx as [vx Hx].
      apply storeA_restrict_lookup_some in Hx as [HxR _].
      apply lvars_fv_elem in HxR. exact HxR.
    - intros x v Hlook.
      apply storeA_restrict_lookup_some in Hlook as [_ Hlook].
      exact (Hσty x v Hlook).
  }
  assert (Hfv_src : formula_fv (basic_world_formula Σg) ⊆ lvars_fv R).
  {
    subst Σg. rewrite formula_fv_basic_world_formula.
    apply lty_env_restrict_lvars_fv_subset.
  }
  assert (Hres_sub_tgt :
    forall v T,
      lty_env_msubst_store σR Σg !! v = Some T ->
      Σg' !! v = Some T).
  {
    intros v T Hlook.
    subst σR Σg Σg' R e'.
    apply lty_env_msubst_store_lookup_some in Hlook as [Hlook Hfresh].
    unfold denot_relevant_env, lty_env_restrict_lvars in *.
    apply storeA_restrict_lookup_some in Hlook as [HvR HΣv].
    apply storeA_restrict_lookup_some_2; [exact HΣv|].
    rewrite HR'. unfold denot_relevant_lvars in HvR.
    apply elem_of_union in HvR as [Hvτ|Hve].
    - apply elem_of_union_l. exact Hvτ.
    - apply elem_of_union_r.
      apply elem_of_difference. split; [exact Hve|].
      intros Hvfixed. apply Hfresh.
      rewrite dom_lstore_lift_free in Hvfixed.
      unfold lvars_of_atoms in Hvfixed.
      apply elem_of_map in Hvfixed as [x [-> Hx]].
      apply elem_of_dom in Hx as [vx Hx].
      unfold lvars_of_atoms. apply elem_of_map.
      exists x. split; [reflexivity|].
      apply elem_of_dom.
      exists vx.
      apply storeA_restrict_lookup_some_2; [exact Hx|].
      apply lvars_fv_elem. unfold denot_relevant_lvars.
      apply elem_of_union_r. exact Hve.
  }
  assert (Htgt_sub_big :
    forall v T,
      Σg' !! v = Some T ->
      (((lty_env_msubst_store σR Σg : lty_env) ∪
        storeA_restrict Σ (R ∩ lvars_of_atoms (dom (σ : StoreT)))) : lty_env)
        !! v = Some T).
  {
    intros v T Hlook.
    subst Σg'.
    unfold denot_relevant_env, lty_env_restrict_lvars in Hlook.
    apply storeA_restrict_lookup_some in Hlook as [HvR' HΣv].
    destruct v as [k|x].
    - apply map_lookup_union_Some_raw. left.
      subst σR Σg.
      apply lty_env_msubst_store_lookup_some_2.
      + unfold denot_relevant_env, lty_env_restrict_lvars.
        apply storeA_restrict_lookup_some_2; [exact HΣv|].
        subst R. unfold denot_relevant_lvars.
        rewrite HR' in HvR'.
        apply elem_of_union in HvR' as [Hvτ|Hve].
        * apply elem_of_union_l. exact Hvτ.
        * apply elem_of_union_r.
          apply elem_of_difference in Hve as [Hve _]. exact Hve.
      + unfold lvars_of_atoms. rewrite elem_of_map.
        intros (a & Heq & _). discriminate.
    - destruct (decide (x ∈ dom (σ : StoreT))) as [Hxσ|Hxσ].
      + apply map_lookup_union_Some_raw. right. split.
        * subst σR Σg.
          apply not_elem_of_dom_1.
          rewrite lty_env_msubst_store_dom.
          intros Hin.
          apply elem_of_difference in Hin as [_ Hfresh].
          apply Hfresh.
          unfold lvars_of_atoms. apply elem_of_map.
          exists x. split; [reflexivity|].
          destruct (σ !! x) as [vx|] eqn:Hxσlook.
          2: {
            exfalso.
            assert (Hxσ' : x ∈ dom (σ : gmap atom value)) by exact Hxσ.
            apply elem_of_dom in Hxσ' as [vx Hlook].
            change (((σ : gmap atom value) !! x) = None) in Hxσlook.
            rewrite Hxσlook in Hlook. discriminate.
          }
          eapply elem_of_dom_2.
          apply storeA_restrict_lookup_some_2; [exact Hxσlook|].
          apply lvars_fv_elem. subst R. unfold denot_relevant_lvars.
          rewrite HR' in HvR'.
          apply elem_of_union in HvR' as [Hvτ|Hve].
          -- apply elem_of_union_l. exact Hvτ.
          -- apply elem_of_union_r.
             apply elem_of_difference in Hve as [Hve _]. exact Hve.
        * apply storeA_restrict_lookup_some_2; [exact HΣv|].
          apply elem_of_intersection. split.
          -- subst R. unfold denot_relevant_lvars.
             rewrite HR' in HvR'.
             apply elem_of_union in HvR' as [Hvτ|Hve].
             ++ apply elem_of_union_l. exact Hvτ.
             ++ apply elem_of_union_r.
                apply elem_of_difference in Hve as [Hve _]. exact Hve.
          -- unfold lvars_of_atoms. apply elem_of_map.
             exists x. split; [reflexivity|exact Hxσ].
      + apply map_lookup_union_Some_raw. left.
        subst σR Σg.
        apply lty_env_msubst_store_lookup_some_2.
        * unfold denot_relevant_env, lty_env_restrict_lvars.
          apply storeA_restrict_lookup_some_2; [exact HΣv|].
          subst R. unfold denot_relevant_lvars.
          rewrite HR' in HvR'.
          apply elem_of_union in HvR' as [Hvτ|Hve].
          -- apply elem_of_union_l. exact Hvτ.
          -- apply elem_of_union_r.
             apply elem_of_difference in Hve as [Hve _]. exact Hve.
        * unfold lvars_of_atoms. rewrite elem_of_map.
          intros (a & Heq & Ha). inversion Heq; subst.
          apply Hxσ.
          rewrite storeA_restrict_dom in Ha.
          apply elem_of_intersection in Ha as [Ha _].
          exact Ha.
  }
  split.
  - intros Hsrc.
    rewrite (formula_msubst_store_restrict_fv_subset σ
      (basic_world_formula Σg) (lvars_fv R) Hfv_src) in Hsrc.
    fold σR in Hsrc.
    pose proof (basic_world_formula_msubst_store_models σR Σg m
      HσRty Hsrc) as Hres.
    pose proof (basic_world_formula_fixed_from_singleton
      Σ σ (R ∩ lvars_of_atoms (dom (σ : StoreT))) m
      Hσty Hfixed_singleton) as Hfixed.
    replace (storeA_restrict Σ
      ((R ∩ lvars_of_atoms (dom (σ : StoreT))) ∩
        lvars_of_atoms (dom (σ : StoreT)))) with
      (storeA_restrict Σ (R ∩ lvars_of_atoms (dom (σ : StoreT)))) in Hfixed.
    2:{
      apply storeA_map_eq. intros v.
      rewrite !storeA_restrict_lookup.
      destruct (decide (v ∈ R ∩ lvars_of_atoms (dom (σ : StoreT))));
        destruct (decide (v ∈ (R ∩ lvars_of_atoms (dom (σ : StoreT))) ∩
          lvars_of_atoms (dom (σ : StoreT)))); try reflexivity; set_solver.
    }
    pose proof (basic_world_formula_union
      (lty_env_msubst_store σR Σg)
      (storeA_restrict Σ (R ∩ lvars_of_atoms (dom (σ : StoreT))))
      m Hres Hfixed) as Hbig.
    eapply basic_world_formula_subenv; [exact Htgt_sub_big|exact Hbig].
  - intros Htgt.
    assert (Hres :
      m ⊨ basic_world_formula (lty_env_msubst_store σR Σg)).
    {
      eapply basic_world_formula_subenv; [exact Hres_sub_tgt|exact Htgt].
    }
    pose proof (basic_world_formula_msubst_store_models_back σR Σg m
      HσRty Hres) as HsrcR.
    rewrite (formula_msubst_store_restrict_fv_subset σ
      (basic_world_formula Σg) (lvars_fv R) Hfv_src).
    fold σR. exact HsrcR.
  Unshelve.
Qed.

Lemma basic_world_formula_msubst_store_singleton_iff
    σ Σ τ e (m : WfWorldT) :
  basic_context_ty_lvars (dom Σ) τ ->
  tm_lvars e ⊆ dom Σ ->
  atom_store_has_ltype Σ σ ->
  (res_restrict m (lvars_fv (denot_relevant_lvars τ e)) : WorldT) =
    singleton_world (store_restrict σ (lvars_fv (denot_relevant_lvars τ e))) ->
  m ⊨ formula_msubst_store σ
    (basic_world_formula (denot_relevant_env Σ τ e)) <->
  m ⊨ basic_world_formula
    (denot_relevant_env Σ τ
      (lstore_instantiate_tm (lstore_lift_free σ) e)).
Proof.
  intros Hwf He Hσty Hsingle.
  eapply basic_world_formula_msubst_store_fixed_singleton_iff; eauto.
  set (Y := lvars_fv (denot_relevant_lvars τ e ∩
    lvars_of_atoms (dom (σ : StoreT)))).
  assert (HY : Y ⊆ lvars_fv (denot_relevant_lvars τ e)).
  {
    subst Y. intros x Hx.
    apply lvars_fv_elem in Hx as Hv.
    apply elem_of_intersection in Hv as [Hv _].
    apply lvars_fv_elem. exact Hv.
  }
  pose proof (res_restrict_singleton_subset m
    (lvars_fv (denot_relevant_lvars τ e)) Y
    (store_restrict σ (lvars_fv (denot_relevant_lvars τ e)))
    HY Hsingle) as Hfix.
  subst Y.
  rewrite storeA_restrict_twice_subset in Hfix by assumption.
  exact Hfix.
Qed.

Lemma denot_relevant_lvars_tm_msubst_store
    σ τ e :
  store_closed σ ->
  denot_relevant_lvars τ
    (lstore_instantiate_tm (lstore_lift_free σ) e) =
  context_ty_lvars τ ∪
    (tm_lvars e ∖ dom (lstore_lift_free σ : LStoreT)).
Proof.
  intros Hclosed.
  unfold denot_relevant_lvars.
  rewrite (tm_lvars_lstore_instantiate_lift_free_closed σ e Hclosed).
  reflexivity.
Qed.

Lemma denot_relevant_env_msubst_residual_sub_target
    σ Σ τ e :
  store_closed σ ->
  let R := denot_relevant_lvars τ e in
  let e' := lstore_instantiate_tm (lstore_lift_free σ) e in
  let Σg := denot_relevant_env Σ τ e in
  let Σg' := denot_relevant_env Σ τ e' in
  let σR := (store_restrict σ (lvars_fv R) : StoreT) in
  forall v T,
    lty_env_msubst_store σR Σg !! v = Some T ->
    Σg' !! v = Some T.
Proof.
  intros Hclosed R e' Σg Σg' σR v T Hlook.
  subst σR Σg Σg' R e'.
  apply lty_env_msubst_store_lookup_some in Hlook as [Hlook Hfresh].
  unfold denot_relevant_env, lty_env_restrict_lvars in *.
  apply storeA_restrict_lookup_some in Hlook as [HvR HΣv].
  apply storeA_restrict_lookup_some_2; [exact HΣv|].
  rewrite denot_relevant_lvars_tm_msubst_store by exact Hclosed.
  unfold denot_relevant_lvars in HvR.
  apply elem_of_union in HvR as [Hvτ|Hve].
  - apply elem_of_union_l. exact Hvτ.
  - apply elem_of_union_r.
    apply elem_of_difference. split; [exact Hve|].
    intros Hvfixed. apply Hfresh.
    rewrite dom_lstore_lift_free in Hvfixed.
    unfold lvars_of_atoms in Hvfixed.
    apply elem_of_map in Hvfixed as [x [-> Hx]].
    apply elem_of_dom in Hx as [vx Hx].
    unfold lvars_of_atoms. apply elem_of_map.
    exists x. split; [reflexivity|].
    apply elem_of_dom. exists vx.
    apply storeA_restrict_lookup_some_2; [exact Hx|].
    apply lvars_fv_elem. unfold denot_relevant_lvars.
    apply elem_of_union_r. exact Hve.
Qed.

Lemma denot_relevant_env_msubst_residual_dom_subset_target
    σ Σ τ e :
  store_closed σ ->
  let R := denot_relevant_lvars τ e in
  let e' := lstore_instantiate_tm (lstore_lift_free σ) e in
  let Σg := denot_relevant_env Σ τ e in
  let Σg' := denot_relevant_env Σ τ e' in
  let σR := (store_restrict σ (lvars_fv R) : StoreT) in
  dom (lty_env_msubst_store σR Σg) ⊆ dom Σg'.
Proof.
  intros Hclosed R e' Σg Σg' σR v Hv.
  apply elem_of_dom in Hv as [T Hlook].
  eapply elem_of_dom_2.
  eapply denot_relevant_env_msubst_residual_sub_target; eauto.
Qed.

Lemma denot_relevant_env_msubst_target_scope_from_residual
    σ Σ τ e (m : WfWorldT) :
  store_closed σ ->
  let R := denot_relevant_lvars τ e in
  let e' := lstore_instantiate_tm (lstore_lift_free σ) e in
  let Σg := denot_relevant_env Σ τ e in
  let Σg' := denot_relevant_env Σ τ e' in
  let σR := (store_restrict σ (lvars_fv R) : StoreT) in
  dom (σ : StoreT) ∩ lvars_fv R ⊆ world_dom (m : WorldT) ->
  lvars_fv (dom (lty_env_msubst_store σR Σg)) ⊆ world_dom (m : WorldT) ->
  lvars_fv (dom Σg') ⊆ world_dom (m : WorldT).
Proof.
  intros Hclosed R e' Σg Σg' σR Hfixed_scope Hres_scope x Hx.
  subst σR Σg Σg' R e'.
  rewrite lvars_fv_elem in Hx.
  unfold denot_relevant_env, lty_env_restrict_lvars in Hx.
  apply elem_of_dom in Hx as [T Hlook].
  apply storeA_restrict_lookup_some in Hlook as [HvR' HΣv].
  rewrite denot_relevant_lvars_tm_msubst_store in HvR' by exact Hclosed.
  unfold denot_relevant_lvars.
  destruct (decide (x ∈ dom (σ : StoreT))) as [Hxσ|Hxσ].
  - assert (HxR : x ∈ lvars_fv (context_ty_lvars τ ∪ tm_lvars e)).
    {
      apply elem_of_union in HvR' as [Hvτ|Hve].
      - rewrite lvars_fv_union. apply elem_of_union_l.
        apply lvars_fv_elem. exact Hvτ.
      - apply elem_of_difference in Hve as [Hve _].
        rewrite lvars_fv_union. apply elem_of_union_r.
        apply lvars_fv_elem. exact Hve.
    }
    assert (HxσR : x ∈
      dom (store_restrict σ
        (lvars_fv (context_ty_lvars τ ∪ tm_lvars e)) : StoreT)).
    {
      change (x ∈ dom (σ : gmap atom value)) in Hxσ.
      apply elem_of_dom in Hxσ as [vx Hσx].
      eapply elem_of_dom_2.
      apply storeA_restrict_lookup_some_2; [exact Hσx|exact HxR].
    }
    apply Hfixed_scope.
    apply elem_of_intersection. split; [exact Hxσ|exact HxR].
  - apply Hres_scope.
    rewrite lvars_fv_elem.
    apply elem_of_dom.
    exists T.
    apply lty_env_msubst_store_lookup_some_2.
    + unfold denot_relevant_env, lty_env_restrict_lvars.
      apply storeA_restrict_lookup_some_2; [exact HΣv|].
      unfold denot_relevant_lvars.
      apply elem_of_union in HvR' as [Hvτ|Hve].
      * apply elem_of_union_l. exact Hvτ.
      * apply elem_of_union_r.
        apply elem_of_difference in Hve as [Hve _]. exact Hve.
    + unfold lvars_of_atoms. rewrite elem_of_map.
      intros (a & Heq & Ha). inversion Heq; subst.
      apply Hxσ.
      rewrite storeA_restrict_dom in Ha.
      apply elem_of_intersection in Ha as [Ha _].
      exact Ha.
  Unshelve.
  all: try typeclasses eauto.
  all: try exact gmap_fmap.
  all: try exact gmap_omap.
  all: try exact gmap_merge.
  all: try exact gset_dom_spec.
Qed.

Lemma denot_relevant_env_msubst_target_lc_from_residual
    σ Σ τ e :
  store_closed σ ->
  let R := denot_relevant_lvars τ e in
  let e' := lstore_instantiate_tm (lstore_lift_free σ) e in
  let Σg := denot_relevant_env Σ τ e in
  let Σg' := denot_relevant_env Σ τ e' in
  let σR := (store_restrict σ (lvars_fv R) : StoreT) in
  lc_lvars (dom (lty_env_msubst_store σR Σg)) ->
  lc_lvars (dom Σg').
Proof.
  intros Hclosed R e' Σg Σg' σR Hlc v Hv.
  subst σR Σg Σg' R e'.
  destruct v as [k|x]; [|exact I].
  exfalso.
  assert (Hvres : LVBound k ∈
      dom (lty_env_msubst_store
        (store_restrict σ (lvars_fv (denot_relevant_lvars τ e)))
        (denot_relevant_env Σ τ e))).
  {
    apply elem_of_dom in Hv as [T Hlook].
    unfold denot_relevant_env, lty_env_restrict_lvars in Hlook.
    apply storeA_restrict_lookup_some in Hlook as [HvR' HΣv].
    rewrite denot_relevant_lvars_tm_msubst_store in HvR' by exact Hclosed.
    apply elem_of_dom. exists T.
    apply lty_env_msubst_store_lookup_some_2.
    - unfold denot_relevant_env, lty_env_restrict_lvars.
      apply storeA_restrict_lookup_some_2; [exact HΣv|].
      unfold denot_relevant_lvars.
      apply elem_of_union in HvR' as [Hvτ|Hve].
      + apply elem_of_union_l. exact Hvτ.
      + apply elem_of_union_r.
        apply elem_of_difference in Hve as [Hve _]. exact Hve.
    - unfold lvars_of_atoms. rewrite elem_of_map.
      intros (a & Hbad & _). discriminate.
  }
  exact (Hlc _ Hvres).
Qed.

Lemma denot_relevant_env_msubst_residual_restrict_target
    σ Σ τ e :
  store_closed σ ->
  let R := denot_relevant_lvars τ e in
  let e' := lstore_instantiate_tm (lstore_lift_free σ) e in
  let Σg := denot_relevant_env Σ τ e in
  let Σg' := denot_relevant_env Σ τ e' in
  let σR := (store_restrict σ (lvars_fv R) : StoreT) in
  storeA_restrict Σg' (dom (lty_env_msubst_store σR Σg)) =
  lty_env_msubst_store σR Σg.
Proof.
  intros Hclosed R e' Σg Σg' σR.
  apply storeA_map_eq. intros v.
  destruct ((lty_env_msubst_store σR Σg : lty_env) !! v) as [T|] eqn:Hres.
  - apply storeA_restrict_lookup_some_2.
    + eapply denot_relevant_env_msubst_residual_sub_target; eauto.
    + eapply elem_of_dom_2. exact Hres.
  - destruct ((storeA_restrict Σg'
      (dom (lty_env_msubst_store σR Σg)) : lty_env) !! v) as [T|] eqn:Htgt;
      [|reflexivity].
    apply storeA_restrict_lookup_some in Htgt as [Hvdom _].
    apply elem_of_dom in Hvdom as [T' Hbad].
    change (((lty_env_msubst_store σR Σg : lty_env) !! v) = None) in Hres.
    rewrite Hbad in Hres. discriminate.
Qed.

Lemma denot_relevant_env_msubst_tm_lvars_residual
    σ Σ τ e :
  store_closed σ ->
  tm_lvars e ⊆ dom Σ ->
  let R := denot_relevant_lvars τ e in
  let e' := lstore_instantiate_tm (lstore_lift_free σ) e in
  let Σg := denot_relevant_env Σ τ e in
  let σR := (store_restrict σ (lvars_fv R) : StoreT) in
  tm_lvars e' ⊆ dom (lty_env_msubst_store σR Σg).
Proof.
  intros Hclosed He R e' Σg σR v Hv.
  subst σR Σg R e'.
  rewrite (tm_lvars_lstore_instantiate_lift_free_closed σ e Hclosed) in Hv.
  apply elem_of_difference in Hv as [Hve Hvfresh].
  rewrite lty_env_msubst_store_dom.
  apply elem_of_difference. split.
  - unfold denot_relevant_env, lty_env_restrict_lvars.
    rewrite storeA_restrict_dom.
    apply elem_of_intersection. split.
    + exact (He _ Hve).
    + unfold denot_relevant_lvars. apply elem_of_union_r. exact Hve.
  - intros HvσR. apply Hvfresh.
    rewrite dom_lstore_lift_free.
    unfold lvars_of_atoms in HvσR |- *.
    apply elem_of_map in HvσR as [x [-> HxσR]].
    apply elem_of_map. exists x. split; [reflexivity|].
    rewrite storeA_restrict_dom in HxσR.
    apply elem_of_intersection in HxσR as [Hxσ _].
    exact Hxσ.
Qed.

Lemma expr_basic_typing_formula_msubst_store_iff
    σ Σ τ e T (m : WfWorldT) :
  basic_context_ty_lvars (dom Σ) τ ->
  tm_lvars e ⊆ dom Σ ->
  lc_tm e ->
  atom_store_has_ltype Σ σ ->
  dom (σ : StoreT) ∩ lvars_fv (denot_relevant_lvars τ e) ⊆
    world_dom (m : WorldT) ->
  m ⊨ formula_msubst_store σ
    (expr_basic_typing_formula (denot_relevant_env Σ τ e) e T) <->
  m ⊨ expr_basic_typing_formula
    (denot_relevant_env Σ τ
      (lstore_instantiate_tm (lstore_lift_free σ) e))
    (lstore_instantiate_tm (lstore_lift_free σ) e) T.
Proof.
  intros Hwf He Hlc Hσty Hfixed_scope.
  pose proof (atom_store_has_ltype_closed _ _ Hσty) as Hclosed.
  set (R := denot_relevant_lvars τ e).
  set (e' := lstore_instantiate_tm (lstore_lift_free σ) e).
  set (Σg := denot_relevant_env Σ τ e).
  set (Σg' := denot_relevant_env Σ τ e').
  set (σR := (store_restrict σ (lvars_fv R) : StoreT)).
  assert (HσRty : atom_store_has_ltype Σg σR).
  {
    subst σR Σg R.
    apply atom_store_has_ltype_denot_relevant_env.
    - intros v Hv.
      unfold denot_relevant_lvars.
      unfold lvars_of_atoms in Hv.
      apply elem_of_map in Hv as [x [-> Hx]].
      apply elem_of_dom in Hx as [vx Hx].
      apply storeA_restrict_lookup_some in Hx as [HxR _].
      apply lvars_fv_elem in HxR. exact HxR.
    - intros x v Hlook.
      apply storeA_restrict_lookup_some in Hlook as [_ Hlook].
      exact (Hσty x v Hlook).
  }
  assert (Hfv_src :
    formula_fv (expr_basic_typing_formula Σg e T) ⊆ lvars_fv R).
  {
    subst Σg. rewrite formula_fv_expr_basic_typing_formula.
    apply lty_env_restrict_lvars_fv_subset.
  }
  assert (Heq_e' :
    lstore_instantiate_tm (lstore_lift_free σR) e = e').
  {
    subst σR e' R.
    eapply (lstore_instantiate_tm_lift_free_agree_subset
      _ _ _ (fv_tm e)).
    - reflexivity.
    - rewrite storeA_restrict_restrict.
      replace (lvars_fv (denot_relevant_lvars τ e) ∩ fv_tm e)
        with (fv_tm e).
      2: {
        unfold denot_relevant_lvars.
        rewrite lvars_fv_union, tm_lvars_fv. set_solver.
      }
      reflexivity.
  }
  split.
  - intros Hsrc.
    rewrite (formula_msubst_store_restrict_fv_subset σ
      (expr_basic_typing_formula Σg e T) (lvars_fv R) Hfv_src) in Hsrc.
    fold σR in Hsrc.
    pose proof (expr_basic_typing_formula_msubst_store_models
      σR Σg e T m HσRty Hsrc) as Hres.
    apply expr_basic_typing_formula_models_iff in Hres
      as [Hlc_res [Hscope_res Hbasic_res]].
    rewrite Heq_e' in Hbasic_res.
    apply expr_basic_typing_formula_models_iff.
    split.
    + eapply denot_relevant_env_msubst_target_lc_from_residual; eauto.
    + split.
      * eapply denot_relevant_env_msubst_target_scope_from_residual; eauto.
      * eapply basic_tm_has_ltype_weaken; [exact Hbasic_res|].
        apply map_subseteq_spec. intros v U Hlook.
        eapply denot_relevant_env_msubst_residual_sub_target; eauto.
  - intros Htgt.
    apply expr_basic_typing_formula_models_iff in Htgt
      as [Hlc_tgt [Hscope_tgt Hbasic_tgt]].
    assert (Hres_lc : lc_lvars (dom (lty_env_msubst_store σR Σg))).
    {
      intros v Hv.
      apply Hlc_tgt.
      eapply denot_relevant_env_msubst_residual_dom_subset_target; eauto.
    }
    assert (Hres_scope :
      lvars_fv (dom (lty_env_msubst_store σR Σg)) ⊆ world_dom (m : WorldT)).
    {
      intros x Hx.
      apply Hscope_tgt.
      rewrite lvars_fv_elem in Hx |- *.
      eapply denot_relevant_env_msubst_residual_dom_subset_target; eauto.
    }
    assert (Hbasic_res :
      basic_tm_has_ltype (lty_env_msubst_store σR Σg) e' T).
    {
      pose proof (denot_relevant_env_msubst_residual_restrict_target
        σ Σ τ e Hclosed) as Hres_eq.
      fold R e' Σg Σg' σR in Hres_eq.
      replace (lty_env_msubst_store σR Σg)
        with (storeA_restrict Σg' (dom (lty_env_msubst_store σR Σg)))
        by exact Hres_eq.
      eapply basic_tm_has_ltype_restrict_lvars_lc.
      - exact Hbasic_tgt.
      - subst e'. apply lstore_instantiate_tm_lift_free_lc; assumption.
      - subst e' R Σg σR.
        eapply denot_relevant_env_msubst_tm_lvars_residual; eauto.
    }
    assert (Hres :
      m ⊨ expr_basic_typing_formula (lty_env_msubst_store σR Σg) e' T).
    {
      apply expr_basic_typing_formula_models_iff.
      repeat split; assumption.
    }
    rewrite <- Heq_e' in Hres.
    pose proof (expr_basic_typing_formula_msubst_store_models_back
      σR Σg e T m HσRty Hres) as HsrcR.
    rewrite (formula_msubst_store_restrict_fv_subset σ
      (expr_basic_typing_formula Σg e T) (lvars_fv R) Hfv_src).
    fold σR. exact HsrcR.
Qed.

Lemma expr_basic_typing_formula_msubst_store_singleton_iff
    σ Σ τ e T (m : WfWorldT) :
  basic_context_ty_lvars (dom Σ) τ ->
  tm_lvars e ⊆ dom Σ ->
  lc_tm e ->
  atom_store_has_ltype Σ σ ->
  (res_restrict m (lvars_fv (denot_relevant_lvars τ e)) : WorldT) =
    singleton_world (store_restrict σ (lvars_fv (denot_relevant_lvars τ e))) ->
  m ⊨ formula_msubst_store σ
    (expr_basic_typing_formula (denot_relevant_env Σ τ e) e T) <->
  m ⊨ expr_basic_typing_formula
    (denot_relevant_env Σ τ
      (lstore_instantiate_tm (lstore_lift_free σ) e))
    (lstore_instantiate_tm (lstore_lift_free σ) e) T.
Proof.
  intros Hwf He Hlc Hσty Hsingle.
  eapply expr_basic_typing_formula_msubst_store_iff; eauto.
  pose proof (f_equal world_dom Hsingle) as Hdom.
  simpl in Hdom.
  rewrite storeA_restrict_dom in Hdom.
  set_solver.
Qed.

Lemma denot_guard_msubst_store_singleton_iff
    σ Σ τ e (m : WfWorldT) :
  basic_context_ty_lvars (dom Σ) τ ->
  tm_lvars e ⊆ dom Σ ->
  lc_tm e ->
  atom_store_has_ltype Σ σ ->
  (res_restrict m (lvars_fv (denot_relevant_lvars τ e)) : WorldT) =
    singleton_world (store_restrict σ (lvars_fv (denot_relevant_lvars τ e))) ->
  res_models m
    (formula_msubst_store σ
      (FAnd (context_ty_wf_formula (denot_relevant_env Σ τ e) τ)
        (FAnd (basic_world_formula (denot_relevant_env Σ τ e))
          (FAnd
            (expr_basic_typing_formula (denot_relevant_env Σ τ e) e
              (erase_ty τ))
            (expr_total_formula e))))) <->
  res_models m
    (FAnd (context_ty_wf_formula
        (denot_relevant_env Σ τ
          (lstore_instantiate_tm (lstore_lift_free σ) e)) τ)
      (FAnd (basic_world_formula
          (denot_relevant_env Σ τ
            (lstore_instantiate_tm (lstore_lift_free σ) e)))
        (FAnd
          (expr_basic_typing_formula
            (denot_relevant_env Σ τ
              (lstore_instantiate_tm (lstore_lift_free σ) e))
            (lstore_instantiate_tm (lstore_lift_free σ) e)
            (erase_ty τ))
          (expr_total_formula
            (lstore_instantiate_tm (lstore_lift_free σ) e))))).
Proof.
  intros Hwf He Hlc Hσty Hsingleton.
  formula_msubst_syntax_norm.
  rewrite !res_models_and_iff.
  split.
  - intros [Hwf_src [Hworld_src [Hbasic_src Htotal_src]]].
    split.
    + eapply context_ty_wf_formula_msubst_store_singleton_iff; eauto.
    + split.
      * eapply basic_world_formula_msubst_store_singleton_iff; eauto.
      * split.
        -- eapply expr_basic_typing_formula_msubst_store_singleton_iff; eauto.
        -- eapply expr_total_formula_msubst_store_singleton_iff; eauto.
  - intros [Hwf_tgt [Hworld_tgt [Hbasic_tgt Htotal_tgt]]].
    split.
    + eapply context_ty_wf_formula_msubst_store_singleton_iff; eauto.
    + split.
      * eapply basic_world_formula_msubst_store_singleton_iff; eauto.
      * split.
        -- eapply expr_basic_typing_formula_msubst_store_singleton_iff; eauto.
        -- eapply expr_total_formula_msubst_store_singleton_iff; eauto.
Qed.

Lemma denot_guard_msubst_store_base_projection_iff
    σ Σbase Σ τ e (m : WfWorldT) :
  basic_context_ty_lvars (dom Σ) τ ->
  tm_lvars e ⊆ dom Σ ->
  lc_tm e ->
  atom_store_has_ltype Σ σ ->
  base_store_projection Σbase σ m ->
  res_models m
    (formula_msubst_store σ
      (FAnd (context_ty_wf_formula (denot_relevant_env Σ τ e) τ)
        (FAnd (basic_world_formula (denot_relevant_env Σ τ e))
          (FAnd
            (expr_basic_typing_formula (denot_relevant_env Σ τ e) e
              (erase_ty τ))
            (expr_total_formula e))))) <->
  res_models m
    (FAnd (context_ty_wf_formula
        (denot_relevant_env Σ τ
          (lstore_instantiate_tm (lstore_lift_free σ) e)) τ)
      (FAnd (basic_world_formula
          (denot_relevant_env Σ τ
            (lstore_instantiate_tm (lstore_lift_free σ) e)))
        (FAnd
          (expr_basic_typing_formula
            (denot_relevant_env Σ τ
              (lstore_instantiate_tm (lstore_lift_free σ) e))
            (lstore_instantiate_tm (lstore_lift_free σ) e)
            (erase_ty τ))
          (expr_total_formula
            (lstore_instantiate_tm (lstore_lift_free σ) e))))).
Proof.
  intros Hwf He Hlc Hσty Hproj.
  pose proof (base_store_projection_dom_subset_world _ _ _ Hproj)
    as Hσ_scope.
  assert (Hfixed_scope :
    dom (σ : StoreT) ∩ lvars_fv (denot_relevant_lvars τ e) ⊆
      world_dom (m : WorldT)).
  { set_solver. }
  assert (Hfixed_singleton :
    (res_restrict m
      (lvars_fv (denot_relevant_lvars τ e ∩
        lvars_of_atoms (dom (σ : StoreT)))) : WorldT) =
      singleton_world
        (store_restrict σ
          (lvars_fv (denot_relevant_lvars τ e ∩
            lvars_of_atoms (dom (σ : StoreT)))))).
  {
    eapply base_store_projection_restrict; [|exact Hproj].
    intros x Hx.
    destruct Hproj as [Hdom _].
    apply lvars_fv_elem in Hx as Hv.
    apply elem_of_intersection in Hv as [_ Hvσ].
    unfold lvars_of_atoms in Hvσ.
    apply elem_of_map in Hvσ as [a [Heq Ha]].
    inversion Heq; subst.
    rewrite <- Hdom. exact Ha.
  }
  formula_msubst_syntax_norm.
  rewrite !res_models_and_iff.
  split.
  - intros [Hwf_src [Hworld_src [Hbasic_src Htotal_src]]].
    split.
    + eapply context_ty_wf_formula_msubst_store_fixed_scope_iff; eauto.
    + split.
      * eapply basic_world_formula_msubst_store_fixed_singleton_iff; eauto.
      * split.
        -- eapply expr_basic_typing_formula_msubst_store_iff; eauto.
        -- eapply expr_total_formula_msubst_store_singleton_iff; eauto.
  - intros [Hwf_tgt [Hworld_tgt [Hbasic_tgt Htotal_tgt]]].
    split.
    + eapply context_ty_wf_formula_msubst_store_fixed_scope_iff; eauto.
    + split.
      * eapply basic_world_formula_msubst_store_fixed_singleton_iff; eauto.
      * split.
        -- eapply expr_basic_typing_formula_msubst_store_iff; eauto.
        -- eapply expr_total_formula_msubst_store_singleton_iff; eauto.
Qed.

Lemma denot_guard_msubst_store_local_singleton_iff
    σ Σ τ e (m : WfWorldT) :
  basic_context_ty_lvars (dom Σ) τ ->
  tm_lvars e ⊆ dom Σ ->
  lc_tm e ->
  atom_store_has_ltype Σ σ ->
  store_singleton_projection σ m ->
  res_models m
    (formula_msubst_store σ
      (FAnd (context_ty_wf_formula (denot_relevant_env Σ τ e) τ)
        (FAnd (basic_world_formula (denot_relevant_env Σ τ e))
          (FAnd
            (expr_basic_typing_formula (denot_relevant_env Σ τ e)
              e (erase_ty τ))
            (expr_total_formula e))))) <->
  res_models m
    (FAnd (context_ty_wf_formula
        (denot_relevant_env Σ τ
          (lstore_instantiate_tm (lstore_lift_free σ) e)) τ)
      (FAnd (basic_world_formula
          (denot_relevant_env Σ τ
            (lstore_instantiate_tm (lstore_lift_free σ) e)))
        (FAnd
          (expr_basic_typing_formula
            (denot_relevant_env Σ τ
              (lstore_instantiate_tm (lstore_lift_free σ) e))
            (lstore_instantiate_tm (lstore_lift_free σ) e)
            (erase_ty τ))
          (expr_total_formula
            (lstore_instantiate_tm (lstore_lift_free σ) e))))).
Proof.
  intros Hwf He Hlc Hσty Hproj.
  assert (Hfixed_scope :
    dom (σ : StoreT) ∩ lvars_fv (denot_relevant_lvars τ e) ⊆
      world_dom (m : WorldT)).
  {
    pose proof (store_singleton_projection_dom_subset_world σ m Hproj)
      as Hdom.
    set_solver.
  }
  assert (Hfixed_singleton :
    (res_restrict m
      (lvars_fv (denot_relevant_lvars τ e ∩
        lvars_of_atoms (dom (σ : StoreT)))) : WorldT) =
      singleton_world
        (store_restrict σ
          (lvars_fv (denot_relevant_lvars τ e ∩
            lvars_of_atoms (dom (σ : StoreT)))))).
  {
    eapply store_singleton_projection_restrict.
    - rewrite lvars_fv_intersection_of_atoms. set_solver.
    - exact Hproj.
  }
  formula_msubst_syntax_norm.
  rewrite !res_models_and_iff.
  split.
  - intros [Hwf_src [Hworld_src [Hbasic_src Htotal_src]]].
    split.
    + eapply context_ty_wf_formula_msubst_store_fixed_scope_iff; eauto.
    + split.
      * eapply basic_world_formula_msubst_store_fixed_singleton_iff; eauto.
      * split.
        -- eapply expr_basic_typing_formula_msubst_store_iff; eauto.
        -- eapply expr_total_formula_msubst_store_singleton_iff; eauto.
  - intros [Hwf_tgt [Hworld_tgt [Hbasic_tgt Htotal_tgt]]].
    split.
    + eapply context_ty_wf_formula_msubst_store_fixed_scope_iff; eauto.
    + split.
      * eapply basic_world_formula_msubst_store_fixed_singleton_iff; eauto.
      * split.
        -- eapply expr_basic_typing_formula_msubst_store_iff; eauto.
        -- eapply expr_total_formula_msubst_store_singleton_iff; eauto.
Qed.

Lemma denot_ty_lvar_gas_zero_msubst_store_singleton_iff
    σ Σ τ e (m : WfWorldT) :
  basic_context_ty_lvars (dom Σ) τ ->
  tm_lvars e ⊆ dom Σ ->
  lc_tm e ->
  atom_store_has_ltype Σ σ ->
  (res_restrict m (lvars_fv (denot_relevant_lvars τ e)) : WorldT) =
    singleton_world (store_restrict σ (lvars_fv (denot_relevant_lvars τ e))) ->
  res_models m (formula_msubst_store σ (denot_ty_lvar_gas 0 Σ τ e)) <->
  res_models m (denot_ty_lvar_gas 0 Σ τ
    (lstore_instantiate_tm (lstore_lift_free σ) e)).
Proof.
  intros Hwf He Hlc Hσty Hsingleton.
  cbn [denot_ty_lvar_gas].
  formula_msubst_syntax_norm.
  rewrite !res_models_and_iff.
  pose proof (denot_guard_msubst_store_singleton_iff σ Σ τ e m
    Hwf He Hlc Hσty Hsingleton) as Hguard.
  split.
  - intros [Hguard_src Htrue].
    assert (Hguard_src0 :
      m ⊨ formula_msubst_store σ
        (FAnd (context_ty_wf_formula (denot_relevant_env Σ τ e) τ)
          (FAnd (basic_world_formula (denot_relevant_env Σ τ e))
            (FAnd
              (expr_basic_typing_formula (denot_relevant_env Σ τ e) e
                (erase_ty τ))
              (expr_total_formula e))))).
    {
      formula_msubst_syntax_norm.
      repeat rewrite res_models_and_iff.
      exact Hguard_src.
    }
    pose proof (proj1 Hguard Hguard_src0) as Hguard_tgt.
    repeat rewrite res_models_and_iff in Hguard_tgt.
    split; [exact Hguard_tgt|exact Htrue].
  - intros [Hguard_tgt Htrue].
    assert (Hguard_tgt0 :
      m ⊨
        (FAnd (context_ty_wf_formula
            (denot_relevant_env Σ τ
              (lstore_instantiate_tm (lstore_lift_free σ) e)) τ)
          (FAnd (basic_world_formula
              (denot_relevant_env Σ τ
                (lstore_instantiate_tm (lstore_lift_free σ) e)))
            (FAnd
              (expr_basic_typing_formula
                (denot_relevant_env Σ τ
                  (lstore_instantiate_tm (lstore_lift_free σ) e))
                (lstore_instantiate_tm (lstore_lift_free σ) e)
                (erase_ty τ))
              (expr_total_formula
                (lstore_instantiate_tm (lstore_lift_free σ) e)))))).
    {
      repeat rewrite res_models_and_iff.
      exact Hguard_tgt.
    }
    pose proof (proj2 Hguard Hguard_tgt0) as Hguard_src.
    formula_msubst_syntax_norm_in Hguard_src.
    repeat rewrite res_models_and_iff in Hguard_src.
    split; [exact Hguard_src|exact Htrue].
Qed.

Lemma denot_ty_lvar_gas_zero_msubst_store_base_projection_iff
    σ Σbase Σ τ e (m : WfWorldT) :
  basic_context_ty_lvars (dom Σ) τ ->
  tm_lvars e ⊆ dom Σ ->
  lc_tm e ->
  atom_store_has_ltype Σ σ ->
  base_store_projection Σbase σ m ->
  res_models m (formula_msubst_store σ (denot_ty_lvar_gas 0 Σ τ e)) <->
  res_models m (denot_ty_lvar_gas 0 Σ τ
    (lstore_instantiate_tm (lstore_lift_free σ) e)).
Proof.
  intros Hwf He Hlc Hσty Hproj.
  cbn [denot_ty_lvar_gas].
  formula_msubst_syntax_norm.
  rewrite !res_models_and_iff.
  pose proof (denot_guard_msubst_store_base_projection_iff
    σ Σbase Σ τ e m Hwf He Hlc Hσty Hproj) as Hguard.
  split.
  - intros [Hguard_src Htrue].
    assert (Hguard_src0 :
      m ⊨ formula_msubst_store σ
        (FAnd (context_ty_wf_formula (denot_relevant_env Σ τ e) τ)
          (FAnd (basic_world_formula (denot_relevant_env Σ τ e))
            (FAnd
              (expr_basic_typing_formula (denot_relevant_env Σ τ e) e
                (erase_ty τ))
              (expr_total_formula e))))).
    {
      formula_msubst_syntax_norm.
      repeat rewrite res_models_and_iff.
      exact Hguard_src.
    }
    pose proof (proj1 Hguard Hguard_src0) as Hguard_tgt.
    repeat rewrite res_models_and_iff in Hguard_tgt.
    split; [exact Hguard_tgt|exact Htrue].
  - intros [Hguard_tgt Htrue].
    assert (Hguard_tgt0 :
      m ⊨
        (FAnd (context_ty_wf_formula
            (denot_relevant_env Σ τ
              (lstore_instantiate_tm (lstore_lift_free σ) e)) τ)
          (FAnd (basic_world_formula
              (denot_relevant_env Σ τ
                (lstore_instantiate_tm (lstore_lift_free σ) e)))
            (FAnd
              (expr_basic_typing_formula
                (denot_relevant_env Σ τ
                  (lstore_instantiate_tm (lstore_lift_free σ) e))
                (lstore_instantiate_tm (lstore_lift_free σ) e)
                (erase_ty τ))
              (expr_total_formula
                (lstore_instantiate_tm (lstore_lift_free σ) e)))))).
    {
      repeat rewrite res_models_and_iff.
      exact Hguard_tgt.
    }
    pose proof (proj2 Hguard Hguard_tgt0) as Hguard_src.
    formula_msubst_syntax_norm_in Hguard_src.
    repeat rewrite res_models_and_iff in Hguard_src.
    split; [exact Hguard_src|exact Htrue].
Qed.

Lemma denot_ty_lvar_gas_zero_msubst_store_local_singleton_iff
    σ Σ τ e (m : WfWorldT) :
  basic_context_ty_lvars (dom Σ) τ ->
  tm_lvars e ⊆ dom Σ ->
  lc_tm e ->
  atom_store_has_ltype Σ σ ->
  store_singleton_projection σ m ->
  res_models m (formula_msubst_store σ (denot_ty_lvar_gas 0 Σ τ e)) <->
  res_models m (denot_ty_lvar_gas 0 Σ τ
    (lstore_instantiate_tm (lstore_lift_free σ) e)).
Proof.
  intros Hwf He Hlc Hσty Hproj.
  cbn [denot_ty_lvar_gas].
  formula_msubst_syntax_norm.
  rewrite !res_models_and_iff.
  pose proof (denot_guard_msubst_store_local_singleton_iff
    σ Σ τ e m Hwf He Hlc Hσty Hproj) as Hguard.
  split.
  - intros [Hguard_src Htrue].
    assert (Hguard_src0 :
      m ⊨ formula_msubst_store σ
        (FAnd (context_ty_wf_formula (denot_relevant_env Σ τ e) τ)
          (FAnd (basic_world_formula (denot_relevant_env Σ τ e))
            (FAnd
              (expr_basic_typing_formula (denot_relevant_env Σ τ e) e
                (erase_ty τ))
              (expr_total_formula e))))).
    {
      formula_msubst_syntax_norm.
      repeat rewrite res_models_and_iff.
      exact Hguard_src.
    }
    pose proof (proj1 Hguard Hguard_src0) as Hguard_tgt.
    repeat rewrite res_models_and_iff in Hguard_tgt.
    split; [exact Hguard_tgt|exact Htrue].
  - intros [Hguard_tgt Htrue].
    assert (Hguard_tgt0 :
      m ⊨
        (FAnd (context_ty_wf_formula
            (denot_relevant_env Σ τ
              (lstore_instantiate_tm (lstore_lift_free σ) e)) τ)
          (FAnd (basic_world_formula
              (denot_relevant_env Σ τ
                (lstore_instantiate_tm (lstore_lift_free σ) e)))
            (FAnd
              (expr_basic_typing_formula
                (denot_relevant_env Σ τ
                  (lstore_instantiate_tm (lstore_lift_free σ) e))
                (lstore_instantiate_tm (lstore_lift_free σ) e)
                (erase_ty τ))
              (expr_total_formula
                (lstore_instantiate_tm (lstore_lift_free σ) e)))))).
    {
      repeat rewrite res_models_and_iff.
      exact Hguard_tgt.
    }
    pose proof (proj2 Hguard Hguard_tgt0) as Hguard_src.
    formula_msubst_syntax_norm_in Hguard_src.
    repeat rewrite res_models_and_iff in Hguard_src.
    split; [exact Hguard_src|exact Htrue].
Qed.

Lemma denot_guard_msubst_store_models
    σ Σ τ e (m : WfWorldT) :
  lvars_of_atoms (dom (σ : gmap atom value)) ⊆ denot_relevant_lvars τ e ->
  atom_store_has_ltype Σ σ ->
  res_models m
    (formula_msubst_store σ
      (FAnd (context_ty_wf_formula (denot_relevant_env Σ τ e) τ)
        (FAnd (basic_world_formula (denot_relevant_env Σ τ e))
          (FAnd
            (expr_basic_typing_formula (denot_relevant_env Σ τ e) e
              (erase_ty τ))
            (expr_total_formula e))))) ->
  res_models m
    (FAnd
      (context_ty_wf_formula
        (denot_relevant_env (lty_env_msubst_store σ Σ)
          (context_ty_msubst_store σ τ)
          (lstore_instantiate_tm (lstore_lift_free σ) e))
        (context_ty_msubst_store σ τ))
      (FAnd
        (basic_world_formula
          (denot_relevant_env (lty_env_msubst_store σ Σ)
            (context_ty_msubst_store σ τ)
            (lstore_instantiate_tm (lstore_lift_free σ) e)))
        (FAnd
          (expr_basic_typing_formula
            (denot_relevant_env (lty_env_msubst_store σ Σ)
              (context_ty_msubst_store σ τ)
              (lstore_instantiate_tm (lstore_lift_free σ) e))
            (lstore_instantiate_tm (lstore_lift_free σ) e)
            (erase_ty (context_ty_msubst_store σ τ)))
          (expr_total_formula
            (lstore_instantiate_tm (lstore_lift_free σ) e))))).
Proof.
  intros Hσrel Hσty Hm.
  pose proof (atom_store_has_ltype_denot_relevant_env Σ σ τ e
    Hσrel Hσty) as Hσty_g.
  pose proof (atom_store_has_ltype_closed _ _ Hσty) as Hclosed.
  cbn [formula_msubst_store formula_mlsubst] in Hm.
  repeat rewrite res_models_and_iff in Hm.
  destruct Hm as [Hwf [Hworld [Hbasic Htotal]]].
  repeat rewrite res_models_and_iff.
  rewrite <- (denot_relevant_env_msubst_store σ Σ τ e Hclosed).
  split.
  - apply context_ty_wf_formula_msubst_store_models;
      [apply atom_store_has_ltype_dom_subset; exact Hσty_g|exact Hwf].
  - split.
    + apply basic_world_formula_msubst_store_models; [exact Hσty_g|exact Hworld].
    + split.
      * rewrite erase_ty_context_ty_msubst_store.
        apply expr_basic_typing_formula_msubst_store_models;
          [exact Hσty_g|exact Hbasic].
      * apply (expr_total_formula_msubst_store_models σ Σ e m);
          [exact Hσty|exact Htotal].
Qed.

Lemma denot_guard_msubst_store_models_back_relevant
    σ Σ τ e (m : WfWorldT) :
  denot_relevant_lvars τ e ⊆ dom Σ ->
  lvars_of_atoms (dom (σ : gmap atom value)) ⊆ denot_relevant_lvars τ e ->
  atom_store_has_ltype Σ σ ->
  res_models m
    (FAnd
      (context_ty_wf_formula
        (denot_relevant_env (lty_env_msubst_store σ Σ)
          (context_ty_msubst_store σ τ)
          (lstore_instantiate_tm (lstore_lift_free σ) e))
        (context_ty_msubst_store σ τ))
      (FAnd
        (basic_world_formula
          (denot_relevant_env (lty_env_msubst_store σ Σ)
            (context_ty_msubst_store σ τ)
            (lstore_instantiate_tm (lstore_lift_free σ) e)))
        (FAnd
          (expr_basic_typing_formula
            (denot_relevant_env (lty_env_msubst_store σ Σ)
              (context_ty_msubst_store σ τ)
              (lstore_instantiate_tm (lstore_lift_free σ) e))
            (lstore_instantiate_tm (lstore_lift_free σ) e)
            (erase_ty (context_ty_msubst_store σ τ)))
          (expr_total_formula
            (lstore_instantiate_tm (lstore_lift_free σ) e))))) ->
  res_models m
    (formula_msubst_store σ
      (FAnd (context_ty_wf_formula (denot_relevant_env Σ τ e) τ)
        (FAnd (basic_world_formula (denot_relevant_env Σ τ e))
          (FAnd
            (expr_basic_typing_formula (denot_relevant_env Σ τ e) e
              (erase_ty τ))
            (expr_total_formula e))))).
Proof.
  intros Hscope Hσrel Hσty Hm.
  pose proof (atom_store_has_ltype_denot_relevant_env Σ σ τ e
    Hσrel Hσty) as Hσty_g.
  pose proof (atom_store_has_ltype_closed _ _ Hσty) as Hclosed.
  rewrite <- (denot_relevant_env_msubst_store σ Σ τ e Hclosed) in Hm.
  rewrite erase_ty_context_ty_msubst_store in Hm.
  repeat rewrite res_models_and_iff in Hm.
  destruct Hm as [Hwf [Hworld [Hbasic Htotal]]].
  cbn [formula_msubst_store formula_mlsubst].
  repeat rewrite res_models_and_iff.
  split.
  - eapply context_ty_wf_formula_msubst_store_models_back.
    + intros v Hv.
      unfold denot_relevant_env, lty_env_restrict_lvars.
      apply elem_of_dom.
      assert (HvΣ : v ∈ dom Σ).
      {
        apply Hscope.
        unfold denot_relevant_lvars. set_solver.
      }
      apply elem_of_dom in HvΣ as [T HT].
      exists T. apply storeA_restrict_lookup_some_2; [exact HT|].
      unfold denot_relevant_lvars. set_solver.
    + exact Hwf.
  - split.
    + eapply basic_world_formula_msubst_store_models_back; eauto.
    + split.
      * eapply expr_basic_typing_formula_msubst_store_models_back; eauto.
      * eapply expr_total_formula_msubst_store_models_back; eauto.
Qed.

Lemma denot_ty_lvar_gas_zero_msubst_store_models_relevant
    σ Σ τ e (m : WfWorldT) :
  lvars_of_atoms (dom (σ : gmap atom value)) ⊆ denot_relevant_lvars τ e ->
  atom_store_has_ltype Σ σ ->
  res_models m (formula_msubst_store σ (denot_ty_lvar_gas 0 Σ τ e)) ->
  res_models m (denot_ty_lvar_gas 0
    (lty_env_msubst_store σ Σ)
    (context_ty_msubst_store σ τ)
    (lstore_instantiate_tm (lstore_lift_free σ) e)).
Proof.
  intros Hσrel Hσty Hm.
  cbn [denot_ty_lvar_gas] in Hm |- *.
  cbn [formula_msubst_store formula_mlsubst] in Hm.
  rewrite res_models_and_iff in Hm.
  destruct Hm as [Hguard _].
  rewrite res_models_and_iff.
  split.
  - apply denot_guard_msubst_store_models; assumption.
  - unfold res_models. cbn [formula_measure res_models_fuel].
    split; [apply formula_scoped_true_iff; trivial|trivial].
Qed.

Lemma denot_ty_lvar_gas_zero_msubst_store_models_relevant_back
    σ Σ τ e (m : WfWorldT) :
  denot_relevant_lvars τ e ⊆ dom Σ ->
  lvars_of_atoms (dom (σ : gmap atom value)) ⊆ denot_relevant_lvars τ e ->
  atom_store_has_ltype Σ σ ->
  res_models m (denot_ty_lvar_gas 0
    (lty_env_msubst_store σ Σ)
    (context_ty_msubst_store σ τ)
    (lstore_instantiate_tm (lstore_lift_free σ) e)) ->
  res_models m (formula_msubst_store σ (denot_ty_lvar_gas 0 Σ τ e)).
Proof.
  intros Hscope Hσrel Hσty Hm.
  cbn [denot_ty_lvar_gas] in Hm |- *.
  rewrite res_models_and_iff in Hm.
  destruct Hm as [Hguard _].
  cbn [formula_msubst_store formula_mlsubst].
  rewrite res_models_and_iff.
  split.
  - eapply denot_guard_msubst_store_models_back_relevant; eauto.
  - unfold res_models. cbn [formula_measure res_models_fuel].
    split; [apply formula_scoped_true_iff; trivial|trivial].
Qed.

Lemma denot_ty_lvar_gas_msubst_store_agree_relevant
    gas σ1 σ2 Σ τ e (m : WfWorldT) :
  storeA_restrict σ1 (lvars_fv (denot_relevant_lvars τ e)) =
  storeA_restrict σ2 (lvars_fv (denot_relevant_lvars τ e)) ->
  store_closed σ1 ->
  store_closed σ2 ->
  res_models m (denot_ty_lvar_gas gas
    (lty_env_msubst_store σ1 Σ)
    (context_ty_msubst_store σ1 τ)
    (lstore_instantiate_tm (lstore_lift_free σ1) e)) ->
  res_models m (denot_ty_lvar_gas gas
    (lty_env_msubst_store σ2 Σ)
    (context_ty_msubst_store σ2 τ)
    (lstore_instantiate_tm (lstore_lift_free σ2) e)).
Proof.
  intros Hagree Hclosed1 Hclosed2 Hmodels.
  set (R := denot_relevant_lvars τ e).
  assert (Hτ :
    context_ty_msubst_store σ1 τ =
    context_ty_msubst_store σ2 τ).
  {
    fold R in Hagree.
    rewrite (context_ty_msubst_store_restrict_subset σ1 τ (lvars_fv R)).
    2:{
      unfold R, denot_relevant_lvars.
      rewrite lvars_fv_union, context_ty_lvars_fv. set_solver.
    }
    rewrite (context_ty_msubst_store_restrict_subset σ2 τ (lvars_fv R)).
    2:{
      unfold R, denot_relevant_lvars.
      rewrite lvars_fv_union, context_ty_lvars_fv. set_solver.
    }
    change (store_restrict σ1 (lvars_fv R) =
      store_restrict σ2 (lvars_fv R)) in Hagree.
    rewrite Hagree. reflexivity.
  }
  assert (He :
    lstore_instantiate_tm (lstore_lift_free σ1) e =
    lstore_instantiate_tm (lstore_lift_free σ2) e).
  {
    apply lstore_instantiate_tm_lift_free_agree_subset
      with (X := lvars_fv R).
    - unfold R, denot_relevant_lvars.
      rewrite lvars_fv_union, tm_lvars_fv. set_solver.
    - exact Hagree.
  }
  rewrite <- Hτ.
  rewrite <- He.
  eapply res_models_denot_ty_lvar_gas_env_agree_on.
  - reflexivity.
  - apply lty_env_restrict_lvars_msubst_store_agree
      with (R := R).
    + unfold R.
      rewrite (denot_relevant_lvars_msubst_store σ1 τ e Hclosed1).
      set_solver.
    + exact Hagree.
  - exact Hmodels.
Qed.
End ContextTypeDenotationMsubst.
