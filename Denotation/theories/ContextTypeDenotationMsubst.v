(** * Denotation.ContextTypeDenotationMsubst

    Models-level transport for substituting a fixed atom store into context-type
    denotations.  This is the shared route used by fibered implication
    elimination in Soundness; case-specific msubst bridges should reduce to
    this theorem rather than re-proving formula-shape facts. *)

From Denotation Require Import Notation ContextTypeDenotationDefinition
  ContextTypeDenotationLvars.

Section ContextTypeDenotationMsubst.

Definition denot_msubst_relevant_store
    (σ : StoreT) (τ : context_ty) (e : tm) : StoreT :=
  store_restrict σ (lvars_fv (denot_relevant_lvars τ e)).

Definition denot_msubst_induction_hyp (gas : nat) : Prop :=
  forall σ0 Σ0 τ0 e0 (m0 : WfWorldT),
    denot_relevant_lvars τ0 e0 ⊆ dom Σ0 ->
    atom_store_has_ltype Σ0 σ0 ->
    m0 ⊨ formula_msubst_store σ0 (denot_ty_lvar_gas gas Σ0 τ0 e0) <->
    m0 ⊨ denot_ty_lvar_gas gas
      (lty_env_msubst_store σ0 Σ0)
      (context_ty_msubst_store σ0 τ0)
      (lstore_instantiate_tm (lstore_lift_free σ0) e0).

Lemma formula_open_denot_ty_lvar_gas_singleton
    k y gas Σ τ e :
  y ∉ lvars_fv (dom Σ) ->
  y ∉ fv_tm e ->
  y ∉ fv_cty τ ->
  formula_open k y (denot_ty_lvar_gas gas Σ τ e) =
  denot_ty_lvar_gas gas
    (lty_env_open_one k y Σ)
    (cty_open k y τ)
    (open_tm k (vfvar y) e).
Proof.
  intros HΣ He Hτ.
  assert (HΣfree : LVFree y ∉ dom Σ).
  {
    intros Hbad. apply HΣ.
    apply lvars_fv_elem. exact Hbad.
  }
  assert (Hfresh :
    open_env_fresh_for_lvars (<[k := y]> ∅)
      (dom Σ ∪ denot_relevant_lvars τ e)).
  {
    apply open_env_fresh_for_lvars_singleton.
    rewrite lvars_fv_union.
    unfold denot_relevant_lvars.
    rewrite lvars_fv_union, context_ty_lvars_fv, tm_lvars_fv.
    set_solver.
  }
  pose proof (formula_open_env_denot_ty_lvar_gas
    (<[k := y]> ∅) gas Σ τ e Hfresh
    (open_env_values_inj_singleton k y)) as Heq.
  rewrite formula_open_env_singleton in Heq.
  rewrite lty_env_open_lvars_singleton in Heq by exact HΣfree.
  rewrite open_cty_env_singleton in Heq.
  rewrite open_tm_env_singleton in Heq.
  exact Heq.
Qed.

Lemma atom_store_has_ltype_denot_relevant_env Σ σ τ e :
  lvars_of_atoms (dom (σ : gmap atom value)) ⊆ denot_relevant_lvars τ e ->
  atom_store_has_ltype Σ σ ->
  atom_store_has_ltype (denot_relevant_env Σ τ e) σ.
Proof.
  intros Hrel Hty.
  unfold denot_relevant_env, lty_env_restrict_lvars.
  apply atom_store_has_ltype_restrict_lvars; assumption.
Qed.

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
  intros Hwf He Hσty Hsingleton.
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
  assert (Hscope_fixed :
    dom (σ : StoreT) ∩ lvars_fv R ⊆ world_dom (m : WorldT)).
  {
    pose proof (f_equal world_dom Hsingleton) as Hdom.
    simpl in Hdom.
    rewrite storeA_restrict_dom in Hdom.
    set_solver.
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
  intros Hwf He Hσty Hsingleton.
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
    pose proof (basic_world_formula_fixed_from_singleton Σ σ R m
      Hσty Hsingleton) as Hfixed.
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

Lemma expr_basic_typing_formula_msubst_store_singleton_iff
    σ Σ τ e T (m : WfWorldT) :
  basic_context_ty_lvars (dom Σ) τ ->
  tm_lvars e ⊆ dom Σ ->
  atom_store_has_ltype Σ σ ->
  (res_restrict m (lvars_fv (denot_relevant_lvars τ e)) : WorldT) =
    singleton_world (store_restrict σ (lvars_fv (denot_relevant_lvars τ e))) ->
  m ⊨ formula_msubst_store σ
    (expr_basic_typing_formula (denot_relevant_env Σ τ e) e T) <->
  m ⊨ expr_basic_typing_formula
    (denot_relevant_env Σ τ
      (lstore_instantiate_tm (lstore_lift_free σ) e))
    (lstore_instantiate_tm (lstore_lift_free σ) e) T.
Admitted.

Lemma denot_guard_msubst_store_singleton_iff
    σ Σ τ e (m : WfWorldT) :
  basic_context_ty_lvars (dom Σ) τ ->
  tm_lvars e ⊆ dom Σ ->
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
  intros Hwf He Hσty Hsingleton.
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

Lemma denot_ty_lvar_gas_zero_msubst_store_singleton_iff
    σ Σ τ e (m : WfWorldT) :
  basic_context_ty_lvars (dom Σ) τ ->
  tm_lvars e ⊆ dom Σ ->
  atom_store_has_ltype Σ σ ->
  (res_restrict m (lvars_fv (denot_relevant_lvars τ e)) : WorldT) =
    singleton_world (store_restrict σ (lvars_fv (denot_relevant_lvars τ e))) ->
  res_models m (formula_msubst_store σ (denot_ty_lvar_gas 0 Σ τ e)) <->
  res_models m (denot_ty_lvar_gas 0 Σ τ
    (lstore_instantiate_tm (lstore_lift_free σ) e)).
Proof.
  intros Hwf He Hσty Hsingleton.
  cbn [denot_ty_lvar_gas].
  formula_msubst_syntax_norm.
  rewrite !res_models_and_iff.
  pose proof (denot_guard_msubst_store_singleton_iff σ Σ τ e m
    Hwf He Hσty Hsingleton) as Hguard.
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

Lemma formula_fv_over_msubst_store_body
    σ b φ e :
  store_closed σ ->
  formula_fv
    (formula_msubst_store σ
      (FImpl (basic_world_formula (<[LVBound 0 := TBase b]> ∅))
        (FImpl
          (expr_result_formula (tm_shift 0 e) (LVBound 0))
          (FFibVars (qual_vars φ ∖ {[LVBound 0]})
            (FOver (type_qualifier_formula φ)))))) =
  formula_fv
    (FImpl (basic_world_formula (<[LVBound 0 := TBase b]> ∅))
      (FImpl
        (expr_result_formula
          (tm_shift 0 (lstore_instantiate_tm (lstore_lift_free σ) e))
          (LVBound 0))
        (FFibVars
          (qual_vars (qual_msubst_store σ φ) ∖ {[LVBound 0]})
          (FOver (type_qualifier_formula (qual_msubst_store σ φ)))))).
Proof.
  intros Hclosed.
  formula_msubst_syntax_norm.
  formula_fv_syntax_norm.
  assert (Hbasic_src :
    lvars_fv
      (formula_lvars
        (formula_msubst_store σ
          (basic_world_formula (<[LVBound 0 := TBase b]> ∅)))) = ∅).
  {
    change (formula_fv
      (formula_msubst_store σ
        (basic_world_formula (<[LVBound 0 := TBase b]> ∅))) = ∅).
    apply set_eq. intros a. split; [|set_solver].
    intros Ha.
    pose proof (formula_msubst_store_fv_subset σ
      (basic_world_formula (<[LVBound 0 := TBase b]> ∅)) a Ha) as Hsub.
    rewrite formula_fv_basic_world_formula in Hsub.
    rewrite dom_insert_L, dom_empty_L in Hsub.
    rewrite lvars_fv_union, lvars_fv_singleton_bound, lvars_fv_empty in Hsub.
    set_solver.
  }
  rewrite Hbasic_src.
  rewrite formula_lvars_fv_basic_world_formula.
  rewrite dom_insert_L, dom_empty_L.
  rewrite lvars_fv_union, lvars_fv_singleton_bound, lvars_fv_empty.
  change (lvars_fv
    (formula_lvars
      (formula_msubst_store σ
        (expr_result_formula (tm_shift 0 e) (LVBound 0)))))
    with (lvars_fv
      ((tm_lvars (tm_shift 0 e) ∪ {[LVBound 0]})
        ∖ dom (lstore_lift_free σ : LStoreT))).
  change (lvars_fv
    (formula_lvars
      (formula_msubst_store σ (type_qualifier_formula φ))))
    with (lvars_fv
      (qual_vars φ ∖ dom (lstore_lift_free σ : LStoreT))).
  rewrite formula_lvars_fv_expr_result_formula.
  rewrite formula_lvars_fv_type_qualifier_formula.
  unfold qual_dom.
  rewrite qual_msubst_store_vars.
  rewrite dom_lstore_lift_free.
  rewrite !lvars_fv_difference_of_atoms.
  rewrite !lvars_fv_union, !lvars_fv_singleton_bound.
  rewrite ?tm_lvars_shift_fv.
  rewrite ?(tm_lvars_lstore_instantiate_lift_free_closed σ e Hclosed).
  change (qual_lvars (qual_msubst_store σ φ))
    with (qual_vars (qual_msubst_store σ φ)).
  rewrite qual_msubst_store_vars.
  rewrite dom_lstore_lift_free.
  rewrite !lvars_fv_difference_of_atoms.
  rewrite !lvars_fv_difference_singleton_bound.
  apply set_eq. intros a.
  rewrite !lvars_fv_difference_of_atoms.
  rewrite !elem_of_union, !elem_of_difference, !elem_of_empty.
  rewrite (elem_of_union (lvars_fv (tm_lvars e)) ∅ a).
  rewrite elem_of_empty.
  tauto.
Qed.

Lemma formula_fv_under_msubst_store_body
    σ b φ e :
  store_closed σ ->
  formula_fv
    (formula_msubst_store σ
      (FImpl (basic_world_formula (<[LVBound 0 := TBase b]> ∅))
        (FImpl
          (expr_result_formula (tm_shift 0 e) (LVBound 0))
          (FFibVars (qual_vars φ ∖ {[LVBound 0]})
            (FUnder (type_qualifier_formula φ)))))) =
  formula_fv
    (FImpl (basic_world_formula (<[LVBound 0 := TBase b]> ∅))
      (FImpl
        (expr_result_formula
          (tm_shift 0 (lstore_instantiate_tm (lstore_lift_free σ) e))
          (LVBound 0))
        (FFibVars
          (qual_vars (qual_msubst_store σ φ) ∖ {[LVBound 0]})
          (FUnder (type_qualifier_formula (qual_msubst_store σ φ)))))).
Proof.
  intros Hclosed.
  formula_msubst_syntax_norm.
  formula_fv_syntax_norm.
  assert (Hbasic_src :
    lvars_fv
      (formula_lvars
        (formula_msubst_store σ
          (basic_world_formula (<[LVBound 0 := TBase b]> ∅)))) = ∅).
  {
    change (formula_fv
      (formula_msubst_store σ
        (basic_world_formula (<[LVBound 0 := TBase b]> ∅))) = ∅).
    apply set_eq. intros a. split; [|set_solver].
    intros Ha.
    pose proof (formula_msubst_store_fv_subset σ
      (basic_world_formula (<[LVBound 0 := TBase b]> ∅)) a Ha) as Hsub.
    rewrite formula_fv_basic_world_formula in Hsub.
    rewrite dom_insert_L, dom_empty_L in Hsub.
    rewrite lvars_fv_union, lvars_fv_singleton_bound, lvars_fv_empty in Hsub.
    set_solver.
  }
  rewrite Hbasic_src.
  rewrite formula_lvars_fv_basic_world_formula.
  rewrite dom_insert_L, dom_empty_L.
  rewrite lvars_fv_union, lvars_fv_singleton_bound, lvars_fv_empty.
  change (lvars_fv
    (formula_lvars
      (formula_msubst_store σ
        (expr_result_formula (tm_shift 0 e) (LVBound 0)))))
    with (lvars_fv
      ((tm_lvars (tm_shift 0 e) ∪ {[LVBound 0]})
        ∖ dom (lstore_lift_free σ : LStoreT))).
  change (lvars_fv
    (formula_lvars
      (formula_msubst_store σ (type_qualifier_formula φ))))
    with (lvars_fv
      (qual_vars φ ∖ dom (lstore_lift_free σ : LStoreT))).
  rewrite formula_lvars_fv_expr_result_formula.
  rewrite formula_lvars_fv_type_qualifier_formula.
  unfold qual_dom.
  rewrite qual_msubst_store_vars.
  rewrite dom_lstore_lift_free.
  rewrite !lvars_fv_difference_of_atoms.
  rewrite !lvars_fv_union, !lvars_fv_singleton_bound.
  rewrite ?tm_lvars_shift_fv.
  rewrite ?(tm_lvars_lstore_instantiate_lift_free_closed σ e Hclosed).
  change (qual_lvars (qual_msubst_store σ φ))
    with (qual_vars (qual_msubst_store σ φ)).
  rewrite qual_msubst_store_vars.
  rewrite dom_lstore_lift_free.
  rewrite !lvars_fv_difference_of_atoms.
  rewrite !lvars_fv_difference_singleton_bound.
  apply set_eq. intros a.
  rewrite !lvars_fv_difference_of_atoms.
  rewrite !elem_of_union, !elem_of_difference, !elem_of_empty.
  rewrite (elem_of_union (lvars_fv (tm_lvars e)) ∅ a).
  rewrite elem_of_empty.
  tauto.
Qed.

Lemma qual_msubst_store_open_fibvars_domain σ φ k y :
  y ∉ dom (σ : gmap atom value) ->
  set_swap (LVBound k) (LVFree y) (qual_vars φ ∖ {[LVBound k]})
    ∖ dom (lstore_lift_free σ : LStoreT) =
  set_swap (LVBound k) (LVFree y)
    (qual_vars (qual_msubst_store σ φ) ∖ {[LVBound k]}).
Proof.
  intros Hy.
  rewrite qual_msubst_store_vars, dom_lstore_lift_free.
  set (R := lvars_of_atoms (dom (σ : gmap atom value))).
  assert (Hbound : LVBound k ∉ R).
  { subst R. unfold lvars_of_atoms. rewrite elem_of_map.
    intros (z & Hz & _). discriminate. }
  assert (Hfree : LVFree y ∉ R).
  { subst R. unfold lvars_of_atoms. rewrite elem_of_map.
    intros (z & Hz & Hzσ). inversion Hz. subst. exact (Hy Hzσ). }
  rewrite <- set_swap_difference_fresh by assumption.
  f_equal. set_solver.
Qed.

Lemma denot_ty_lvar_gas_msubst_store_over_body
    σ Σ b φ e (m : WfWorldT) :
  atom_store_has_ltype Σ σ ->
  res_models m
    (formula_msubst_store σ
      (FForall
        (FImpl (basic_world_formula (<[LVBound 0 := TBase b]> ∅))
          (FImpl
            (expr_result_formula (tm_shift 0 e) (LVBound 0))
            (FFibVars (qual_vars φ ∖ {[LVBound 0]})
              (FOver (type_qualifier_formula φ))))))) ->
  res_models m
    (FForall
      (FImpl (basic_world_formula (<[LVBound 0 := TBase b]> ∅))
        (FImpl
          (expr_result_formula
            (tm_shift 0 (lstore_instantiate_tm (lstore_lift_free σ) e))
            (LVBound 0))
          (FFibVars
            (qual_vars (qual_msubst_store σ φ) ∖ {[LVBound 0]})
            (FOver (type_qualifier_formula (qual_msubst_store σ φ))))))).
Proof.
  intros Hσty Hsrc.
  pose proof (atom_store_has_ltype_closed _ _ Hσty) as Hclosed.
  set (src :=
    FImpl (basic_world_formula (<[LVBound 0 := TBase b]> ∅))
      (FImpl
        (expr_result_formula (tm_shift 0 e) (LVBound 0))
        (FFibVars (qual_vars φ ∖ {[LVBound 0]})
          (FOver (type_qualifier_formula φ))))).
  set (dst :=
    FImpl (basic_world_formula (<[LVBound 0 := TBase b]> ∅))
      (FImpl
        (expr_result_formula
          (tm_shift 0 (lstore_instantiate_tm (lstore_lift_free σ) e))
          (LVBound 0))
        (FFibVars
          (qual_vars (qual_msubst_store σ φ) ∖ {[LVBound 0]})
          (FOver (type_qualifier_formula (qual_msubst_store σ φ)))))).
  assert (Hfv : formula_fv (formula_msubst_store σ src) = formula_fv dst).
  { subst src dst. apply formula_fv_over_msubst_store_body. exact Hclosed. }
  eapply (res_models_forall_map_same_fv m (formula_msubst_store σ src) dst).
  - exact Hfv.
  - pose proof (res_models_scoped _ _ Hsrc) as Hscope_src.
    change (formula_scoped_in_world m (FForall (formula_msubst_store σ src)))
      in Hscope_src.
    unfold formula_scoped_in_world in Hscope_src |- *.
    rewrite formula_fv_forall in Hscope_src |- *.
    rewrite <- Hfv. exact Hscope_src.
  - exists (dom (σ : gmap atom value) ∪ fv_tm e ∪ qual_dom φ).
    intros y Hy F my HFin HFout Hext Hopen.
    assert (Hyσ : y ∉ dom (σ : gmap atom value)) by set_solver.
    assert (Hyφ : y ∉ qual_dom φ) by set_solver.
    assert (Hyφσ : y ∉ qual_dom (qual_msubst_store σ φ)).
    { intros Hybad. apply Hyφ. eapply qual_dom_msubst_store_subset; exact Hybad. }
    assert (Htarget_open_scope :
      formula_scoped_in_world my (formula_open 0 y dst)).
    {
      eapply formula_scoped_open_of_extend.
      - rewrite <- Hfv. exact HFin.
      - exact HFout.
      - exact Hext.
    }
    subst src dst.
    rewrite formula_open_msubst_store_fresh in Hopen by exact Hyσ.
    formula_msubst_syntax_norm_in Hopen.
    formula_open_syntax_norm_in Hopen.
    formula_open_syntax_norm_in Htarget_open_scope.
    formula_open_syntax_norm.
    eapply res_models_impl2_map; [| | | | exact Hopen].
    + exact Htarget_open_scope.
    + intros Hworld.
      change (my ⊨ FAtom (lqual_msubst_store σ
        (lqual_open 0 y
          (basic_world_lqual (<[LVBound 0 := TBase b]> ∅))))).
      rewrite lqual_msubst_store_fresh by
        (unfold lqual_fv, lqual_open, basic_world_lqual;
         cbn [lqual_dom];
         eapply elem_of_disjoint; intros z Hzσ Hzopen;
         pose proof (lvars_fv_open_subset 0 y
           (dom (<[LVBound 0 := TBase b]> ∅ : lty_env)) z Hzopen)
           as Hzopen';
         rewrite dom_insert_L, dom_empty_L, lvars_fv_union,
           lvars_fv_singleton_bound, lvars_fv_empty in Hzopen';
         set_solver).
      exact Hworld.
    + intros Hresult.
      eapply expr_result_formula_msubst_store_open_shift_models_back;
        [exact Hclosed|set_solver|exact Hresult].
    + intros Hfib.
      rewrite formula_open_over in Hfib.
      rewrite type_qualifier_formula_open in Hfib by exact Hyφ.
      formula_msubst_syntax_norm_in Hfib.
      change (my ⊨ FFibVars
        (set_swap (LVBound 0) (LVFree y) (qual_vars φ ∖ {[LVBound 0]})
          ∖ dom (lstore_lift_free σ : LStoreT))
        (FOver (formula_msubst_store σ
          (type_qualifier_formula (φ ^q^ y))))) in Hfib.
      rewrite (qual_msubst_store_open_fibvars_domain σ φ 0 y Hyσ) in Hfib.
      eapply (res_models_FFibVars_map my
        (set_swap (LVBound 0) (LVFree y)
          (qual_vars (qual_msubst_store σ φ) ∖ {[LVBound 0]}))
        (FOver (formula_msubst_store σ
          (type_qualifier_formula (φ ^q^ y))))
        (formula_open 0 y
          (FOver (type_qualifier_formula (qual_msubst_store σ φ))))).
      * eapply formula_scoped_impl_r.
        eapply formula_scoped_impl_r.
        exact Htarget_open_scope.
      * intros σfib mfib Hproj Hover.
        formula_msubst_syntax_norm_in Hover.
        eapply res_models_over_map.
        -- pose proof (res_fiber_from_projection_world_dom my mfib
             (lvars_fv
               (set_swap (LVBound 0) (LVFree y)
                 (qual_vars (qual_msubst_store σ φ) ∖ {[LVBound 0]})))
             σfib Hproj) as Hdomfib.
           pose proof (formula_scoped_impl_r my _ _ Htarget_open_scope)
             as Hscope_impl1.
           pose proof (formula_scoped_impl_r my _ _ Hscope_impl1)
             as Hscope_fib.
           pose proof (formula_scoped_fibvars_r my _ _ Hscope_fib)
             as Hscope_over_my.
           eapply formula_scoped_in_world_from_formula_fv.
           unfold formula_scoped_in_world in Hscope_over_my.
           rewrite Hdomfib.
           intros a Ha.
           apply Hscope_over_my.
           eapply formula_msubst_store_fv_subset; exact Ha.
        -- intros n _ Hqual.
           rewrite type_qualifier_formula_open by exact Hyφσ.
           rewrite qual_open_msubst_store_fresh by exact Hyσ.
           eapply type_qualifier_formula_msubst_store_assoc_models.
           exact Hqual.
        -- exact Hover.
      * exact Hfib.
  - change (m ⊨ FForall (formula_msubst_store σ src)) in Hsrc.
    exact Hsrc.
Qed.

Lemma denot_ty_lvar_gas_msubst_store_under_body
    σ Σ b φ e (m : WfWorldT) :
  atom_store_has_ltype Σ σ ->
  res_models m
    (formula_msubst_store σ
      (FForall
        (FImpl (basic_world_formula (<[LVBound 0 := TBase b]> ∅))
          (FImpl
            (expr_result_formula (tm_shift 0 e) (LVBound 0))
            (FFibVars (qual_vars φ ∖ {[LVBound 0]})
              (FUnder (type_qualifier_formula φ))))))) ->
  res_models m
    (FForall
      (FImpl (basic_world_formula (<[LVBound 0 := TBase b]> ∅))
        (FImpl
          (expr_result_formula
            (tm_shift 0 (lstore_instantiate_tm (lstore_lift_free σ) e))
            (LVBound 0))
          (FFibVars
            (qual_vars (qual_msubst_store σ φ) ∖ {[LVBound 0]})
            (FUnder (type_qualifier_formula (qual_msubst_store σ φ))))))).
Proof.
  intros Hσty Hsrc.
  pose proof (atom_store_has_ltype_closed _ _ Hσty) as Hclosed.
  set (src :=
    FImpl (basic_world_formula (<[LVBound 0 := TBase b]> ∅))
      (FImpl
        (expr_result_formula (tm_shift 0 e) (LVBound 0))
        (FFibVars (qual_vars φ ∖ {[LVBound 0]})
          (FUnder (type_qualifier_formula φ))))).
  set (dst :=
    FImpl (basic_world_formula (<[LVBound 0 := TBase b]> ∅))
      (FImpl
        (expr_result_formula
          (tm_shift 0 (lstore_instantiate_tm (lstore_lift_free σ) e))
          (LVBound 0))
        (FFibVars
          (qual_vars (qual_msubst_store σ φ) ∖ {[LVBound 0]})
          (FUnder (type_qualifier_formula (qual_msubst_store σ φ)))))).
  assert (Hfv : formula_fv (formula_msubst_store σ src) = formula_fv dst).
  { subst src dst. apply formula_fv_under_msubst_store_body. exact Hclosed. }
  eapply (res_models_forall_map_same_fv m (formula_msubst_store σ src) dst).
  - exact Hfv.
  - pose proof (res_models_scoped _ _ Hsrc) as Hscope_src.
    change (formula_scoped_in_world m (FForall (formula_msubst_store σ src)))
      in Hscope_src.
    unfold formula_scoped_in_world in Hscope_src |- *.
    rewrite formula_fv_forall in Hscope_src |- *.
    rewrite <- Hfv. exact Hscope_src.
  - exists (dom (σ : gmap atom value) ∪ fv_tm e ∪ qual_dom φ).
    intros y Hy F my HFin HFout Hext Hopen.
    assert (Hyσ : y ∉ dom (σ : gmap atom value)) by set_solver.
    assert (Hyφ : y ∉ qual_dom φ) by set_solver.
    assert (Hyφσ : y ∉ qual_dom (qual_msubst_store σ φ)).
    { intros Hybad. apply Hyφ. eapply qual_dom_msubst_store_subset; exact Hybad. }
    assert (Htarget_open_scope :
      formula_scoped_in_world my (formula_open 0 y dst)).
    {
      eapply formula_scoped_open_of_extend.
      - rewrite <- Hfv. exact HFin.
      - exact HFout.
      - exact Hext.
    }
    subst src dst.
    rewrite formula_open_msubst_store_fresh in Hopen by exact Hyσ.
    formula_msubst_syntax_norm_in Hopen.
    formula_open_syntax_norm_in Hopen.
    formula_open_syntax_norm_in Htarget_open_scope.
    formula_open_syntax_norm.
    eapply res_models_impl2_map; [| | | | exact Hopen].
    + exact Htarget_open_scope.
    + intros Hworld.
      change (my ⊨ FAtom (lqual_msubst_store σ
        (lqual_open 0 y
          (basic_world_lqual (<[LVBound 0 := TBase b]> ∅))))).
      rewrite lqual_msubst_store_fresh by
        (unfold lqual_fv, lqual_open, basic_world_lqual;
         cbn [lqual_dom];
         eapply elem_of_disjoint; intros z Hzσ Hzopen;
         pose proof (lvars_fv_open_subset 0 y
           (dom (<[LVBound 0 := TBase b]> ∅ : lty_env)) z Hzopen)
           as Hzopen';
         rewrite dom_insert_L, dom_empty_L, lvars_fv_union,
           lvars_fv_singleton_bound, lvars_fv_empty in Hzopen';
         set_solver).
      exact Hworld.
    + intros Hresult.
      eapply expr_result_formula_msubst_store_open_shift_models_back;
        [exact Hclosed|set_solver|exact Hresult].
    + intros Hfib.
      rewrite formula_open_under in Hfib.
      rewrite type_qualifier_formula_open in Hfib by exact Hyφ.
      formula_msubst_syntax_norm_in Hfib.
      change (my ⊨ FFibVars
        (set_swap (LVBound 0) (LVFree y) (qual_vars φ ∖ {[LVBound 0]})
          ∖ dom (lstore_lift_free σ : LStoreT))
        (FUnder (formula_msubst_store σ
          (type_qualifier_formula (φ ^q^ y))))) in Hfib.
      rewrite (qual_msubst_store_open_fibvars_domain σ φ 0 y Hyσ) in Hfib.
      eapply (res_models_FFibVars_map my
        (set_swap (LVBound 0) (LVFree y)
          (qual_vars (qual_msubst_store σ φ) ∖ {[LVBound 0]}))
        (FUnder (formula_msubst_store σ
          (type_qualifier_formula (φ ^q^ y))))
        (formula_open 0 y
          (FUnder (type_qualifier_formula (qual_msubst_store σ φ))))).
      * eapply formula_scoped_impl_r.
        eapply formula_scoped_impl_r.
        exact Htarget_open_scope.
      * intros σfib mfib Hproj Hunder.
        formula_msubst_syntax_norm_in Hunder.
        eapply res_models_under_map.
        -- pose proof (res_fiber_from_projection_world_dom my mfib
             (lvars_fv
               (set_swap (LVBound 0) (LVFree y)
                 (qual_vars (qual_msubst_store σ φ) ∖ {[LVBound 0]})))
             σfib Hproj) as Hdomfib.
           pose proof (formula_scoped_impl_r my _ _ Htarget_open_scope)
             as Hscope_impl1.
           pose proof (formula_scoped_impl_r my _ _ Hscope_impl1)
             as Hscope_fib.
           pose proof (formula_scoped_fibvars_r my _ _ Hscope_fib)
             as Hscope_under_my.
           eapply formula_scoped_in_world_from_formula_fv.
           unfold formula_scoped_in_world in Hscope_under_my.
           rewrite Hdomfib.
           intros a Ha.
           apply Hscope_under_my.
           eapply formula_msubst_store_fv_subset; exact Ha.
        -- intros n _ Hqual.
           rewrite type_qualifier_formula_open by exact Hyφσ.
           rewrite qual_open_msubst_store_fresh by exact Hyσ.
           eapply type_qualifier_formula_msubst_store_assoc_models.
           exact Hqual.
        -- exact Hunder.
      * exact Hfib.
  - change (m ⊨ FForall (formula_msubst_store σ src)) in Hsrc.
    exact Hsrc.
Qed.

Lemma denot_ty_lvar_gas_msubst_store_arrow_body
    gas σ Σ τx τr e (m : WfWorldT) :
  denot_msubst_induction_hyp gas ->
  denot_relevant_lvars (CTArrow τx τr) e ⊆ dom Σ ->
  lvars_of_atoms (dom (σ : gmap atom value)) ⊆
    denot_relevant_lvars (CTArrow τx τr) e ->
  atom_store_has_ltype Σ σ ->
  let Σg := denot_relevant_env Σ (CTArrow τx τr) e in
  let Σx := typed_lty_env_bind Σg (erase_ty τx) in
  res_models m
    (formula_msubst_store σ
      (FForall
        (FImpl (basic_world_formula (<[LVBound 0 := erase_ty τx]> ∅))
          (FImpl
            (denot_ty_lvar_gas gas Σx
              (cty_shift 0 τx) (tret (vbvar 0)))
            (denot_ty_lvar_gas gas Σx τr
              (tapp_tm (tm_shift 0 e) (vbvar 0))))))) ->
  let e' := lstore_instantiate_tm (lstore_lift_free σ) e in
  let τx' := context_ty_msubst_store σ τx in
  let τr' := context_ty_msubst_store σ τr in
  let Σg' := denot_relevant_env (lty_env_msubst_store σ Σ)
    (CTArrow τx' τr') e' in
  let Σx' := typed_lty_env_bind Σg' (erase_ty τx') in
  res_models m
    (FForall
      (FImpl (basic_world_formula (<[LVBound 0 := erase_ty τx']> ∅))
        (FImpl
          (denot_ty_lvar_gas gas Σx'
            (cty_shift 0 τx') (tret (vbvar 0)))
          (denot_ty_lvar_gas gas Σx' τr'
            (tapp_tm (tm_shift 0 e') (vbvar 0)))))).
Admitted.

Lemma denot_ty_lvar_gas_msubst_store_wand_body
    gas σ Σ τx τr e (m : WfWorldT) :
  denot_msubst_induction_hyp gas ->
  denot_relevant_lvars (CTWand τx τr) e ⊆ dom Σ ->
  lvars_of_atoms (dom (σ : gmap atom value)) ⊆
    denot_relevant_lvars (CTWand τx τr) e ->
  atom_store_has_ltype Σ σ ->
  let Σg := denot_relevant_env Σ (CTWand τx τr) e in
  let Σx := typed_lty_env_bind Σg (erase_ty τx) in
  res_models m
    (formula_msubst_store σ
      (FForall
        (FImpl (basic_world_formula (<[LVBound 0 := erase_ty τx]> ∅))
          (FWand
            (denot_ty_lvar_gas gas Σx
              (cty_shift 0 τx) (tret (vbvar 0)))
            (denot_ty_lvar_gas gas Σx τr
              (tapp_tm (tm_shift 0 e) (vbvar 0))))))) ->
  let e' := lstore_instantiate_tm (lstore_lift_free σ) e in
  let τx' := context_ty_msubst_store σ τx in
  let τr' := context_ty_msubst_store σ τr in
  let Σg' := denot_relevant_env (lty_env_msubst_store σ Σ)
    (CTWand τx' τr') e' in
  let Σx' := typed_lty_env_bind Σg' (erase_ty τx') in
  res_models m
    (FForall
      (FImpl (basic_world_formula (<[LVBound 0 := erase_ty τx']> ∅))
        (FWand
          (denot_ty_lvar_gas gas Σx'
            (cty_shift 0 τx') (tret (vbvar 0)))
          (denot_ty_lvar_gas gas Σx' τr'
            (tapp_tm (tm_shift 0 e') (vbvar 0)))))).
Admitted.

Lemma denot_ty_lvar_gas_msubst_store_models_relevant_back_restricted
    gas σ Σ τ e (m : WfWorldT) :
  subseteq (denot_relevant_lvars τ e) (dom Σ) ->
  lvars_of_atoms (dom (σ : gmap atom value)) ⊆ denot_relevant_lvars τ e ->
  atom_store_has_ltype Σ σ ->
  res_models m (denot_ty_lvar_gas gas
    (lty_env_msubst_store σ Σ)
    (context_ty_msubst_store σ τ)
    (lstore_instantiate_tm (lstore_lift_free σ) e)) ->
  res_models m (formula_msubst_store σ (denot_ty_lvar_gas gas Σ τ e)).
Admitted.

Lemma denot_ty_lvar_gas_msubst_store_models_relevant_back
    gas σ Σ τ e (m : WfWorldT) :
  subseteq (denot_relevant_lvars τ e) (dom Σ) ->
  atom_store_has_ltype Σ σ ->
  res_models m (denot_ty_lvar_gas gas
    (lty_env_msubst_store σ Σ)
    (context_ty_msubst_store σ τ)
    (lstore_instantiate_tm (lstore_lift_free σ) e)) ->
  res_models m (formula_msubst_store σ (denot_ty_lvar_gas gas Σ τ e)).
Proof.
  intros Hscope Hty Hmodels.
  pose proof (atom_store_has_ltype_closed _ _ Hty) as Hclosed.
  set (σr := denot_msubst_relevant_store σ τ e).
  rewrite (formula_msubst_store_restrict_fv_subset σ
    (denot_ty_lvar_gas gas Σ τ e)
    (lvars_fv (denot_relevant_lvars τ e))).
  2:{
    transitivity (fv_tm e ∪ fv_cty τ).
    - apply formula_fv_denot_ty_lvar_gas_subset_relevant_pre_open.
    - unfold denot_relevant_lvars.
      rewrite lvars_fv_union, tm_lvars_fv, context_ty_lvars_fv.
      set_solver.
  }
  change (store_restrict σ (lvars_fv (denot_relevant_lvars τ e))) with σr.
  eapply denot_ty_lvar_gas_msubst_store_models_relevant_back_restricted.
  - exact Hscope.
  - unfold σr, denot_msubst_relevant_store.
    intros v Hv.
    unfold lvars_of_atoms in Hv.
    apply elem_of_map in Hv as [x [-> Hx]].
    apply storeA_restrict_dom_subset in Hx.
    rewrite lvars_fv_elem in Hx. exact Hx.
  - unfold σr, denot_msubst_relevant_store.
    intros x v Hxv.
    apply storeA_restrict_lookup_some in Hxv as [_ Hxv].
    exact (Hty x v Hxv).
  - eapply denot_ty_lvar_gas_msubst_store_agree_relevant
      with (σ1 := σ).
    + unfold σr, denot_msubst_relevant_store.
      rewrite storeA_restrict_twice_same. reflexivity.
    + exact Hclosed.
    + unfold σr, denot_msubst_relevant_store.
      apply store_closed_restrict. exact Hclosed.
    + exact Hmodels.
Qed.

Lemma denot_ty_lvar_gas_msubst_store_models_relevant
    gas σ Σ τ e (m : WfWorldT) :
  subseteq (denot_relevant_lvars τ e) (dom Σ) ->
  lvars_of_atoms (dom (σ : gmap atom value)) ⊆ denot_relevant_lvars τ e ->
  atom_store_has_ltype Σ σ ->
  res_models m (formula_msubst_store σ (denot_ty_lvar_gas gas Σ τ e)) ->
  res_models m (denot_ty_lvar_gas gas
    (lty_env_msubst_store σ Σ)
    (context_ty_msubst_store σ τ)
    (lstore_instantiate_tm (lstore_lift_free σ) e)).
Proof.
  induction gas as [|gas IH] in σ, Σ, τ, e, m |- *.
  - intros _ Hσrel Hσty Hm.
    eapply denot_ty_lvar_gas_zero_msubst_store_models_relevant; eauto.
  - intros Hscope Hσrel Hσty Hm.
    assert (IHfull : denot_msubst_induction_hyp gas).
    {
      intros σ0 Σ0 τ0 e0 m0 Hscope0 Hty0.
      split.
      - intros Hmodels0.
        set (σr := denot_msubst_relevant_store σ0 τ0 e0).
        eapply denot_ty_lvar_gas_msubst_store_agree_relevant
          with (σ1 := σr).
        + unfold σr, denot_msubst_relevant_store.
          rewrite storeA_restrict_twice_same. reflexivity.
        + unfold σr, denot_msubst_relevant_store.
          apply store_closed_restrict.
          eapply atom_store_has_ltype_closed; exact Hty0.
        + eapply atom_store_has_ltype_closed; exact Hty0.
        + eapply IH.
          * exact Hscope0.
          * unfold σr, denot_msubst_relevant_store.
            intros v Hv.
            unfold lvars_of_atoms in Hv.
            apply elem_of_map in Hv as [x [-> Hx]].
            apply storeA_restrict_dom_subset in Hx.
            rewrite lvars_fv_elem in Hx. exact Hx.
          * unfold σr, denot_msubst_relevant_store.
            intros x v Hxv.
            apply storeA_restrict_lookup_some in Hxv as [_ Hxv].
            exact (Hty0 x v Hxv).
          * unfold σr, denot_msubst_relevant_store.
            rewrite <- (formula_msubst_store_restrict_fv_subset σ0
              (denot_ty_lvar_gas gas Σ0 τ0 e0)
              (lvars_fv (denot_relevant_lvars τ0 e0))).
            -- exact Hmodels0.
            -- transitivity (fv_tm e0 ∪ fv_cty τ0).
               ++ apply formula_fv_denot_ty_lvar_gas_subset_relevant_pre_open.
               ++ unfold denot_relevant_lvars.
                  rewrite lvars_fv_union, tm_lvars_fv, context_ty_lvars_fv.
                  set_solver.
      - intros Hmodels0.
        eapply denot_ty_lvar_gas_msubst_store_models_relevant_back; eauto.
    }
    destruct τ as [b φ|b φ|τ1 τ2|τ1 τ2|τ1 τ2|τx τr|τx τr];
      cbn [denot_ty_lvar_gas] in Hm |- *;
      cbn [formula_msubst_store formula_mlsubst] in Hm;
      rewrite res_models_and_iff in Hm;
      destruct Hm as [Hguard Hbody].
    + rewrite res_models_and_iff. split.
      * eapply denot_guard_msubst_store_models;
          [exact Hσrel|exact Hσty|exact Hguard].
      * apply denot_ty_lvar_gas_msubst_store_over_body with (Σ := Σ);
          assumption.
    + rewrite res_models_and_iff. split.
      * eapply denot_guard_msubst_store_models;
          [exact Hσrel|exact Hσty|exact Hguard].
      * apply denot_ty_lvar_gas_msubst_store_under_body with (Σ := Σ);
          assumption.
    + rewrite res_models_and_iff. split.
      * eapply denot_guard_msubst_store_models;
          [exact Hσrel|exact Hσty|exact Hguard].
      * cbn [context_ty_msubst_store].
        rewrite res_models_and_iff in Hbody.
        destruct Hbody as [Hτ1 Hτ2].
        cbn [denot_ty_lvar_gas].
        rewrite res_models_and_iff. split.
        -- set (σ1 := denot_msubst_relevant_store σ τ1 e).
           eapply denot_ty_lvar_gas_msubst_store_agree_relevant
             with (σ1 := σ1).
           ++ unfold σ1, denot_msubst_relevant_store.
              rewrite storeA_restrict_twice_same. reflexivity.
           ++ unfold σ1, denot_msubst_relevant_store.
              apply store_closed_restrict.
              eapply atom_store_has_ltype_closed; exact Hσty.
           ++ eapply atom_store_has_ltype_closed; exact Hσty.
           ++ eapply IH.
              ** intros v Hv. apply Hscope.
                 unfold denot_relevant_lvars, context_ty_lvars in *.
                 cbn [context_ty_lvars_at] in *.
                 apply elem_of_union in Hv as [Hv|Hv].
                 --- apply elem_of_union_l. apply elem_of_union_l. exact Hv.
                 --- apply elem_of_union_r. exact Hv.
              ** unfold σ1, denot_msubst_relevant_store.
                 intros v Hv.
                 unfold lvars_of_atoms in Hv.
                 apply elem_of_map in Hv as [x [-> Hx]].
                 apply storeA_restrict_dom_subset in Hx.
                 rewrite lvars_fv_elem in Hx. exact Hx.
              ** unfold σ1, denot_msubst_relevant_store.
                 intros x v Hxv.
                 apply storeA_restrict_lookup_some in Hxv as [_ Hxv].
                 exact (Hσty x v Hxv).
              ** unfold σ1, denot_msubst_relevant_store.
                 rewrite <- (formula_msubst_store_restrict_fv_subset σ
                   (denot_ty_lvar_gas gas Σ τ1 e)
                   (lvars_fv (denot_relevant_lvars τ1 e))).
                 --- change (m ⊨ formula_msubst_store σ
                       (denot_ty_lvar_gas gas Σ τ1 e)).
                     exact Hτ1.
                 --- transitivity (fv_tm e ∪ fv_cty τ1).
                     +++ apply formula_fv_denot_ty_lvar_gas_subset_relevant_pre_open.
                     +++ unfold denot_relevant_lvars.
                         rewrite lvars_fv_union, tm_lvars_fv, context_ty_lvars_fv.
                         set_solver.
        -- set (σ2 := denot_msubst_relevant_store σ τ2 e).
           eapply denot_ty_lvar_gas_msubst_store_agree_relevant
             with (σ1 := σ2).
           ++ unfold σ2, denot_msubst_relevant_store.
              rewrite storeA_restrict_twice_same. reflexivity.
           ++ unfold σ2, denot_msubst_relevant_store.
              apply store_closed_restrict.
              eapply atom_store_has_ltype_closed; exact Hσty.
           ++ eapply atom_store_has_ltype_closed; exact Hσty.
           ++ eapply IH.
              ** intros v Hv. apply Hscope.
                 unfold denot_relevant_lvars, context_ty_lvars in *.
                 cbn [context_ty_lvars_at] in *.
                 apply elem_of_union in Hv as [Hv|Hv].
                 --- apply elem_of_union_l. apply elem_of_union_r. exact Hv.
                 --- apply elem_of_union_r. exact Hv.
              ** unfold σ2, denot_msubst_relevant_store.
                 intros v Hv.
                 unfold lvars_of_atoms in Hv.
                 apply elem_of_map in Hv as [x [-> Hx]].
                 apply storeA_restrict_dom_subset in Hx.
                 rewrite lvars_fv_elem in Hx. exact Hx.
              ** unfold σ2, denot_msubst_relevant_store.
                 intros x v Hxv.
                 apply storeA_restrict_lookup_some in Hxv as [_ Hxv].
                 exact (Hσty x v Hxv).
              ** unfold σ2, denot_msubst_relevant_store.
                 rewrite <- (formula_msubst_store_restrict_fv_subset σ
                   (denot_ty_lvar_gas gas Σ τ2 e)
                   (lvars_fv (denot_relevant_lvars τ2 e))).
                 --- change (m ⊨ formula_msubst_store σ
                       (denot_ty_lvar_gas gas Σ τ2 e)).
                     exact Hτ2.
                 --- transitivity (fv_tm e ∪ fv_cty τ2).
                     +++ apply formula_fv_denot_ty_lvar_gas_subset_relevant_pre_open.
                     +++ unfold denot_relevant_lvars.
                         rewrite lvars_fv_union, tm_lvars_fv, context_ty_lvars_fv.
                         set_solver.
    + rewrite res_models_and_iff. split.
      * eapply denot_guard_msubst_store_models;
          [exact Hσrel|exact Hσty|exact Hguard].
      * pose proof (denot_guard_msubst_store_models σ Σ (CTUnion τ1 τ2) e m
          Hσrel Hσty Hguard) as Hguard'.
        cbn [context_ty_msubst_store denot_ty_lvar_gas].
        eapply res_models_or_transport_between_worlds.
        -- eapply formula_fv_denot_ty_lvar_gas_scope_from_guard_pre_open
             with (τbig := context_ty_msubst_store σ (CTUnion τ1 τ2)).
           ++ cbn [context_ty_msubst_store context_ty_lvars context_ty_lvars_at].
              set_solver.
           ++ exact Hguard'.
        -- eapply formula_fv_denot_ty_lvar_gas_scope_from_guard_pre_open
             with (τbig := context_ty_msubst_store σ (CTUnion τ1 τ2)).
           ++ cbn [context_ty_msubst_store context_ty_lvars context_ty_lvars_at].
              set_solver.
           ++ exact Hguard'.
        -- intros Hτ1.
           eapply IHfull.
           ++ intros v Hv. apply Hscope.
              unfold denot_relevant_lvars, context_ty_lvars in *.
              cbn [context_ty_lvars_at] in *.
              apply elem_of_union in Hv as [Hv|Hv].
              ** apply elem_of_union_l. apply elem_of_union_l. exact Hv.
              ** apply elem_of_union_r. exact Hv.
           ++ exact Hσty.
           ++ change (m ⊨ formula_msubst_store σ
                (denot_ty_lvar_gas gas Σ τ1 e)).
              exact Hτ1.
        -- intros Hτ2.
           eapply IHfull.
           ++ intros v Hv. apply Hscope.
              unfold denot_relevant_lvars, context_ty_lvars in *.
              cbn [context_ty_lvars_at] in *.
              apply elem_of_union in Hv as [Hv|Hv].
              ** apply elem_of_union_l. apply elem_of_union_r. exact Hv.
              ** apply elem_of_union_r. exact Hv.
           ++ exact Hσty.
           ++ change (m ⊨ formula_msubst_store σ
                (denot_ty_lvar_gas gas Σ τ2 e)).
              exact Hτ2.
        -- exact Hbody.
    + rewrite res_models_and_iff. split.
      * eapply denot_guard_msubst_store_models;
          [exact Hσrel|exact Hσty|exact Hguard].
      * cbn [context_ty_msubst_store denot_ty_lvar_gas].
        eapply res_models_plus_map; [| | exact Hbody].
        -- intros m' Hτ1.
           eapply IHfull.
           ++ intros v Hv. apply Hscope.
              unfold denot_relevant_lvars, context_ty_lvars in *.
              cbn [context_ty_lvars_at] in *.
              apply elem_of_union in Hv as [Hv|Hv].
              ** apply elem_of_union_l. apply elem_of_union_l. exact Hv.
              ** apply elem_of_union_r. exact Hv.
           ++ exact Hσty.
           ++ change (m' ⊨ formula_msubst_store σ
                (denot_ty_lvar_gas gas Σ τ1 e)).
              exact Hτ1.
        -- intros m' Hτ2.
           eapply IHfull.
           ++ intros v Hv. apply Hscope.
              unfold denot_relevant_lvars, context_ty_lvars in *.
              cbn [context_ty_lvars_at] in *.
              apply elem_of_union in Hv as [Hv|Hv].
              ** apply elem_of_union_l. apply elem_of_union_r. exact Hv.
              ** apply elem_of_union_r. exact Hv.
           ++ exact Hσty.
           ++ change (m' ⊨ formula_msubst_store σ
                (denot_ty_lvar_gas gas Σ τ2 e)).
              exact Hτ2.
    + rewrite res_models_and_iff. split.
      * eapply denot_guard_msubst_store_models;
          [exact Hσrel|exact Hσty|exact Hguard].
      * cbn [context_ty_msubst_store denot_ty_lvar_gas].
        eapply denot_ty_lvar_gas_msubst_store_arrow_body;
          [exact IHfull|exact Hscope|exact Hσrel|exact Hσty|].
        exact Hbody.
    + rewrite res_models_and_iff. split.
      * eapply denot_guard_msubst_store_models;
          [exact Hσrel|exact Hσty|exact Hguard].
      * cbn [context_ty_msubst_store denot_ty_lvar_gas].
        eapply denot_ty_lvar_gas_msubst_store_wand_body;
          [exact IHfull|exact Hscope|exact Hσrel|exact Hσty|].
        exact Hbody.
Qed.

Lemma denot_ty_lvar_gas_msubst_store_models_relevant_iff
    gas σ Σ τ e (m : WfWorldT) :
  subseteq (denot_relevant_lvars τ e) (dom Σ) ->
  lvars_of_atoms (dom (σ : gmap atom value)) ⊆ denot_relevant_lvars τ e ->
  atom_store_has_ltype Σ σ ->
  res_models m (formula_msubst_store σ (denot_ty_lvar_gas gas Σ τ e)) <->
  res_models m (denot_ty_lvar_gas gas
    (lty_env_msubst_store σ Σ)
    (context_ty_msubst_store σ τ)
    (lstore_instantiate_tm (lstore_lift_free σ) e)).
Proof.
  intros Hscope Hσrel Hσty. split.
  - eapply denot_ty_lvar_gas_msubst_store_models_relevant; eauto.
  - eapply denot_ty_lvar_gas_msubst_store_models_relevant_back; eauto.
Qed.

Lemma denot_ty_lvar_gas_msubst_store_models
    gas σ Σ τ e (m : WfWorldT) :
  subseteq (denot_relevant_lvars τ e) (dom Σ) ->
  atom_store_has_ltype Σ σ ->
  res_models m (formula_msubst_store σ (denot_ty_lvar_gas gas Σ τ e)) ->
  res_models m (denot_ty_lvar_gas gas
    (lty_env_msubst_store (denot_msubst_relevant_store σ τ e) Σ)
    (context_ty_msubst_store (denot_msubst_relevant_store σ τ e) τ)
    (lstore_instantiate_tm
      (lstore_lift_free (denot_msubst_relevant_store σ τ e)) e)).
Proof.
  intros Hscope Hty Hmodels.
  eapply denot_ty_lvar_gas_msubst_store_models_relevant.
  - exact Hscope.
  - unfold denot_msubst_relevant_store.
    intros v Hv.
    unfold lvars_of_atoms in Hv.
    apply elem_of_map in Hv as [x [-> Hx]].
    apply storeA_restrict_dom_subset in Hx.
    rewrite lvars_fv_elem in Hx. exact Hx.
  - unfold denot_msubst_relevant_store.
    intros x v Hxv.
    apply storeA_restrict_lookup_some in Hxv as [_ Hxv].
    exact (Hty x v Hxv).
  - unfold denot_msubst_relevant_store.
    rewrite <- (formula_msubst_store_restrict_fv_subset σ
      (denot_ty_lvar_gas gas Σ τ e)
      (lvars_fv (denot_relevant_lvars τ e))).
    + exact Hmodels.
    + transitivity (fv_tm e ∪ fv_cty τ).
      * apply formula_fv_denot_ty_lvar_gas_subset_relevant_pre_open.
      * unfold denot_relevant_lvars.
        rewrite lvars_fv_union, tm_lvars_fv, context_ty_lvars_fv.
        set_solver.
Qed.

End ContextTypeDenotationMsubst.
