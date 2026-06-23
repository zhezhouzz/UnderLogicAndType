(** * ContextTyping.SoundnessPersist

    Fundamental-case support for value-only introduction of [CTPersist]. *)

From CoreLang Require Import BasicTypingProps InstantiationProps.
From ContextStore Require Import Store.
From ContextAlgebra Require Import ResourceInterface.
From ContextBasicDenotation Require Import RelevantEnv BasicTypingFormula TermExtension.
From Denotation Require Import Context DenotationSetMapFacts TypeEquiv
  TypeEquivCore TypeEquivFiberBaseResult TypeEquivFiberTransport TypePersist.
From ContextTyping Require Import Typing.

Local Notation StoreT := (gmap atom value) (only parsing).
Local Notation WorldT := (World (V := value)) (only parsing).
Local Notation WfWorldT := (WfWorld (V := value)) (only parsing).
Local Notation LStoreT := (LStore (V := value)) (only parsing).

Lemma ctx_denote_under_fv_contains_erase_dom Σ Γ :
  dom (erase_ctx Γ) ⊆ formula_fv (ctx_denote_under Σ Γ).
Proof.
  intros x Hx.
  destruct Γ; cbn [ctx_denote_under erase_ctx ctx_fv] in *;
    rewrite formula_fv_and;
    apply elem_of_union_l;
    rewrite formula_fv_basic_world_formula;
    rewrite lvars_fv_atom_env_to_lty_env_dom;
    set_solver.
Qed.

Lemma ctx_persistent_singleton_on_erase_subset
    Σ Γ X (m : WfWorldT) :
  X ⊆ dom (erase_ctx Γ) ->
  persistent_formula (ctx_denote_under Σ Γ) ->
  m ⊨ ctx_denote_under Σ Γ ->
  exists σ : StoreT,
    dom (σ : StoreT) = X /\
    res_restrict m X =
      (exist _ (singleton_world σ) (wf_singleton_world σ) : WfWorldT).
Proof.
  intros HX Hpersist Hctx.
  pose proof (Hpersist m Hctx) as Hpersist_m.
  apply res_models_persist_iff in Hpersist_m
    as [σbig [Hdom_big [Hrestrict_big _]]].
  exists (store_restrict σbig X).
  split.
  - change (dom (store_restrict σbig X : StoreT) = X).
    change (dom (σbig : StoreT) = formula_fv (ctx_denote_under Σ Γ))
      in Hdom_big.
    rewrite storeA_restrict_dom, Hdom_big.
    apply set_eq. intros a. split.
    + intros Ha. apply elem_of_intersection in Ha as [_ Ha]. exact Ha.
    + intros Ha. apply elem_of_intersection. split; [|exact Ha].
      apply ctx_denote_under_fv_contains_erase_dom.
      exact (HX a Ha).
  - transitivity (res_restrict (res_restrict m (formula_fv (ctx_denote_under Σ Γ))) X).
    + rewrite res_restrict_restrict_eq.
      replace (formula_fv (ctx_denote_under Σ Γ) ∩ X) with X.
	      * reflexivity.
	      * apply set_eq. intros a. split.
	        -- intros Ha. apply elem_of_intersection. split; [|exact Ha].
	           apply ctx_denote_under_fv_contains_erase_dom.
	           exact (HX a Ha).
	        -- intros Ha. apply elem_of_intersection in Ha as [_ Ha].
	           exact Ha.
    + rewrite Hrestrict_big.
      apply res_restrict_singleton_world.
Qed.

Lemma context_typing_wf_ret_value_obs_subset Σ Γ v τ :
  context_typing_wf Σ Γ (tret v) (CTPersist τ) ->
  fv_cty τ ∪ fv_value v ⊆ dom (erase_ctx Γ).
Proof.
  intros Hwf a Ha.
  apply elem_of_union in Ha as [Ha|Ha].
  - apply context_typing_wf_fv_cty_subset_erase_dom with
      (Σ := Σ) (e := tret v) (τ := CTPersist τ) in Hwf.
    cbn [fv_cty context_ty_lvars context_ty_lvars_at] in Hwf.
    exact (Hwf a Ha).
  - pose proof (context_typing_wf_fv_tm_subset Σ Γ (tret v)
      (CTPersist τ) Hwf) as Hfv.
    cbn [fv_tm] in Hfv.
    exact (Hfv a Ha).
Qed.

Lemma msubst_value_agree_on_restrict
    (σ1 σ2 : StoreT) X v :
  closed_env (store_restrict σ1 X) ->
  closed_env (store_restrict σ2 X) ->
  fv_value v ⊆ X ->
  store_restrict σ1 X = store_restrict σ2 X ->
  m{σ1} v = m{σ2} v.
Proof.
  intros Hclosed1 Hclosed2 HvX Hagree.
  rewrite <- (@msubst_restrict_closed_on value _ _ _ _ _
    σ1 X v Hclosed1 HvX).
  rewrite <- (@msubst_restrict_closed_on value _ _ _ _ _
    σ2 X v Hclosed2 HvX).
  change (m{(store_restrict σ1 X : StoreT)} v =
    m{(store_restrict σ2 X : StoreT)} v).
  rewrite Hagree. reflexivity.
Qed.

Lemma expr_result_formula_at_ret_value_closed_result
    D v y (my : WfWorldT) :
  tm_lvars (tret v) ⊆ D ->
  LVFree y ∉ D ->
  fv_value v ⊆ world_dom (my : WorldT) ->
  wfworld_closed_on (fv_value v) my ->
  lc_value v ->
  my ⊨ expr_result_formula_at D (tret v) (LVFree y) ->
  wfworld_closed_on ({[y]} : aset) my.
Proof.
  intros HvD HyD Hvdom Hclosed_v Hv Hres σ Hσ.
  pose proof (expr_result_formula_at_models_elim
    D (tret v) y my HvD HyD Hres σ Hσ) as Hstore.
  destruct Hstore as [_ [vy [Hylook Heval]]].
  assert (Hylook_free : σ !! y = Some vy).
  {
    change (((lstore_lift_free σ : LStoreT) : gmap logic_var value)
      !! LVFree y = Some vy) in Hylook.
    rewrite lstore_lift_free_lookup_free in Hylook.
    exact Hylook.
  }
  change (tm_eval_in_store σ (tret v) vy) in Heval.
  pose proof (proj2 (tm_eval_in_store_restrict_fv_subset
    σ (tret v) vy (fv_value v) ltac:(cbn [fv_tm]; set_solver)) Heval)
    as Heval_restrict.
  assert (Hclosed_restrict : store_closed (store_restrict σ (fv_value v))).
  { exact (Hclosed_v σ Hσ). }
  pose proof (tm_eval_in_store_ret_value_inv
    (store_restrict σ (fv_value v)) v vy
    Hclosed_restrict Hv Heval_restrict) as Hvy_eq.
  assert (Hdom_restrict :
      dom (store_restrict σ (fv_value v) : StoreT) = fv_value v).
  {
    change (dom (storeA_restrict σ (fv_value v) : gmap atom value) =
      fv_value v).
    rewrite storeA_restrict_dom.
    rewrite (wfworld_store_dom my σ Hσ).
    apply set_eq. intros a. set_solver.
  }
  split.
  - unfold closed_env. apply map_Forall_lookup_2.
    intros a va Hlook.
    apply storeA_restrict_lookup_some in Hlook as [Hay Hlook].
    replace a with y in Hlook by set_solver.
    assert (Hsome : Some va = Some vy).
    { transitivity (σ !! y); [symmetry; exact Hlook|exact Hylook_free]. }
    inversion Hsome. subst va.
    rewrite Hvy_eq.
    pose proof (msubst_fv_delete_value
      (store_restrict σ (fv_value v)) v (proj1 Hclosed_restrict))
      as Hfv.
    apply set_eq. intros x. split; [|set_solver].
    intros Hx.
    pose proof (Hfv x Hx) as Hx'.
    assert (Hxdom : x ∈ dom (store_restrict σ (fv_value v) : StoreT)).
    { rewrite Hdom_restrict. set_solver. }
    set_solver.
  - unfold lc_env. apply map_Forall_lookup_2.
    intros a va Hlook.
    apply storeA_restrict_lookup_some in Hlook as [Hay Hlook].
    replace a with y in Hlook by set_solver.
    assert (Hsome : Some va = Some vy).
    { transitivity (σ !! y); [symmetry; exact Hlook|exact Hylook_free]. }
    inversion Hsome. subst va.
    rewrite Hvy_eq.
    apply msubst_lc; [exact (proj2 Hclosed_restrict)|exact Hv].
Qed.

Lemma insert_relevant_env_ret_value_restrict_eq Σ τ v y :
  y ∉ lvars_fv (dom Σ) ∪ fv_cty τ ∪ fv_value v ->
  lty_env_restrict_lvars
    (<[LVFree y := erase_ty τ]>
      (relevant_env Σ τ (tret v)))
    (relevant_lvars τ (tret (vfvar y))) =
  lty_env_restrict_lvars
    (<[LVFree y := erase_ty τ]> Σ)
    (relevant_lvars τ (tret (vfvar y))).
Proof.
  apply RelevantEnv.insert_relevant_env_ret_value_restrict_eq.
Qed.

Lemma res_restrict_singleton_push_ret_value_result
    A D v y (m my : WfWorldT) σA :
  fv_value v ⊆ A ->
  A ⊆ world_dom (m : WorldT) ->
  y ∉ world_dom (m : WorldT) ->
  y ∉ A ->
  tm_lvars (tret v) ⊆ D ->
  LVFree y ∉ D ->
  my ⊨ expr_result_formula_at D (tret v) (LVFree y) ->
  wfworld_closed_on (A ∪ {[y]}) my ->
  lc_value v ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_restrict my (world_dom (m : WorldT)) = m ->
  res_restrict m A =
    (exist _ (singleton_world σA) (wf_singleton_world σA) : WfWorldT) ->
  exists σy : StoreT,
    dom (σy : StoreT) = A ∪ {[y]} /\
    res_restrict my (A ∪ {[y]}) =
      (exist _ (singleton_world σy) (wf_singleton_world σy) : WfWorldT).
Proof.
  intros HvA HAm Hym HyA HtmD HyD Hres Hclosed Hv Hdom_my Hbase Hsingle.
  destruct (wfA_ne _ (worldA_wf my)) as [σ0 Hσ0].
  set (σy := store_restrict σ0 (A ∪ {[y]}) : StoreT).
  exists σy.
  assert (Hdomσy : dom (σy : StoreT) = A ∪ {[y]}).
  {
    subst σy.
    change (dom (storeA_restrict σ0 (A ∪ {[y]}) : gmap atom value) =
      A ∪ {[y]}).
    rewrite storeA_restrict_dom.
    rewrite (wfworld_store_dom my σ0 Hσ0), Hdom_my.
    apply set_eq. intros a. set_solver.
  }
  split; [exact Hdomσy|].
  assert (Hres_small : my ⊨ expr_result_formula (tret v) (LVFree y)).
  {
    unfold expr_result_formula.
    eapply expr_result_formula_at_coarsen_domain.
    - exact HtmD.
    - intros a Ha. exact Ha.
    - exact HyD.
    - exact Hres.
  }
  apply wfworld_ext. apply world_ext.
  - change (world_dom (res_restrict my (A ∪ {[y]}) : WorldT) =
      dom (σy : StoreT)).
    rewrite res_restrict_dom, Hdomσy.
    apply set_eq. intros a. set_solver.
  - intros σ. split.
    + intros Hσproj.
      destruct Hσproj as [σmy [Hσmy Hσeq]]. subst σ.
      set (σm := store_restrict σmy (world_dom (m : WorldT)) : StoreT).
      set (σ0m := store_restrict σ0 (world_dom (m : WorldT)) : StoreT).
      assert (Hσm : (m : WorldT) σm).
      {
        subst σm.
        assert ((res_restrict my (world_dom (m : WorldT)) : WorldT)
          (store_restrict σmy (world_dom (m : WorldT)))).
        { exists σmy. split; [exact Hσmy|reflexivity]. }
        rewrite Hbase in H. exact H.
      }
      assert (Hσ0m : (m : WorldT) σ0m).
      {
        subst σ0m.
        assert ((res_restrict my (world_dom (m : WorldT)) : WorldT)
          (store_restrict σ0 (world_dom (m : WorldT)))).
        { exists σ0. split; [exact Hσ0|reflexivity]. }
        rewrite Hbase in H. exact H.
      }
      pose proof (res_restrict_singleton_store_eq
        m A σA σm Hsingle Hσm) as Hσm_A.
      pose proof (res_restrict_singleton_store_eq
        m A σA σ0m Hsingle Hσ0m) as Hσ0m_A.
      assert (HA_eq : store_restrict σmy A = store_restrict σ0 A).
      {
        transitivity (store_restrict σm A).
	        - subst σm. rewrite storeA_restrict_restrict.
	          replace (world_dom (m : WorldT) ∩ A) with A by set_solver.
	          reflexivity.
	        - rewrite Hσm_A. rewrite <- Hσ0m_A.
	          subst σ0m. rewrite storeA_restrict_restrict.
          replace (world_dom (m : WorldT) ∩ A) with A by set_solver.
          reflexivity.
      }
      assert (HclosedA : wfworld_closed_on A my).
      { eapply wfworld_closed_on_mono; [|exact Hclosed]. set_solver. }
      assert (Hinst_eq : m{σmy} v = m{σ0} v).
      {
        eapply msubst_value_agree_on_restrict.
        - exact (proj1 (HclosedA σmy Hσmy)).
        - exact (proj1 (HclosedA σ0 Hσ0)).
        - exact HvA.
        - exact HA_eq.
      }
      pose proof (expr_result_formula_ret_value_inst_eq_on
        my (A ∪ {[y]}) v y ltac:(set_solver) ltac:(set_solver)
        Hclosed Hv Hres_small σmy Hσmy) as Hy_my.
      pose proof (expr_result_formula_ret_value_inst_eq_on
        my (A ∪ {[y]}) v y ltac:(set_solver) ltac:(set_solver)
        Hclosed Hv Hres_small σ0 Hσ0) as Hy_0.
      assert (Hinst_my_big :
          m{(store_restrict σmy (A ∪ {[y]}) : StoreT)} v = m{σmy} v).
      {
        apply (@msubst_restrict_closed_on value _ _ _ _ _
          σmy (A ∪ {[y]}) v (proj1 (Hclosed σmy Hσmy))).
        set_solver.
      }
      assert (Hinst_0_big :
          m{(store_restrict σ0 (A ∪ {[y]}) : StoreT)} v = m{σ0} v).
      {
        apply (@msubst_restrict_closed_on value _ _ _ _ _
          σ0 (A ∪ {[y]}) v (proj1 (Hclosed σ0 Hσ0))).
        set_solver.
      }
      subst σy.
      apply storeA_map_eq. intros a.
      rewrite !storeA_restrict_lookup.
      destruct (decide (a ∈ A ∪ {[y]})) as [Ha|Ha]; [|reflexivity].
      destruct (decide (a = y)) as [->|Hay].
      * apply option_eq. intros vy. split; intros Hlook.
        -- assert (HlookR :
              (store_restrict σmy (A ∪ {[y]}) : StoreT) !! y = Some vy).
           { apply storeA_restrict_lookup_some_2; [exact Hlook|set_solver]. }
           pose proof Hy_my as Hy_my_v.
           rewrite (msubst_fvar_lookup_closed
             (store_restrict σmy (A ∪ {[y]}) : StoreT) y vy
             (proj1 (Hclosed σmy Hσmy)) HlookR) in Hy_my_v.
           assert (Hy0_dom : y ∈ dom (σ0 : StoreT)).
           {
             rewrite (wfworld_store_dom my σ0 Hσ0), Hdom_my.
             set_solver.
           }
           apply elem_of_dom in Hy0_dom as [v0 Hlook0].
           assert (Hlook0R :
              (store_restrict σ0 (A ∪ {[y]}) : StoreT) !! y = Some v0).
           { apply storeA_restrict_lookup_some_2; [exact Hlook0|set_solver]. }
           pose proof Hy_0 as Hy_0_v.
           rewrite (msubst_fvar_lookup_closed
             (store_restrict σ0 (A ∪ {[y]}) : StoreT) y v0
             (proj1 (Hclosed σ0 Hσ0)) Hlook0R) in Hy_0_v.
           assert (Hv0 : v0 = vy).
	           {
	             rewrite Hy_0_v, Hinst_0_big, <- Hinst_eq,
	               <- Hinst_my_big, <- Hy_my_v.
	             reflexivity.
	           }
	           rewrite Hv0 in Hlook0. exact Hlook0.
        -- assert (HlookR :
              (store_restrict σ0 (A ∪ {[y]}) : StoreT) !! y = Some vy).
           { apply storeA_restrict_lookup_some_2; [exact Hlook|set_solver]. }
           pose proof Hy_0 as Hy_0_v.
           rewrite (msubst_fvar_lookup_closed
             (store_restrict σ0 (A ∪ {[y]}) : StoreT) y vy
             (proj1 (Hclosed σ0 Hσ0)) HlookR) in Hy_0_v.
           assert (Hymy_dom : y ∈ dom (σmy : StoreT)).
           {
             rewrite (wfworld_store_dom my σmy Hσmy), Hdom_my.
             set_solver.
           }
           apply elem_of_dom in Hymy_dom as [v0 Hlook_my].
           assert (Hlook_myR :
              (store_restrict σmy (A ∪ {[y]}) : StoreT) !! y = Some v0).
           { apply storeA_restrict_lookup_some_2; [exact Hlook_my|set_solver]. }
           pose proof Hy_my as Hy_my_v.
           rewrite (msubst_fvar_lookup_closed
             (store_restrict σmy (A ∪ {[y]}) : StoreT) y v0
             (proj1 (Hclosed σmy Hσmy)) Hlook_myR) in Hy_my_v.
           assert (Hv0 : v0 = vy).
	           {
	             rewrite Hy_my_v, Hinst_my_big, Hinst_eq,
	               <- Hinst_0_big, <- Hy_0_v.
	             reflexivity.
	           }
	           rewrite Hv0 in Hlook_my. exact Hlook_my.
      * assert (HaA : a ∈ A) by set_solver.
        assert (HmyBig :
            (store_restrict σmy (A ∪ {[y]}) : StoreT) !! a = σmy !! a).
        {
          symmetry.
          eapply (store_lookup_eq_of_restrict_eq_full
            σmy (store_restrict σmy (A ∪ {[y]}) : StoreT)
            (A ∪ {[y]}) a); [exact Ha|reflexivity].
        }
        assert (H0Big :
            (store_restrict σ0 (A ∪ {[y]}) : StoreT) !! a = σ0 !! a).
        {
          symmetry.
          eapply (store_lookup_eq_of_restrict_eq_full
            σ0 (store_restrict σ0 (A ∪ {[y]}) : StoreT)
            (A ∪ {[y]}) a); [exact Ha|reflexivity].
        }
        assert (HmyA : (store_restrict σmy A : StoreT) !! a = σmy !! a).
        {
          symmetry.
          eapply (store_lookup_eq_of_restrict_eq_full
            σmy (store_restrict σmy A : StoreT) A a);
            [exact HaA|reflexivity].
        }
        assert (H0A : (store_restrict σ0 A : StoreT) !! a = σ0 !! a).
        {
          symmetry.
          eapply (store_lookup_eq_of_restrict_eq_full
            σ0 (store_restrict σ0 A : StoreT) A a);
            [exact HaA|reflexivity].
        }
        rewrite ?HmyBig, ?H0Big.
        transitivity ((store_restrict σmy A : StoreT) !! a).
        -- symmetry. exact HmyA.
        -- transitivity ((store_restrict σ0 A : StoreT) !! a).
           ++ exact (f_equal (fun ρ : StoreT => ρ !! a) HA_eq).
           ++ exact H0A.
    + intros Hσ.
      subst σy.
      apply singleton_world_member_eq in Hσ.
      subst σ.
      exists σ0. split; [exact Hσ0|reflexivity].
Qed.

(* The value-level singleton/result helper is intentionally kept separate from
   the typing-aware case lemma below: it is the only proof step that uses the
   fact that [ret v] is a value rather than an arbitrary term. *)
Lemma ty_denote_gas_persist_ret_value_intro_singleton
    gas Σ τ v σ (m : WfWorldT) :
  lty_env_closed Σ ->
  lc_value v ->
  dom (σ : StoreT) = fv_cty τ ∪ fv_value v ->
  res_restrict m (fv_cty τ ∪ fv_value v) =
    (exist _ (singleton_world σ) (wf_singleton_world σ) : WfWorldT) ->
  m ⊨ ty_denote_gas gas Σ τ (tret v) ->
  m ⊨ ty_denote_gas (S gas) Σ (CTPersist τ) (tret v).
Proof.
  intros HΣclosed Hv Hdomσ Hsingle Hden.
  pose proof (ty_denote_gas_guard_formula gas Σ τ
    (tret v) m Hden) as Hguard_src.
  assert (Hguard_tgt :
      m ⊨ ty_guard_formula
        (relevant_env Σ (CTPersist τ) (tret v))
        (CTPersist τ) (tret v)).
  { apply ty_guard_to_persist. exact Hguard_src. }
  eapply res_models_and_intro_from_models; [exact Hguard_tgt|].
  assert (Hscope_full :
      formula_scoped_in_world m
        (ty_denote_gas (S gas) Σ (CTPersist τ) (tret v))).
  {
    unfold formula_scoped_in_world.
    eapply ty_denote_gas_scope_of_guard.
    - reflexivity.
    - exact Hguard_tgt.
  }
  cbn [ty_denote_gas] in Hscope_full.
  pose proof (formula_scoped_and_r _ _ _ Hscope_full) as Hscope_forall.
  eapply res_models_forall_rev_intro; [exact Hscope_forall|].
  set (Dres := dom (relevant_env Σ (CTPersist τ) (tret v))).
  exists (world_dom (m : WorldT) ∪ lvars_fv (dom Σ) ∪
    lvars_fv Dres ∪ fv_cty τ ∪ fv_value v).
  intros y Hy my Hdom_my Hbase_my.
  rewrite formula_open_impl.
  eapply res_models_impl_intro.
  {
    rewrite <- formula_open_impl.
    eapply formula_scoped_forall_open_res_le.
    - exact Hscope_forall.
    - rewrite <- Hbase_my. apply res_restrict_le.
    - rewrite Hdom_my. apply elem_of_union_r. apply elem_of_singleton.
      reflexivity.
  }
  intros Hres.
  cbn [formula_open] in Hres.
  subst Dres.
  rewrite formula_open_expr_result_formula_at_shift0 in Hres.
  2:{ apply lvars_shift_from_lc. apply relevant_env_closed. exact HΣclosed. }
  2:{ rewrite lvars_shift_from_fv. clear -Hy. set_solver. }
  2:{ apply lc_ret_iff_value. exact Hv. }
  2:{ cbn [fv_tm]. clear -Hy. set_solver. }
  rewrite (lvars_shift_from_lc_eq 0
    (dom (relevant_env Σ (CTPersist τ) (tret v))))
    in Hres
    by (apply relevant_env_closed; exact HΣclosed).
  rewrite relevant_env_persist_eq in Hres.
  pose proof (res_models_and_elim_l _ _ _ Hguard_src) as Hwf_src.
  pose proof (res_models_and_elim_r _ _ _ Hguard_src) as Hguard_rest_src.
  pose proof (res_models_and_elim_l _ _ _ Hguard_rest_src) as Hworld_src.
  pose proof (res_models_and_elim_r _ _ _ Hguard_rest_src) as Hguard_tail_src.
  pose proof (res_models_and_elim_l _ _ _ Hguard_tail_src) as Hbasic_src.
  pose proof Hworld_src as Hworld_src_info.
  apply basic_world_formula_models_iff in Hworld_src_info
    as [_ [Hrel_world _]].
  pose proof Hwf_src as Hwf_src_info.
  apply context_ty_wf_formula_models_iff in Hwf_src_info
    as [HlcD_src [_ [HτD_src Hbasic_cty_src]]].
  assert (Hlcτ_src : lc_context_ty τ).
  {
    unfold lc_context_ty.
    eapply (context_ty_lvars_at_lc 0
      (dom (relevant_env Σ τ (tret v))) τ);
      eauto.
  }
  pose proof Hbasic_src as Hbasic_src_info.
  apply expr_basic_typing_formula_models_iff in Hbasic_src_info
    as [_ [_ Hbasic_lty_src]].
  pose proof (basic_tm_has_ltype_lvars _ _ _ Hbasic_lty_src) as HtmD_src.
  assert (HtmD_ret_src :
      tm_lvars (tret v) ⊆ dom (relevant_env Σ τ (tret v))).
  {
    rewrite (tm_lvars_lc_eq_atoms (tret v)).
    - exact HtmD_src.
    - constructor. exact Hv.
  }
  assert (HA_sub : fv_cty τ ∪ fv_value v ⊆ world_dom (m : WorldT)).
  {
    pose proof (res_restrict_singleton_exact_dom_subset
      m (fv_cty τ ∪ fv_value v) σ Hdomσ Hsingle) as Hsub.
    exact Hsub.
  }
  assert (Hy_m : y ∉ world_dom (m : WorldT)).
  { clear -Hy. set_solver. }
  assert (Hyτ : y ∉ fv_cty τ).
  { clear -Hy. set_solver. }
  assert (Hyv : y ∉ fv_value v).
  { clear -Hy. set_solver. }
  assert (Hclosed_v_m : wfworld_closed_on (fv_value v) m).
  {
    change (fv_value v) with (fv_tm (tret v)).
    eapply denot_ty_lvar_guard_wfworld_closed_on_term.
    exact Hguard_src.
  }
  assert (Hclosed_v_my : wfworld_closed_on (fv_value v) my).
  {
    eapply wfworld_closed_on_le.
    - intros a Ha. apply HA_sub. set_solver.
    - rewrite <- Hbase_my. apply res_restrict_le.
    - exact Hclosed_v_m.
  }
  assert (HDmy : lvars_fv
      (dom (relevant_env Σ (CTPersist τ) (tret v)))
      ⊆ world_dom (my : WorldT)).
  {
    intros a Ha.
    rewrite relevant_env_persist_eq in Ha.
    rewrite Hdom_my.
    apply elem_of_union_l.
    apply Hrel_world. exact Ha.
  }
  assert (HtmD_result :
      tm_lvars (tret v) ⊆
        dom (relevant_env Σ (CTPersist τ) (tret v))).
  { rewrite relevant_env_persist_eq. exact HtmD_ret_src. }
  assert (HyD_result :
      LVFree y ∉ dom (relevant_env Σ (CTPersist τ) (tret v))).
  {
    intros HyD.
    apply Hy_m.
    apply Hrel_world.
    apply lvars_fv_elem.
    rewrite relevant_env_persist_eq in HyD.
    exact HyD.
  }
  assert (Hclosed_y_my : wfworld_closed_on ({[y]} : aset) my).
  {
    eapply expr_result_formula_at_ret_value_closed_result.
    - exact HtmD_result.
    - exact HyD_result.
    - rewrite Hdom_my. intros a Ha. apply elem_of_union_l.
      apply HA_sub. set_solver.
    - exact Hclosed_v_my.
    - exact Hv.
    - exact Hres.
  }
  assert (Hclosed_τ_m : wfworld_closed_on (fv_cty τ) m).
  {
    eapply basic_world_formula_wfworld_closed_on_atoms.
    - intros lv Hlv.
      unfold lvars_of_atoms in Hlv.
      apply elem_of_map in Hlv as [a [-> Ha]].
      apply HτD_src.
      apply lvars_fv_elem.
      rewrite context_ty_lvars_fv.
      exact Ha.
    - exact Hworld_src.
  }
  assert (Hclosed_τ_my : wfworld_closed_on (fv_cty τ) my).
  {
    eapply wfworld_closed_on_le.
    - intros a Ha. apply HA_sub. set_solver.
    - rewrite <- Hbase_my. apply res_restrict_le.
    - exact Hclosed_τ_m.
  }
  assert (Hclosed_Ay :
      wfworld_closed_on (fv_cty τ ∪ fv_value v ∪ {[y]}) my).
  {
    apply wfworld_closed_on_union.
    - apply wfworld_closed_on_union; [exact Hclosed_τ_my|exact Hclosed_v_my].
    - exact Hclosed_y_my.
  }
  pose proof (res_restrict_singleton_push_ret_value_result
    (fv_cty τ ∪ fv_value v)
    (dom (relevant_env Σ (CTPersist τ) (tret v)))
    v y m my σ
    ltac:(set_solver) HA_sub Hy_m ltac:(set_solver)
    HtmD_result HyD_result Hres Hclosed_Ay Hv Hdom_my Hbase_my Hsingle)
    as [σy [Hdomσy Hsingle_y]].
  assert (Hinner_insert :
      my ⊨ ty_denote_gas gas
        (<[LVFree y := erase_ty τ]> Σ) τ (tret (vfvar y))).
  {
    eapply (ty_denote_gas_result_alias_at
      gas (<[LVFree y := erase_ty τ]> Σ) τ (tret v) y
      (dom (relevant_env Σ (CTPersist τ) (tret v))) my).
    - apply lty_env_closed_insert_free. exact HΣclosed.
    - apply relevant_env_closed. exact HΣclosed.
    - rewrite relevant_env_persist_eq. exact HtmD_ret_src.
    - rewrite relevant_env_persist_eq. exact HτD_src.
    - exact HyD_result.
    - exact HDmy.
    - apply map_lookup_insert.
    - exact Hres.
    - rewrite (ty_denote_gas_insert_fresh_lty_env_eq
        gas Σ τ (tret v) y (erase_ty τ)).
      2:{
        intros HyΣ.
        assert (HyΣfv : y ∈ lvars_fv (dom Σ)).
        { apply lvars_fv_elem. exact HyΣ. }
        apply Hy. clear -HyΣfv. set_solver.
      }
      2:{
        intros Hy_lvar.
        apply Hyτ.
        rewrite <- context_ty_lvars_fv.
        apply lvars_fv_elem. exact Hy_lvar.
      }
      2:{ cbn [fv_tm]. exact Hyv. }
      eapply (res_models_kripke m my).
      + rewrite <- Hbase_my. apply res_restrict_le.
      + exact Hden.
  }
  assert (Hinner_norm :
      my ⊨ ty_denote_gas gas
        (<[LVFree y := erase_ty τ]>
          (relevant_env Σ τ (tret v)))
        τ (tret (vfvar y))).
  {
    eapply res_models_ty_denote_gas_env_agree_on.
    - reflexivity.
    - symmetry. apply insert_relevant_env_ret_value_restrict_eq.
      clear -Hy. set_solver.
    - exact Hinner_insert.
  }
  rewrite formula_open_persist.
  rewrite formula_open_ty_denote_gas_singleton.
  2:{
    rewrite typed_lty_env_bind_lvars_fv_dom.
    intros HyD.
    apply Hy_m.
    apply Hrel_world.
    apply lvars_fv_elem.
    rewrite relevant_env_persist_eq in HyD.
    apply lvars_fv_elem in HyD.
    exact HyD.
  }
  2:{ cbn [fv_tm fv_value]. set_solver. }
  2:{ rewrite cty_shift_fv. exact Hyτ. }
  rewrite cty_open_shift_from_lc_fresh.
  2:{ exact Hlcτ_src. }
  2:{ exact Hyτ. }
  rewrite typed_lty_env_bind_open_current.
  2:{ exact HyD_result. }
  2:{ apply relevant_env_closed. exact HΣclosed. }
  change (erase_ty (CTPersist τ)) with (erase_ty τ).
  rewrite relevant_env_persist_eq.
  eapply (res_models_persist_intro_from_singleton_superset
    my
    (ty_denote_gas gas
      (<[LVFree y := erase_ty τ]>
        (relevant_env Σ τ (tret v)))
      τ (tret (vfvar y)))
    (fv_cty τ ∪ fv_value v ∪ {[y]}) σy).
  - etransitivity; [apply ty_denote_gas_fv_subset|].
    cbn [fv_tm fv_value]. set_solver.
  - exact Hdomσy.
  - exact Hsingle_y.
  - exact Hinner_norm.
Qed.

Lemma ty_denote_value_persist_intro_singleton
    Δ τ v σ (m : WfWorldT) :
  lc_value v ->
  dom (σ : StoreT) = fv_cty τ ∪ fv_value v ->
  res_restrict m (fv_cty τ ∪ fv_value v) =
    (exist _ (singleton_world σ) (wf_singleton_world σ) : WfWorldT) ->
  m ⊨ ty_denote Δ τ (tret v) ->
  m ⊨ ty_denote Δ (CTPersist τ) (tret v).
Proof.
  intros Hv Hdomσ Hsingle Hden.
  unfold ty_denote in *.
  cbn [cty_depth].
  eapply ty_denote_gas_persist_ret_value_intro_singleton; eauto.
  apply atom_store_to_lvar_store_closed.
Qed.

Lemma ty_denote_under_value_persist_intro Σ Γ τ v :
  context_typing_wf Σ Γ (tret v) (CTPersist τ) ->
  persistent_formula (ctx_denote_under Σ Γ) ->
  ctx_denote_under Σ Γ ⊫
    FImpl
      (ty_denote_under Σ Γ τ (tret v))
      (ty_denote_under Σ Γ (CTPersist τ) (tret v)).
Proof.
  intros Hwf Hpersist m Hctx.
  pose proof (context_typing_wf_ret_lc_value
    Σ Γ v (CTPersist τ) Hwf) as Hv.
  pose proof (context_typing_wf_ret_value_obs_subset
    Σ Γ v τ Hwf) as Hobs.
  pose proof (ctx_denote_under_basic_world Σ Γ m Hctx) as Hworld.
  pose proof (basic_world_formula_atom_env_dom_subset
    (ctx_erasure_under Σ Γ) m Hworld) as Hctxdom.
  ctx_erasure_under_norm_in Hctxdom.
  assert (Hobs_world : fv_cty τ ∪ fv_value v ⊆ world_dom (m : WorldT)).
  { intros a Ha. apply Hctxdom. pose proof (Hobs a Ha). set_solver. }
  eapply res_models_impl_intro_scoped.
  - unfold formula_scoped_in_world, ty_denote_under, ty_denote.
    etransitivity; [apply formula_fv_ty_denote_gas_subset_relevant|].
    cbn [fv_tm]. intros a Ha. apply Hobs_world. set_solver.
  - unfold formula_scoped_in_world, ty_denote_under, ty_denote.
    etransitivity; [apply formula_fv_ty_denote_gas_subset_relevant|].
    cbn [fv_tm fv_cty]. intros a Ha. apply Hobs_world. set_solver.
  - intros Hτ.
    destruct (ctx_persistent_singleton_on_erase_subset
      Σ Γ (fv_cty τ ∪ fv_value v) m Hobs Hpersist Hctx)
      as [σ [Hdomσ Hsingle]].
    unfold ty_denote_under in Hτ |- *.
    eapply ty_denote_value_persist_intro_singleton; eauto.
Qed.

Lemma fundamental_persist_intro_case Σ Γ τ v :
  context_typing_wf Σ Γ (tret v) (CTPersist τ) ->
  persistent_formula (ctx_denote_under Σ Γ) ->
  ctx_denote_under Σ Γ ⊫ ty_denote_under Σ Γ τ (tret v) ->
  ctx_denote_under Σ Γ ⊫
    ty_denote_under Σ Γ (CTPersist τ) (tret v).
Proof.
  intros Hwf Hpersist IH m Hctx.
  pose proof (IH m Hctx) as Hτ.
  pose proof (context_typing_wf_ret_lc_value
    Σ Γ v (CTPersist τ) Hwf) as Hv.
  pose proof (context_typing_wf_ret_value_obs_subset
    Σ Γ v τ Hwf) as Hobs.
  destruct (ctx_persistent_singleton_on_erase_subset
    Σ Γ (fv_cty τ ∪ fv_value v) m Hobs Hpersist Hctx)
    as [σ [Hdomσ Hsingle]].
  unfold ty_denote_under in Hτ |- *.
  eapply ty_denote_value_persist_intro_singleton; eauto.
Qed.
