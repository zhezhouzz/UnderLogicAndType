(** * Denotation.TypeEquiv

    Main term-result-equivalence transport theorem. *)

From Denotation Require Import Notation TypeDenote TypeDenoteRegular.
From Denotation Require Import
  TypeEquivCore
  TypeEquivTermBase TypeEquivTermResult
  TypeEquivFiberTransport
  TypeEquivFiberBaseCore TypeEquivFiberBaseProjected
  TypeEquivBody
  TypeEquivArrow
  ResultFirstOpen
  TypeEquivArrow
  TypeEquivWand
  TypeEquivWand
  TypeEquivTLet
  TypeEquivTLet.
From CoreLang Require Import StrongNormalization.

Section TypeDenote.

Lemma ty_static_guard_relevant_of_full
    (Σ : lty_env) τ e (m : WfWorldT) :
  m ⊨ ty_static_guard_formula Σ τ e ->
  m ⊨ ty_static_guard_formula (relevant_env Σ τ e) τ e.
Proof.
  intros Hstatic.
  unfold ty_static_guard_formula in Hstatic |- *.
  repeat rewrite res_models_and_iff in Hstatic |- *.
  destruct Hstatic as [Hwf [Hworld Hbasic]].
  assert (Hworld_rel : m ⊨ basic_world_formula (relevant_env Σ τ e)).
  {
    eapply basic_world_formula_subenv; [|exact Hworld].
    intros v T Hlook.
    unfold relevant_env, lty_env_restrict_lvars in Hlook.
    change ((storeA_restrict Σ (relevant_lvars τ e)
      : gmap logic_var ty) !! v = Some T) in Hlook.
    apply storeA_restrict_lookup_some in Hlook as [_ Hlook].
    exact Hlook.
  }
  split.
  - eapply context_ty_wf_formula_relevant_env; eauto.
  - split; [exact Hworld_rel|].
    apply expr_basic_typing_formula_models_iff.
    apply basic_world_formula_models_iff in Hworld as [HlcΣ _].
    apply basic_world_formula_models_iff in Hworld_rel as [HlcRel [HscopeRel _]].
    apply expr_basic_typing_formula_models_iff in Hbasic as [_ [_ Hty]].
    pose proof (basic_tm_has_ltype_lc Σ e (erase_ty τ) HlcΣ Hty)
      as Hlc_e.
    split; [exact HlcRel|]. split; [exact HscopeRel|].
    unfold relevant_env.
    eapply basic_tm_has_ltype_restrict_lvars_lc; [exact Hty|exact Hlc_e|].
    unfold relevant_lvars. set_solver.
Qed.

Lemma ty_guard_relevant_of_static_full_total
    (Σ : lty_env) τ e (m : WfWorldT) :
  m ⊨ ty_static_guard_formula Σ τ e ->
  m ⊨ expr_total_formula e ->
  m ⊨ ty_guard_formula (relevant_env Σ τ e) τ e.
Proof.
  intros Hstatic Htotal.
  pose proof (ty_static_guard_relevant_of_full Σ τ e m Hstatic)
    as Hstatic_rel.
  unfold ty_static_guard_formula in Hstatic_rel.
  unfold ty_guard_formula.
  repeat rewrite res_models_and_iff in Hstatic_rel.
  destruct Hstatic_rel as [Hwf [Hworld Hbasic]].
  repeat rewrite res_models_and_iff.
  split; [exact Hwf|].
  split; [exact Hworld|].
  split; [exact Hbasic|exact Htotal].
Qed.

Lemma ty_denote_gas_zero_transport_static_tm_equiv
    (Σ : lty_env) τ e_src e_tgt (m : WfWorldT) :
  tm_equiv_on m e_src e_tgt ->
  tm_total_equiv_on m e_src e_tgt ->
  m ⊨ ty_static_guard_formula Σ τ e_tgt ->
  lc_tm e_tgt ->
  fv_tm e_tgt ⊆ world_dom (m : WorldT) ->
  m ⊨ ty_denote_gas 0 Σ τ e_src ->
  m ⊨ ty_denote_gas 0 Σ τ e_tgt.
Proof.
  intros _ Htotal_equiv Hstatic Hlc Hfv Hzero_src.
  pose proof (ty_denote_gas_guard_of_zero
    Σ τ e_src m Hzero_src) as Hguard_src.
  repeat rewrite res_models_and_iff in Hguard_src.
  destruct Hguard_src as [_ [_ [_ Htotal_src]]].
  pose proof (tm_equiv_total m e_src e_tgt Htotal_equiv Hlc Hfv Htotal_src)
    as Htotal_tgt.
  apply ty_denote_gas_zero_of_guard.
  eapply ty_guard_relevant_of_static_full_total.
  - exact Hstatic.
  - exact Htotal_tgt.
Qed.

Lemma ty_denote_gas_zero_tret_of_static_guard
    (Σ : lty_env) τ v (m : WfWorldT) :
  m ⊨ ty_static_guard_formula Σ τ (tret v) ->
  m ⊨ ty_denote_gas 0 Σ τ (tret v).
Proof.
  intros Hstatic.
  assert (Htotal : m ⊨ expr_total_formula (tret v)).
  {
    unfold ty_static_guard_formula in Hstatic.
    repeat rewrite res_models_and_iff in Hstatic.
    destruct Hstatic as [_ [Hworld Hbasic]].
    eapply expr_total_formula_tret_of_basic; eauto.
  }
  apply ty_denote_gas_zero_of_guard.
  eapply ty_guard_relevant_of_static_full_total; eauto.
Qed.

Lemma ty_static_guard_fv_tm_subset
    (Σ : lty_env) τ e (m : WfWorldT) :
  m ⊨ ty_static_guard_formula Σ τ e ->
  fv_tm e ⊆ world_dom (m : WorldT).
Proof.
  intros Hstatic.
  unfold ty_static_guard_formula in Hstatic.
  repeat rewrite res_models_and_iff in Hstatic.
  destruct Hstatic as [_ [Hworld Hbasic]].
  apply expr_basic_typing_formula_models_iff in Hbasic
    as [_ [_ Hty]].
  pose proof (basic_tm_has_ltype_lvars _ _ _ Hty)
    as Htm_lvars.
  apply basic_world_formula_models_iff in Hworld
    as [_ [Hscope _]].
  intros a Ha.
  apply Hscope.
  apply lvars_fv_elem.
  apply Htm_lvars.
  unfold lvars_of_atoms.
    apply elem_of_map. exists a. split; [reflexivity|exact Ha].
Qed.

Lemma basic_world_insert_result_alias
    (Σ : lty_env) T e z (m : WfWorldT) :
  LVFree z ∉ dom Σ ->
  m ⊨ expr_result_formula e (LVFree z) ->
  m ⊨ basic_world_formula Σ ->
  m ⊨ expr_basic_typing_formula Σ e T ->
  m ⊨ basic_world_formula (<[LVFree z := T]> Σ).
Proof.
  intros HzΣ Hres Hworld Hbasic.
  pose proof Hworld as Hworld_formula.
  pose proof Hbasic as Hbasic_formula.
  apply basic_world_formula_models_iff in Hworld
    as [HlcΣ [HscopeΣ HtypedΣ]].
  apply expr_basic_typing_formula_models_iff in Hbasic
    as [_ [_ Hty]].
  pose proof (basic_tm_has_ltype_lvars Σ e T Hty) as HfvΣ.
  pose proof (expr_result_formula_to_atom_world e (LVFree z) m Hres)
    as Hres_world.
  destruct Hres_world as [_ [Hres_dom _]].
  assert (Hz_lworld : LVFree z ∈ lvars_of_atoms (world_dom (m : WorldT))).
  {
    rewrite <- res_lift_free_dom.
    apply Hres_dom.
    cbn [tm_lvars tm_lvars_at value_lvars_at lvar_value_keys].
    set_solver.
  }
  assert (Hz_world : z ∈ world_dom (m : WorldT)).
  {
    unfold lvars_of_atoms in Hz_lworld.
    apply elem_of_map in Hz_lworld as [a [Haz Ha]].
    inversion Haz. subst a. exact Ha.
  }
  apply basic_world_formula_models_iff.
  split.
  - apply lty_env_closed_insert_free. exact HlcΣ.
  - split.
    + rewrite dom_insert_L, lvars_fv_union, lvars_fv_singleton_free.
      intros a Ha.
      apply elem_of_union in Ha as [Ha|Ha].
      * apply elem_of_singleton in Ha. subst a.
        exact Hz_world.
      * exact (HscopeΣ _ Ha).
    + unfold lworld_has_type, worldA_has_type in HtypedΣ |- *.
      destruct HtypedΣ as [HdomΣ HstoresΣ].
      split.
      * rewrite res_lift_free_dom.
        rewrite dom_insert_L.
        intros v Hv.
        apply elem_of_union in Hv as [Hv|Hv].
        -- apply elem_of_singleton in Hv. subst v.
           exact Hz_lworld.
        -- exact (HdomΣ _ Hv).
      * intros ρ Hρ v U val HΣins Hρv.
        destruct Hρ as [σ [Hσ ->]].
        destruct v as [k|y].
        -- rewrite lookup_insert_ne in HΣins by discriminate.
           eapply HstoresΣ.
           ++ exists σ. split; [exact Hσ|reflexivity].
           ++ exact HΣins.
           ++ exact Hρv.
        -- destruct (decide (y = z)) as [->|Hyz].
           ++ apply lookup_insert_Some in HΣins
                as [[_ HU]|[Hneq _]]; [subst U|congruence].
              change (((lstore_lift_free σ : LStoreT)
                : gmap logic_var value) !! LVFree z = Some val) in Hρv.
              rewrite lstore_lift_free_lookup_free in Hρv.
              pose proof (expr_result_formula_to_atom_world
                e (LVFree z) m Hres) as Hres_world'.
              destruct Hres_world' as [_ [_ Hstores_res]].
              assert (Hlift :
                  (res_lift_free m : LWorldT) (lstore_lift_free σ)).
              { exists σ. split; [exact Hσ|reflexivity]. }
              specialize (Hstores_res (lstore_lift_free σ) Hlift)
                as [_ [vres [Hz_lookup Heval]]].
              change (((lstore_lift_free σ : LStoreT)
                : gmap logic_var value) !! LVFree z = Some vres)
                in Hz_lookup.
              rewrite lstore_lift_free_lookup_free in Hz_lookup.
              rewrite Hρv in Hz_lookup. inversion Hz_lookup. subst vres.
              set (σe := store_restrict σ (fv_tm e)).
              assert (Hσe_typed : atom_store_has_ltype Σ σe).
              {
                subst σe.
                intros a u Hlook.
                apply storeA_restrict_lookup_some in Hlook as [Hafve Hσa].
                assert (HaΣ : LVFree a ∈ dom Σ).
                {
                  apply HfvΣ.
                  unfold lvars_of_atoms. set_solver.
                }
                apply elem_of_dom in HaΣ as [Ua HΣa].
                exists Ua. split; [exact HΣa|].
                eapply HstoresΣ.
                - exists σ. split; [exact Hσ|reflexivity].
                - exact HΣa.
                - change (((lstore_lift_free σ : LStoreT)
                    : gmap logic_var value) !! LVFree a = Some u).
                  rewrite lstore_lift_free_lookup_free. exact Hσa.
              }
              assert (Heval_e :
                  tm_eval_in_store σe e val).
              {
                subst σe.
                apply (proj2 (tm_eval_in_store_restrict_fv_subset
                  σ e val (fv_tm e) ltac:(set_solver))).
                exact Heval.
              }
              assert (Hfv_dom : fv_tm e ⊆ dom (σe : StoreT)).
              {
                intros a Ha.
                assert (Haσ : a ∈ dom (σ : StoreT)).
                {
                  pose proof (wfworld_store_dom m σ Hσ) as Hσdom.
                  change (a ∈ dom (σ : gmap atom value)).
                  rewrite Hσdom.
                  apply HscopeΣ.
                  apply lvars_fv_elem.
                  apply HfvΣ.
                  unfold lvars_of_atoms. set_solver.
                }
                change (a ∈ dom (σ : gmap atom value)) in Haσ.
                apply elem_of_dom in Haσ as [u Hσa].
                change (a ∈ dom (σe : gmap atom value)).
                apply elem_of_dom. exists u.
                subst σe.
                apply (storeA_restrict_lookup_some_2 _ _ _ _ Hσa Ha).
              }
              eapply basic_tm_eval_value_type; eauto.
           ++ rewrite lookup_insert_ne in HΣins by congruence.
              eapply HstoresΣ.
              ** exists σ. split; [exact Hσ|reflexivity].
              ** exact HΣins.
              ** exact Hρv.
Qed.

Lemma basic_tm_has_ltype_tapp_tm_fvar_fun
    (Σ : lty_env) z y s T :
  lty_env_closed Σ ->
  Σ !! LVFree z = Some (s →ₜ T) ->
  Σ !! LVFree y = Some s ->
  basic_tm_has_ltype Σ (tapp_tm (tret (vfvar z)) (vfvar y)) T.
Proof.
  intros Hclosed Hz Hy.
  unfold tapp_tm.
  eapply BTT_Let with (T1 := s →ₜ T) (L := {[y]} ∪ lvars_fv (dom Σ)).
  - constructor. constructor. exact Hz.
  - intros f Hf.
    cbn [open_tm open_value value_shift].
    eapply BTT_App with (s1 := s) (s2 := T).
    + constructor. rewrite typed_lty_env_bind_open_current.
      * apply map_lookup_insert.
      * intros Hbad. apply Hf.
        apply elem_of_union_r. apply lvars_fv_elem. exact Hbad.
      * exact Hclosed.
    + constructor.
      rewrite typed_lty_env_bind_open_current.
      * rewrite lookup_insert_ne by set_solver. exact Hy.
      * intros Hbad. apply Hf.
        apply elem_of_union_r. apply lvars_fv_elem. exact Hbad.
      * exact Hclosed.
Qed.

Lemma ty_static_guard_tapp_fun_result_alias
    (Σ : lty_env) τ vf y z s (m : WfWorldT) :
  LVFree z ∉ dom Σ ->
  Σ !! LVFree y = Some s ->
  m ⊨ expr_result_formula (tret vf) (LVFree z) ->
  m ⊨ context_ty_wf_formula Σ τ ->
  m ⊨ basic_world_formula Σ ->
  m ⊨ expr_basic_typing_formula Σ (tret vf) (s →ₜ erase_ty τ) ->
  m ⊨ ty_static_guard_formula
    (<[LVFree z := s →ₜ erase_ty τ]> Σ) τ
    (tapp_tm (tret (vfvar z)) (vfvar y)).
Proof.
  intros HzΣ Hy Hres Hwf Hworld Hfun_basic.
  pose proof (basic_world_insert_result_alias
    Σ (s →ₜ erase_ty τ) (tret vf) z m
    HzΣ Hres Hworld Hfun_basic) as Hworld_insert.
  unfold ty_static_guard_formula.
  repeat rewrite res_models_and_iff.
  split.
  - apply context_ty_wf_formula_models_iff.
    apply context_ty_wf_formula_models_iff in Hwf
      as [Hlc [Hscope Hbasicτ]].
    apply basic_world_formula_models_iff in Hworld_insert
      as [Hlc_insert [Hscope_insert _]].
    split; [exact Hlc_insert|]. split; [exact Hscope_insert|].
    eapply basic_context_ty_lvars_mono; [|exact Hbasicτ].
    rewrite dom_insert_L. set_solver.
  - split; [exact Hworld_insert|].
    apply expr_basic_typing_formula_models_iff.
    apply basic_world_formula_models_iff in Hworld_insert
      as [Hlc_insert [Hscope_insert _]].
    split; [exact Hlc_insert|]. split; [exact Hscope_insert|].
    eapply (basic_tm_has_ltype_tapp_tm_fvar_fun
      (<[LVFree z := s →ₜ erase_ty τ]> Σ) z y s (erase_ty τ)).
    + exact Hlc_insert.
    + apply map_lookup_insert.
    + rewrite lookup_insert_ne by
        (intros Heq; inversion Heq; subst; apply HzΣ; apply elem_of_dom; eauto).
      exact Hy.
Qed.

Lemma ty_denote_gas_zero_tapp_fun_result_alias
    (Σ : lty_env) τ vf y z s (m : WfWorldT) :
  LVFree z ∉ dom Σ ->
  z ∉ fv_value vf ∪ {[y]} ∪ fv_cty τ ->
  Σ !! LVFree y = Some s ->
  wfworld_closed_on
    (fv_tm (tapp_tm (tret (vfvar z)) (vfvar y)) ∪
     fv_tm (tapp_tm (tret vf) (vfvar y))) m ->
  lc_value vf ->
  m ⊨ expr_result_formula (tret vf) (LVFree z) ->
  m ⊨ context_ty_wf_formula Σ τ ->
  m ⊨ basic_world_formula Σ ->
  m ⊨ expr_basic_typing_formula Σ (tret vf) (s →ₜ erase_ty τ) ->
  m ⊨ ty_denote_gas 0 Σ τ (tapp_tm (tret vf) (vfvar y)) ->
  m ⊨ ty_denote_gas 0
    (<[LVFree z := s →ₜ erase_ty τ]> Σ) τ
    (tapp_tm (tret (vfvar z)) (vfvar y)).
Proof.
  intros HzΣ Hzfresh Hy Hclosed Hvf Hres Hwf Hworld Hfun_basic Hzero_src.
  assert (Hzτ : LVFree z ∉ context_ty_lvars τ).
  {
    intros Hbad. apply Hzfresh.
    apply lvars_fv_elem in Hbad.
    rewrite context_ty_lvars_fv in Hbad.
    set_solver.
  }
  assert (Hzsrc : z ∉ fv_tm (tapp_tm (tret vf) (vfvar y))).
  {
    rewrite fv_tapp_tm. cbn [fv_tm fv_value].
    set_solver.
  }
  assert (Hzero_src_insert :
      m ⊨ ty_denote_gas 0
        (<[LVFree z := s →ₜ erase_ty τ]> Σ) τ
        (tapp_tm (tret vf) (vfvar y))).
  {
    eapply ty_denote_gas_insert_fresh_lty_env; eauto.
  }
  assert (Hstatic_tgt :
      m ⊨ ty_static_guard_formula
        (<[LVFree z := s →ₜ erase_ty τ]> Σ) τ
        (tapp_tm (tret (vfvar z)) (vfvar y))).
  {
    eapply ty_static_guard_tapp_fun_result_alias; eauto.
  }
  pose proof (tm_equiv_tapp_value_fun_result_alias
    m vf y z Hclosed Hvf Hres) as Hequiv.
  pose proof (tm_total_equiv_tapp_value_fun_result_alias
    m vf y z Hclosed Hvf Hres) as Htotal_equiv.
  assert (Hequiv_src_tgt :
      tm_equiv_on m
        (tapp_tm (tret vf) (vfvar y))
        (tapp_tm (tret (vfvar z)) (vfvar y))).
  {
    intros σ v Hσ.
    pose proof (Hequiv σ v Hσ) as [Hzt Hvz].
    split; [exact Hvz|exact Hzt].
  }
  assert (Htotal_src_tgt :
      tm_total_equiv_on m
        (tapp_tm (tret vf) (vfvar y))
        (tapp_tm (tret (vfvar z)) (vfvar y))).
  {
    intros σ Hσ.
    pose proof (Htotal_equiv σ Hσ) as [Hzt Hvz].
    split; [exact Hvz|exact Hzt].
  }
  eapply ty_denote_gas_zero_transport_static_tm_equiv.
  - exact Hequiv_src_tgt.
  - exact Htotal_src_tgt.
  - exact Hstatic_tgt.
  - apply lc_tapp_tm; [constructor; constructor | constructor].
  - eapply ty_static_guard_fv_tm_subset. exact Hstatic_tgt.
  - exact Hzero_src_insert.
Qed.

Lemma ty_static_guard_ret_value_result_alias
    (Σ : lty_env) τ (m : WfWorldT) vx z :
  lty_env_closed Σ ->
  Σ !! LVFree z = Some (erase_ty τ) ->
  m ⊨ expr_result_formula (tret vx) (LVFree z) ->
  m ⊨ ty_static_guard_formula Σ τ (tret vx) ->
  m ⊨ ty_static_guard_formula Σ τ (tret (vfvar z)).
Proof.
  intros HΣclosed Hlookup Hres Hstatic.
  assert (Htotal_vx : m ⊨ expr_total_formula (tret vx)).
  {
    unfold ty_static_guard_formula in Hstatic.
    repeat rewrite res_models_and_iff in Hstatic.
    destruct Hstatic as [_ [Hworld Hbasic]].
    eapply expr_total_formula_tret_of_basic; eauto.
  }
  assert (Hguard_vx :
      m ⊨ FAnd
        (context_ty_wf_formula Σ τ)
        (FAnd
          (basic_world_formula Σ)
          (FAnd
            (expr_basic_typing_formula Σ (tret vx) (erase_ty τ))
            (expr_total_formula (tret vx))))).
  {
    unfold ty_static_guard_formula in Hstatic.
    repeat rewrite res_models_and_iff in Hstatic.
    destruct Hstatic as [Hwf [Hworld Hbasic]].
    apply res_models_and_iff. split; [exact Hwf|].
    apply res_models_and_iff. split; [exact Hworld|].
    apply res_models_and_iff. split; [exact Hbasic|exact Htotal_vx].
  }
  pose proof (ty_denote_gas_result_alias_guard
    Σ τ (tret vx) z m Hlookup Hguard_vx)
    as Hguard_z.
  unfold ty_static_guard_formula.
  repeat rewrite res_models_and_iff in Hguard_z.
  destruct Hguard_z as [Hwf [Hworld [Hbasic _]]].
  apply res_models_and_iff. split; [exact Hwf|].
  apply res_models_and_iff. split; [exact Hworld|exact Hbasic].
Qed.

Lemma typed_total_equiv_ret_value_result_alias_static
    (Σ : lty_env) τ (m : WfWorldT) vx z :
  wfworld_closed_on (fv_tm (tret (vfvar z)) ∪ fv_tm (tret vx)) m ->
  lc_value vx ->
  m ⊨ expr_result_formula (tret vx) (LVFree z) ->
  m ⊨ ty_static_guard_formula Σ τ (tret (vfvar z)) ->
  m ⊨ ty_denote_gas 0 Σ τ (tret vx) ->
  typed_total_equiv_on Σ τ m (tret vx) (tret (vfvar z)).
Proof.
  intros Hclosed Hvx Hres Hstatic_tgt Hzero_v.
  pose proof (tm_equiv_ret_value_result_alias
    m vx z Hclosed Hvx Hres) as Heq_zv.
  pose proof (tm_total_equiv_ret_value_result_alias
    m vx z Hclosed Hvx Hres) as Htotal_zv.
  assert (Heq_vz : tm_equiv_on m (tret vx) (tret (vfvar z))).
  {
    intros σ v Hσ.
    pose proof (Heq_zv σ v Hσ) as [Hzv Hvz].
    split; [exact Hvz|exact Hzv].
  }
  assert (Htotal_vz : tm_total_equiv_on m (tret vx) (tret (vfvar z))).
  {
    intros σ Hσ.
    pose proof (Htotal_zv σ Hσ) as [Hzv Hvz].
    split; [exact Hvz|exact Hzv].
  }
  assert (Hzero_z :
      m ⊨ ty_denote_gas 0 Σ τ (tret (vfvar z))).
  {
    eapply ty_denote_gas_zero_transport_static_tm_equiv.
    - exact Heq_vz.
    - exact Htotal_vz.
    - exact Hstatic_tgt.
    - constructor. constructor.
    - eapply ty_static_guard_fv_tm_subset. exact Hstatic_tgt.
    - exact Hzero_v.
  }
  split; [exact Heq_vz|].
  split; [exact Htotal_vz|].
  split; [exact Hzero_v|exact Hzero_z].
Qed.

Lemma ty_static_guard_fv_subset
    (Σ : lty_env) τ e (m : WfWorldT) :
  m ⊨ ty_static_guard_formula Σ τ e ->
  fv_tm e ∪ fv_cty τ ⊆ world_dom (m : WorldT).
Proof.
  intros Hstatic a Ha.
  apply elem_of_union in Ha as [Ha|Ha].
  - eapply ty_static_guard_fv_tm_subset; eauto.
  - unfold ty_static_guard_formula in Hstatic.
    repeat rewrite res_models_and_iff in Hstatic.
    destruct Hstatic as [Hwf [Hworld _]].
    pose proof (context_ty_wf_formula_fv_cty_subset
      Σ τ m Hwf a Ha) as HΣa.
    apply basic_world_formula_models_iff in Hworld
      as [_ [Hscope _]].
    exact (Hscope _ HΣa).
Qed.

Lemma ty_denote_gas_fv_tm_subset
    gas (Σ : lty_env) τ e (m : WfWorldT) :
  m ⊨ ty_denote_gas gas Σ τ e ->
  fv_tm e ⊆ world_dom (m : WorldT).
Proof.
  intros Hden.
  pose proof (ty_denote_gas_guard gas Σ τ e m Hden) as Hguard.
  unfold ty_guard_formula in Hguard.
  repeat rewrite res_models_and_iff in Hguard.
  destruct Hguard as [_ [Hworld [Hbasic _]]].
  apply expr_basic_typing_formula_models_iff in Hbasic as [_ [_ Hty]].
  pose proof (basic_tm_has_ltype_lvars _ _ _ Hty) as Htm_lvars.
  apply basic_world_formula_models_iff in Hworld as [_ [Hscope _]].
  intros a Ha.
  apply Hscope.
  apply lvars_fv_elem.
  apply Htm_lvars.
  unfold lvars_of_atoms.
  apply elem_of_map. exists a. split; [reflexivity|exact Ha].
Qed.

Lemma ty_static_guard_wfworld_closed_on_term
    (Σ : lty_env) τ e (m : WfWorldT) :
  m ⊨ ty_static_guard_formula Σ τ e ->
  wfworld_closed_on (fv_tm e) m.
Proof.
  intros Hstatic.
  unfold ty_static_guard_formula in Hstatic.
  repeat rewrite res_models_and_iff in Hstatic.
  destruct Hstatic as [_ [Hworld Hbasic]].
  apply expr_basic_typing_formula_models_iff in Hbasic
    as [_ [_ Hty]].
  eapply basic_world_formula_wfworld_closed_on_atoms;
    [eapply basic_tm_has_ltype_lvars; exact Hty|exact Hworld].
Qed.

Lemma ty_static_guard_context_wf
    (Σ : lty_env) τ e (m : WfWorldT) :
  m ⊨ ty_static_guard_formula Σ τ e ->
  m ⊨ context_ty_wf_formula Σ τ.
Proof.
  intros Hstatic.
  unfold ty_static_guard_formula in Hstatic.
  repeat rewrite res_models_and_iff in Hstatic.
  tauto.
Qed.

Lemma ty_static_guard_basic_world
    (Σ : lty_env) τ e (m : WfWorldT) :
  m ⊨ ty_static_guard_formula Σ τ e ->
  m ⊨ basic_world_formula Σ.
Proof.
  intros Hstatic.
  unfold ty_static_guard_formula in Hstatic.
  repeat rewrite res_models_and_iff in Hstatic.
  tauto.
Qed.

Lemma ty_static_guard_basic_typing
    (Σ : lty_env) τ e (m : WfWorldT) :
  m ⊨ ty_static_guard_formula Σ τ e ->
  m ⊨ expr_basic_typing_formula Σ e (erase_ty τ).
Proof.
  intros Hstatic.
  unfold ty_static_guard_formula in Hstatic.
  repeat rewrite res_models_and_iff in Hstatic.
  tauto.
Qed.

Lemma ty_static_guard_insert_irrelevant
    (Σ : lty_env) τ e x T (m : WfWorldT) :
  LVFree x ∉ dom Σ ->
  LVFree x ∉ relevant_lvars τ e ->
  m ⊨ basic_world_formula (<[LVFree x := T]> Σ) ->
  m ⊨ ty_static_guard_formula Σ τ e ->
  m ⊨ ty_static_guard_formula (<[LVFree x := T]> Σ) τ e.
Proof.
  intros HxΣ Hxrel Hworld_insert Hstatic.
  unfold ty_static_guard_formula in Hstatic |- *.
  repeat rewrite res_models_and_iff in Hstatic |- *.
  destruct Hstatic as [Hwf [Hworld Hbasic]].
  split.
  - apply context_ty_wf_formula_models_iff.
    apply context_ty_wf_formula_models_iff in Hwf
      as [_ [_ Hτwf]].
    apply basic_world_formula_models_iff in Hworld_insert
      as [Hlc_insert [Hscope_insert _]].
    split; [exact Hlc_insert|]. split; [exact Hscope_insert|].
    eapply basic_context_ty_lvars_mono; [|exact Hτwf].
    rewrite dom_insert_L. set_solver.
  - split; [exact Hworld_insert|].
    apply expr_basic_typing_formula_models_iff.
    apply expr_basic_typing_formula_models_iff in Hbasic
      as [_ [_ Hety]].
    apply basic_world_formula_models_iff in Hworld_insert
      as [Hlc_insert [Hscope_insert _]].
    split; [exact Hlc_insert|]. split; [exact Hscope_insert|].
    eapply basic_tm_has_ltype_weaken; [exact Hety|].
    apply insert_subseteq.
    apply not_elem_of_dom. exact HxΣ.
Qed.

Lemma ty_denote_gas_tm_equiv
    gas Σ τ e1 e2 (m : WfWorldT) :
  typed_total_equiv_on Σ τ m e1 e2 ->
  m ⊨ ty_denote_gas gas Σ τ e1 ->
  m ⊨ ty_denote_gas gas Σ τ e2.
Proof.
  revert Σ τ e1 e2 m.
  induction gas as [|gas IH]; intros Σ τ e1 e2 m Hequiv Hm.
  - exact (typed_total_equiv_target_zero _ _ _ _ _ Hequiv).
  - pose proof (typed_total_equiv_target_zero
      Σ τ m e1 e2 Hequiv) as Hzero_tgt.
    pose proof (ty_denote_gas_guard_of_zero
      Σ τ e2 m Hzero_tgt) as Hguard_tgt.
    repeat rewrite res_models_and_iff in Hguard_tgt.
    destruct τ as [b φ|b φ|τ1 τ2|τ1 τ2|τ1 τ2|τx τr|τx τr|τ1];
      cbn [ty_denote_gas ty_guard_formula] in Hm |- *;
      unfold ty_guard_formula in Hm |- *;
      repeat rewrite res_models_and_iff in Hm |- *;
      destruct Hm as [_ Hbody]; split.
    all: try exact Hguard_tgt.
    + eapply ty_denote_gas_tm_equiv_over_body; eauto.
    + eapply ty_denote_gas_tm_equiv_under_body; eauto.
    + eapply ty_denote_gas_tm_equiv_inter_body; eauto.
    + eapply ty_denote_gas_tm_equiv_union_body; eauto.
    + eapply ty_denote_gas_tm_equiv_sum_body; eauto.
    + eapply ty_denote_gas_tm_equiv_arrow_body; eauto.
    + eapply ty_denote_gas_tm_equiv_wand_body; eauto.
    + pose proof (typed_fiber_equiv_of_tm_equiv
        Σ (CTPersist τ1) m e1 e2
        (typed_total_equiv_tm_equiv _ _ _ _ _ Hequiv)
        (typed_total_equiv_source_zero _ _ _ _ _ Hequiv)
        Hzero_tgt) as Hfib.
      pose proof (typed_fiber_equiv_result_projected _ _ _ _ _ Hfib)
        as [_ Htgt_to_src].
      eapply (tlet_persist_body_transport gas Σ τ1 e1 e2 m);
        [eapply typed_total_equiv_source_zero; exact Hequiv
        |exact Hzero_tgt
        |exact Htgt_to_src
        |exact Hbody].
Qed.

Lemma ty_denote_gas_tapp_fun_result_alias
    gas (Σ : lty_env) τ vf y z s (m : WfWorldT) :
  LVFree z ∉ dom Σ ->
  z ∉ fv_value vf ∪ {[y]} ∪ fv_cty τ ->
  Σ !! LVFree y = Some s ->
  wfworld_closed_on
    (fv_tm (tapp_tm (tret (vfvar z)) (vfvar y)) ∪
     fv_tm (tapp_tm (tret vf) (vfvar y))) m ->
  lc_value vf ->
  m ⊨ expr_result_formula (tret vf) (LVFree z) ->
  m ⊨ context_ty_wf_formula Σ τ ->
  m ⊨ basic_world_formula Σ ->
  m ⊨ expr_basic_typing_formula Σ (tret vf) (s →ₜ erase_ty τ) ->
  m ⊨ ty_denote_gas gas Σ τ (tapp_tm (tret vf) (vfvar y)) ->
  m ⊨ ty_denote_gas gas
    (<[LVFree z := s →ₜ erase_ty τ]> Σ) τ
    (tapp_tm (tret (vfvar z)) (vfvar y)).
Proof.
  intros HzΣ Hzfresh Hy Hclosed Hvf Hres Hwf Hworld Hfun_basic Hsrc.
  pose proof (ty_denote_gas_guard gas Σ τ
    (tapp_tm (tret vf) (vfvar y)) m Hsrc) as Hguard_src.
  pose proof (ty_denote_gas_zero_of_guard Σ τ
    (tapp_tm (tret vf) (vfvar y)) m Hguard_src) as Hzero_src.
  pose proof (ty_denote_gas_zero_tapp_fun_result_alias
    Σ τ vf y z s m HzΣ Hzfresh Hy Hclosed Hvf Hres
    Hwf Hworld Hfun_basic Hzero_src) as Hzero_tgt.
  assert (Hequiv_src_tgt :
      tm_equiv_on m
        (tapp_tm (tret vf) (vfvar y))
        (tapp_tm (tret (vfvar z)) (vfvar y))).
  {
    pose proof (tm_equiv_tapp_value_fun_result_alias
      m vf y z Hclosed Hvf Hres) as Hequiv.
    intros σ v Hσ.
    pose proof (Hequiv σ v Hσ) as [Hzt Hvz].
    split; [exact Hvz|exact Hzt].
  }
  assert (Htotal_src_tgt :
      tm_total_equiv_on m
        (tapp_tm (tret vf) (vfvar y))
        (tapp_tm (tret (vfvar z)) (vfvar y))).
  {
    pose proof (tm_total_equiv_tapp_value_fun_result_alias
      m vf y z Hclosed Hvf Hres) as Htotal_equiv.
    intros σ Hσ.
    pose proof (Htotal_equiv σ Hσ) as [Hzt Hvz].
    split; [exact Hvz|exact Hzt].
  }
  assert (Hzero_src_insert :
      m ⊨ ty_denote_gas 0
        (<[LVFree z := s →ₜ erase_ty τ]> Σ) τ
        (tapp_tm (tret vf) (vfvar y))).
  {
    assert (Hzτ : LVFree z ∉ context_ty_lvars τ).
    {
      intros Hbad. apply Hzfresh.
      apply lvars_fv_elem in Hbad.
      rewrite context_ty_lvars_fv in Hbad.
      set_solver.
    }
    assert (Hzsrc : z ∉ fv_tm (tapp_tm (tret vf) (vfvar y))).
    {
      rewrite fv_tapp_tm. cbn [fv_tm fv_value].
      set_solver.
    }
    eapply ty_denote_gas_insert_fresh_lty_env; eauto.
  }
  assert (Htyped :
      typed_total_equiv_on
        (<[LVFree z := s →ₜ erase_ty τ]> Σ) τ m
        (tapp_tm (tret vf) (vfvar y))
        (tapp_tm (tret (vfvar z)) (vfvar y))).
  {
    split; [exact Hequiv_src_tgt|].
    split; [exact Htotal_src_tgt|].
    split; [exact Hzero_src_insert|exact Hzero_tgt].
  }
  eapply ty_denote_gas_tm_equiv; [exact Htyped|].
  eapply (ty_denote_gas_insert_fresh_lty_env
    gas Σ τ (tapp_tm (tret vf) (vfvar y)) z (s →ₜ erase_ty τ) m).
  - exact HzΣ.
  - intros Hbad. apply Hzfresh.
    apply lvars_fv_elem in Hbad.
    rewrite context_ty_lvars_fv in Hbad.
    set_solver.
  - rewrite fv_tapp_tm. cbn [fv_tm fv_value]. set_solver.
  - exact Hsrc.
Qed.

Lemma ty_static_guard_tapp_fun_result_base
    (Σ : lty_env) τ vf y s (m : WfWorldT) :
  Σ !! LVFree y = Some s ->
  m ⊨ context_ty_wf_formula Σ τ ->
  m ⊨ basic_world_formula Σ ->
  m ⊨ expr_basic_typing_formula Σ (tret vf) (s →ₜ erase_ty τ) ->
  m ⊨ ty_static_guard_formula Σ τ
    (tapp_tm (tret vf) (vfvar y)).
Proof.
  intros Hy Hwf Hworld Hfun_basic.
  unfold ty_static_guard_formula.
  repeat rewrite res_models_and_iff.
  split; [exact Hwf|].
  split; [exact Hworld|].
  apply expr_basic_typing_formula_models_iff.
  apply basic_world_formula_models_iff in Hworld
    as [HlcΣ [Hscope _]].
  apply expr_basic_typing_formula_models_iff in Hfun_basic
    as [_ [_ Hfun_ty]].
  split; [exact HlcΣ|]. split; [exact Hscope|].
  unfold tapp_tm.
  eapply BTT_Let with (T1 := s →ₜ erase_ty τ)
    (L := {[y]} ∪ lvars_fv (dom Σ)).
  - exact Hfun_ty.
  - intros f Hf.
    cbn [open_tm open_value value_shift].
    eapply BTT_App with (s1 := s) (s2 := erase_ty τ).
    + constructor.
      rewrite typed_lty_env_bind_open_current.
      * apply map_lookup_insert.
      * intros Hbad. apply Hf.
        apply elem_of_union_r. apply lvars_fv_elem. exact Hbad.
      * exact HlcΣ.
    + constructor.
      rewrite typed_lty_env_bind_open_current.
      * rewrite lookup_insert_ne by set_solver. exact Hy.
      * intros Hbad. apply Hf.
        apply elem_of_union_r. apply lvars_fv_elem. exact Hbad.
      * exact HlcΣ.
Qed.

Lemma ty_denote_gas_tapp_fun_result_alias_back
    gas (Σ : lty_env) τ vf y z s (m : WfWorldT) :
  LVFree z ∉ dom Σ ->
  z ∉ fv_value vf ∪ {[y]} ∪ fv_cty τ ->
  Σ !! LVFree y = Some s ->
  wfworld_closed_on
    (fv_tm (tapp_tm (tret (vfvar z)) (vfvar y)) ∪
     fv_tm (tapp_tm (tret vf) (vfvar y))) m ->
  lc_value vf ->
  m ⊨ expr_result_formula (tret vf) (LVFree z) ->
  m ⊨ context_ty_wf_formula Σ τ ->
  m ⊨ basic_world_formula Σ ->
  m ⊨ expr_basic_typing_formula Σ (tret vf) (s →ₜ erase_ty τ) ->
  m ⊨ ty_denote_gas gas
    (<[LVFree z := s →ₜ erase_ty τ]> Σ) τ
    (tapp_tm (tret (vfvar z)) (vfvar y)) ->
  m ⊨ ty_denote_gas gas Σ τ
    (tapp_tm (tret vf) (vfvar y)).
Proof.
  intros HzΣ Hzfresh Hy Hclosed Hvf Hres Hwf Hworld Hfun_basic Hsrc.
  pose proof (tm_equiv_tapp_value_fun_result_alias
    m vf y z Hclosed Hvf Hres) as Hequiv_src_tgt.
  pose proof (tm_total_equiv_tapp_value_fun_result_alias
    m vf y z Hclosed Hvf Hres) as Htotal_src_tgt.
  pose proof (ty_denote_gas_guard gas
    (<[LVFree z := s →ₜ erase_ty τ]> Σ) τ
    (tapp_tm (tret (vfvar z)) (vfvar y)) m Hsrc) as Hguard_src.
  pose proof (ty_denote_gas_zero_of_guard
    (<[LVFree z := s →ₜ erase_ty τ]> Σ) τ
    (tapp_tm (tret (vfvar z)) (vfvar y)) m Hguard_src)
    as Hzero_src.
  assert (Hstatic_tgt :
      m ⊨ ty_static_guard_formula Σ τ
        (tapp_tm (tret vf) (vfvar y))).
  { eapply ty_static_guard_tapp_fun_result_base; eauto. }
  assert (Htotal_tgt :
      m ⊨ expr_total_formula (tapp_tm (tret vf) (vfvar y))).
  {
    repeat rewrite res_models_and_iff in Hguard_src.
    destruct Hguard_src as [_ [_ [_ Htotal_src]]].
    eapply tm_equiv_total.
    - exact Htotal_src_tgt.
    - apply lc_tapp_tm; [constructor; exact Hvf|constructor].
    - exact (ty_static_guard_fv_tm_subset _ _ _ _ Hstatic_tgt).
    - exact Htotal_src.
  }
  assert (Hzero_tgt :
      m ⊨ ty_denote_gas 0 Σ τ
        (tapp_tm (tret vf) (vfvar y))).
  {
    apply ty_denote_gas_zero_of_guard_formula.
    eapply ty_guard_relevant_of_static_full_total; eauto.
  }
  assert (Hzero_tgt_insert :
      m ⊨ ty_denote_gas 0
        (<[LVFree z := s →ₜ erase_ty τ]> Σ) τ
        (tapp_tm (tret vf) (vfvar y))).
  {
    eapply ty_denote_gas_insert_fresh_lty_env; eauto.
    - intros Hbad. apply Hzfresh.
      apply lvars_fv_elem in Hbad.
      rewrite context_ty_lvars_fv in Hbad. set_solver.
    - rewrite fv_tapp_tm. cbn [fv_tm fv_value]. set_solver.
  }
  assert (Htyped :
      typed_total_equiv_on
        (<[LVFree z := s →ₜ erase_ty τ]> Σ) τ m
        (tapp_tm (tret (vfvar z)) (vfvar y))
        (tapp_tm (tret vf) (vfvar y))).
  {
    split; [exact Hequiv_src_tgt|].
    split; [exact Htotal_src_tgt|].
    split; [exact Hzero_src|exact Hzero_tgt_insert].
  }
  pose proof (ty_denote_gas_tm_equiv gas
    (<[LVFree z := s →ₜ erase_ty τ]> Σ) τ
    (tapp_tm (tret (vfvar z)) (vfvar y))
    (tapp_tm (tret vf) (vfvar y)) m Htyped Hsrc)
    as Htgt_insert.
  rewrite (ty_denote_gas_insert_fresh_lty_env_eq
    gas Σ τ (tapp_tm (tret vf) (vfvar y)) z
    (s →ₜ erase_ty τ)) in Htgt_insert.
  - exact Htgt_insert.
  - exact HzΣ.
  - intros Hbad. apply Hzfresh.
    apply lvars_fv_elem in Hbad.
    rewrite context_ty_lvars_fv in Hbad. set_solver.
  - rewrite fv_tapp_tm. cbn [fv_tm fv_value]. set_solver.
Qed.

Lemma ty_denote_gas_tapp_fun_result_alias_back_from_static
    gas (Σ : lty_env) τ vf y z s (m : WfWorldT) :
  LVFree z ∉ dom Σ ->
  z ∉ fv_value vf ∪ {[y]} ∪ fv_cty τ ->
  Σ !! LVFree y = Some s ->
  lc_value vf ->
  m ⊨ expr_result_formula (tret vf) (LVFree z) ->
  m ⊨ expr_basic_typing_formula Σ (tret vf) (s →ₜ erase_ty τ) ->
  m ⊨ ty_static_guard_formula Σ τ
    (tapp_tm (tret vf) (vfvar y)) ->
  m ⊨ ty_denote_gas gas
    (<[LVFree z := s →ₜ erase_ty τ]> Σ) τ
    (tapp_tm (tret (vfvar z)) (vfvar y)) ->
  m ⊨ ty_denote_gas gas Σ τ
    (tapp_tm (tret vf) (vfvar y)).
Proof.
  intros HzΣ Hzfresh Hy Hvf Hres Hbasic_fun Hstatic Hsrc.
  pose proof (ty_static_guard_context_wf _ _ _ _ Hstatic) as Hwf.
  pose proof (ty_static_guard_basic_world _ _ _ _ Hstatic) as Hworld.
  assert (Hstatic_src :
      m ⊨ ty_static_guard_formula
        (<[LVFree z := s →ₜ erase_ty τ]> Σ) τ
        (tapp_tm (tret (vfvar z)) (vfvar y))).
  {
    eapply ty_static_guard_tapp_fun_result_alias; eauto.
  }
  assert (Hclosed_tgt :
      wfworld_closed_on
        (fv_tm (tapp_tm (tret vf) (vfvar y))) m).
  {
    eapply ty_static_guard_wfworld_closed_on_term.
    exact Hstatic.
  }
  assert (Hclosed_src :
      wfworld_closed_on
        (fv_tm (tapp_tm (tret (vfvar z)) (vfvar y))) m).
  {
    eapply ty_static_guard_wfworld_closed_on_term.
    exact Hstatic_src.
  }
  assert (Hclosed :
      wfworld_closed_on
        (fv_tm (tapp_tm (tret (vfvar z)) (vfvar y)) ∪
         fv_tm (tapp_tm (tret vf) (vfvar y))) m).
  { apply wfworld_closed_on_union; assumption. }
  eapply ty_denote_gas_tapp_fun_result_alias_back; eauto.
Qed.

Lemma ty_denote_gas_tapp_fun_result_alias_from_static
    gas (Σ : lty_env) τ vf y z s (m : WfWorldT) :
  LVFree z ∉ dom Σ ->
  z ∉ fv_value vf ∪ {[y]} ∪ fv_cty τ ->
  Σ !! LVFree y = Some s ->
  lc_value vf ->
  m ⊨ expr_result_formula (tret vf) (LVFree z) ->
  m ⊨ expr_basic_typing_formula Σ (tret vf) (s →ₜ erase_ty τ) ->
  m ⊨ ty_static_guard_formula Σ τ
    (tapp_tm (tret vf) (vfvar y)) ->
  m ⊨ ty_denote_gas gas Σ τ
    (tapp_tm (tret vf) (vfvar y)) ->
  m ⊨ ty_denote_gas gas
    (<[LVFree z := s →ₜ erase_ty τ]> Σ) τ
    (tapp_tm (tret (vfvar z)) (vfvar y)).
Proof.
  intros HzΣ Hzfresh Hy Hvf Hres Hbasic_fun Hstatic Hsrc.
  pose proof Hstatic as Hstatic_src.
  pose proof (ty_static_guard_context_wf _ _ _ _ Hstatic) as Hwf.
  pose proof (ty_static_guard_basic_world _ _ _ _ Hstatic) as Hworld.
  assert (Hclosed_src :
      wfworld_closed_on
        (fv_tm (tapp_tm (tret vf) (vfvar y))) m).
  {
    eapply ty_static_guard_wfworld_closed_on_term.
    exact Hstatic_src.
  }
  assert (Hstatic_tgt :
      m ⊨ ty_static_guard_formula
        (<[LVFree z := s →ₜ erase_ty τ]> Σ) τ
        (tapp_tm (tret (vfvar z)) (vfvar y))).
  {
    eapply ty_static_guard_tapp_fun_result_alias; eauto.
  }
  assert (Hclosed_tgt :
      wfworld_closed_on
        (fv_tm (tapp_tm (tret (vfvar z)) (vfvar y))) m).
  {
    eapply ty_static_guard_wfworld_closed_on_term.
    exact Hstatic_tgt.
  }
  assert (Hclosed :
      wfworld_closed_on
        (fv_tm (tapp_tm (tret (vfvar z)) (vfvar y)) ∪
         fv_tm (tapp_tm (tret vf) (vfvar y))) m).
  { apply wfworld_closed_on_union; assumption. }
  eapply ty_denote_gas_tapp_fun_result_alias; eauto.
Qed.

Lemma ty_denote_gas_tapp_fun_arg_result_alias_from_static
    gas (Σ : lty_env) τ vf vx z w (m : WfWorldT) :
  LVFree z ∈ dom Σ ->
  LVFree w ∈ dom Σ ->
  lc_value vf ->
  lc_value vx ->
  m ⊨ expr_result_formula (tret vf) (LVFree z) ->
  m ⊨ expr_result_formula (tret vx) (LVFree w) ->
  m ⊨ ty_static_guard_formula Σ τ (tapp_tm (tret vf) vx) ->
  m ⊨ ty_denote_gas gas Σ τ
    (tapp_tm (tret (vfvar z)) (vfvar w)) ->
  m ⊨ ty_denote_gas gas Σ τ (tapp_tm (tret vf) vx).
Proof.
  intros HzΣ HwΣ Hvf Hvx Hfun Harg Hstatic Hsrc.
  assert (Hclosed :
      wfworld_closed_on
        (fv_tm (tapp_tm (tret (vfvar z)) (vfvar w)) ∪
         fv_tm (tapp_tm (tret vf) vx)) m).
  {
    pose proof (ty_static_guard_basic_world Σ τ
      (tapp_tm (tret vf) vx) m Hstatic) as Hworld.
    pose proof (basic_world_formula_wfworld_closed_on_dom
      Σ m Hworld) as Hclosed_dom.
    pose proof (ty_static_guard_wfworld_closed_on_term
      Σ τ (tapp_tm (tret vf) vx) m Hstatic) as Hclosed_tgt.
    eapply (wfworld_closed_on_mono
      (fv_tm (tapp_tm (tret (vfvar z)) (vfvar w)) ∪
       fv_tm (tapp_tm (tret vf) vx))
      (lvars_fv (dom Σ) ∪ fv_tm (tapp_tm (tret vf) vx))).
    - rewrite !fv_tapp_tm.
      change (fv_tm (tret (vfvar z))) with ({[z]} : aset).
      change (fv_value (vfvar w)) with ({[w]} : aset).
      intros a Ha.
      apply elem_of_union in Ha as [Ha|Ha].
      + apply elem_of_union_l.
        apply lvars_fv_elem.
        assert (a = z \/ a = w) as Hazw by set_solver.
        destruct Hazw as [Haz|Haw]; subst a; [exact HzΣ|exact HwΣ].
      + apply elem_of_union_r. exact Ha.
    - apply (wfworld_closed_on_union
        (lvars_fv (dom Σ))
        (fv_tm (tapp_tm (tret vf) vx))).
      + exact Hclosed_dom.
      + exact Hclosed_tgt.
  }
  pose proof (tm_equiv_tapp_value_fun_arg_result_alias
    m vf vx z w Hclosed Hvf Hvx Hfun Harg) as Hequiv.
  pose proof (tm_total_equiv_tapp_value_fun_arg_result_alias
    m vf vx z w Hclosed Hvf Hvx Hfun Harg) as Htotal.
  pose proof (ty_denote_gas_guard gas Σ τ
    (tapp_tm (tret (vfvar z)) (vfvar w)) m Hsrc) as Hguard_src.
  pose proof (ty_denote_gas_zero_of_guard Σ τ
    (tapp_tm (tret (vfvar z)) (vfvar w)) m Hguard_src) as Hzero_src.
  assert (Hzero_tgt :
      m ⊨ ty_denote_gas 0 Σ τ (tapp_tm (tret vf) vx)).
  {
    eapply ty_denote_gas_zero_transport_static_tm_equiv.
    - exact Hequiv.
    - exact Htotal.
    - exact Hstatic.
    - apply lc_tapp_tm; [constructor; exact Hvf|exact Hvx].
    - eapply ty_static_guard_fv_tm_subset. exact Hstatic.
    - exact Hzero_src.
  }
  assert (Htyped :
      typed_total_equiv_on Σ τ m
        (tapp_tm (tret (vfvar z)) (vfvar w))
        (tapp_tm (tret vf) vx)).
  {
    split; [exact Hequiv|].
    split; [exact Htotal|].
    split; [exact Hzero_src|exact Hzero_tgt].
  }
  eapply ty_denote_gas_tm_equiv; eauto.
Qed.

Local Lemma body_tret_bvar0 :
  body_tm (tret (vbvar 0)).
Proof.
  apply body_ret_iff_value.
  exists ∅. intros y _.
  cbn.
  constructor.
Qed.

Local Lemma tm_equiv_on_tlete_ret_bvar0
    (m : WfWorldT) e :
  tm_equiv_on m e (tlete e (tret (vbvar 0))).
Proof.
  intros σ v Hσ.
  unfold tm_eval_in_store, expr_eval_in_store.
  split.
  - intros He.
    cbn [lstore_instantiate_tm lstore_instantiate_tm_at
      lstore_instantiate_tm_split_at].
    eapply reduction_lete_intro.
    + apply body_tret_bvar0.
    + exact He.
    + apply Steps_refl.
      pose proof (steps_regular2 _ _ He) as Hret.
      exact Hret.
  - intros Hlet.
    cbn [lstore_instantiate_tm lstore_instantiate_tm_at
      lstore_instantiate_tm_split_at] in Hlet.
    apply reduction_lete in Hlet as [vx [He Hbody]].
    + cbn [lstore_instantiate_tm lstore_instantiate_tm_at
        lstore_instantiate_tm_split_at
        lstore_instantiate_value_at lstore_instantiate_value_split_at]
        in Hbody.
      pose proof (val_steps_self vx (tret v) Hbody) as Heq.
      inversion Heq; subst. exact He.
Qed.

Local Lemma tm_total_equiv_on_tlete_ret_bvar0
    (m : WfWorldT) e :
  tm_total_equiv_on m e (tlete e (tret (vbvar 0))).
Proof.
  intros σ Hσ.
  unfold lstore_instantiate_tm.
  split.
  - intros Htotal.
    cbn [lstore_instantiate_tm lstore_instantiate_tm_at
      lstore_instantiate_tm_split_at].
    eapply must_terminating_tlete_intro.
    + apply body_tret_bvar0.
    + exact Htotal.
    + intros vx Hsteps.
      cbn [lstore_instantiate_tm lstore_instantiate_tm_at
        lstore_instantiate_tm_split_at
        lstore_instantiate_value_at lstore_instantiate_value_split_at].
      change (must_terminating (tret vx)).
      apply must_terminating_tret.
      apply lc_ret_iff_value.
      eapply steps_regular2. exact Hsteps.
  - intros Htotal.
    cbn [lstore_instantiate_tm lstore_instantiate_tm_at
      lstore_instantiate_tm_split_at] in Htotal.
    eapply must_terminating_tlete_elim_e1. exact Htotal.
Qed.

Local Lemma expr_basic_typing_tlete_ret_bvar0
    (Σ : lty_env) τ e (m : WfWorldT) :
  m ⊨ expr_basic_typing_formula Σ e (erase_ty τ) ->
  m ⊨ expr_basic_typing_formula Σ
    (tlete e (tret (vbvar 0))) (erase_ty τ).
Proof.
  intros Hbasic.
  apply expr_basic_typing_formula_models_iff in Hbasic as [HlcΣ [Hsub Hty]].
  apply expr_basic_typing_formula_models_iff.
  split; [exact HlcΣ|].
  split.
  - cbn [fv_tm fv_value].
    exact Hsub.
  - eapply BTT_Let with (T1 := erase_ty τ) (L := lvars_fv (dom Σ)).
    + exact Hty.
    + intros y Hy.
      cbn.
      constructor. constructor.
      rewrite typed_lty_env_bind_open_current.
      * apply map_lookup_insert.
      * intros HyΣ. apply Hy.
        apply lvars_fv_elem. exact HyΣ.
      * exact HlcΣ.
Qed.

Local Lemma relevant_env_tlete_ret_bvar0
    (Σ : lty_env) τ e :
  lc_tm e ->
  relevant_env Σ τ (tlete e (tret (vbvar 0))) =
  relevant_env Σ τ e.
Proof.
  intros Hlc.
  unfold relevant_env, lty_env_restrict_lvars, relevant_lvars.
  f_equal.
  rewrite (tm_lvars_lc_eq_atoms e Hlc).
  rewrite (tm_lvars_lc_eq_atoms (tlete e (tret (vbvar 0)))).
  - cbn [fv_tm fv_value].
    set_solver.
  - apply lc_lete_iff_body. split; [exact Hlc|apply body_tret_bvar0].
Qed.

Lemma ty_denote_gas_result_alias_at
    gas (Σ : lty_env) τ e x D (m : WfWorldT) :
  lty_env_closed Σ ->
  lc_lvars D ->
  tm_lvars e ⊆ D ->
  context_ty_lvars τ ⊆ D ->
  LVFree x ∉ D ->
  lvars_fv D ⊆ world_dom (m : WorldT) ->
  Σ !! LVFree x = Some (erase_ty τ) ->
  m ⊨ expr_result_formula_at D e (LVFree x) ->
  m ⊨ ty_denote_gas gas Σ τ e ->
  m ⊨ ty_denote_gas gas Σ τ (tret (vfvar x)).
Proof.
  intros HΣclosed HlcD HeD HτD HxD HDm Hlookup Hres Hsource.
  pose proof (ty_denote_gas_guard gas Σ τ e m Hsource) as Hguard_full.
  pose proof Hguard_full as Hguard_parts.
  repeat rewrite res_models_and_iff in Hguard_parts.
  destruct Hguard_parts as [Hwf [Hworld [Hbasic Htotal]]].
  assert (Hxτ : x ∉ fv_cty τ).
  {
    intros Hxτ.
    apply HxD. apply HτD.
    apply lvars_fv_elem. rewrite context_ty_lvars_fv. exact Hxτ.
  }
  assert (Hxe : x ∉ fv_tm e).
  {
    intros Hxe.
    apply HxD. apply HeD.
    apply lvars_fv_elem. rewrite tm_lvars_fv. exact Hxe.
  }
  assert (Hlc_e : lc_tm e).
  {
    apply expr_basic_typing_formula_models_iff in Hbasic as [HlcΣ [_ Hty]].
    eapply basic_tm_has_ltype_lc; [exact HlcΣ|exact Hty].
  }
  assert (Hres_small : m ⊨ expr_result_formula e (LVFree x)).
  {
    unfold expr_result_formula.
    eapply expr_result_formula_at_coarsen_domain.
    - exact HeD.
    - intros v Hv. exact Hv.
    - exact HxD.
    - exact Hres.
  }
  set (Σg := relevant_env Σ τ e).
  set (Σx := Σ).
  assert (Hguard_ret :
      m ⊨ ty_guard_formula (relevant_env Σ τ (tret (vfvar x)))
        τ (tret (vfvar x))).
  {
    assert (Hworld_ret :
        m ⊨ basic_world_formula (relevant_env Σ τ (tret (vfvar x)))).
    {
      eapply basic_world_formula_subenv
        with (Σbig := <[LVFree x := erase_ty τ]> (relevant_env Σ τ e)).
      - intros v T Hv.
        unfold relevant_env, lty_env_restrict_lvars in Hv |- *.
	        apply storeA_restrict_lookup_some in Hv as [Hvrel Hv].
	        destruct (decide (v = LVFree x)) as [->|Hvx].
	        + change ((Σ : gmap logic_var ty) !! LVFree x = Some T) in Hv.
	          rewrite Hlookup in Hv. inversion Hv. subst T.
	          apply map_lookup_insert.
        + rewrite lookup_insert_ne by congruence.
          apply (storeA_restrict_lookup_some_2 _ _ _ _ Hv).
          unfold relevant_lvars in Hvrel |- *.
          apply elem_of_union in Hvrel as [Hvτ|Hvxv].
          * apply elem_of_union_l. exact Hvτ.
          * cbn [tm_lvars tm_lvars_at value_lvars_at lvar_value_keys] in Hvxv.
            apply elem_of_singleton in Hvxv. contradiction.
      - eapply basic_world_insert_result_alias.
        + apply relevant_env_fresh_free.
          * exact Hxτ.
          * exact Hxe.
        + exact Hres_small.
        + exact Hworld.
        + exact Hbasic.
    }
    assert (Hbasic_ret :
        m ⊨ expr_basic_typing_formula
          (relevant_env Σ τ (tret (vfvar x)))
          (tret (vfvar x)) (erase_ty τ)).
    {
      pose proof Hworld_ret as Hworld_ret_parts.
      apply basic_world_formula_models_iff in Hworld_ret_parts
        as [Hlc_ret [Hscope_ret _]].
      eapply ret_fvar_typing_of_lookup.
      - exact Hlc_ret.
      - exact Hscope_ret.
      - unfold relevant_env, lty_env_restrict_lvars.
        apply storeA_restrict_lookup_some_2.
        + exact Hlookup.
        + unfold relevant_lvars.
          apply elem_of_union_r.
          cbn [tm_lvars tm_lvars_at value_lvars_at lvar_value_keys].
          apply elem_of_singleton. reflexivity.
    }
    unfold ty_guard_formula.
    repeat rewrite res_models_and_iff.
    split.
    - eapply context_ty_wf_formula_relevant_env_change_term.
      + exact Hworld_ret.
      + exact Hwf.
    - split; [exact Hworld_ret|].
      split; [exact Hbasic_ret|].
      eapply expr_total_formula_tret_of_basic.
      + exact Hworld_ret.
      + exact Hbasic_ret.
  }
  assert (Hzero_ret :
      m ⊨ ty_denote_gas 0 Σ τ (tret (vfvar x))).
  { eapply ty_denote_gas_zero_of_guard_formula. exact Hguard_ret. }
  assert (Hguard_source :
      m ⊨ ty_guard_formula (relevant_env Σ τ e) τ e).
  { exact Hguard_full. }
  assert (Hzero_source :
      m ⊨ ty_denote_gas 0 Σ τ e).
  { eapply ty_denote_gas_zero_of_guard_formula. exact Hguard_source. }
  assert (Hzero_tlet :
      m ⊨ ty_denote_gas 0 Σ τ (tlete e (tret (vbvar 0)))).
  {
    eapply ty_denote_gas_zero_of_guard_formula.
    unfold ty_guard_formula.
    rewrite relevant_env_tlete_ret_bvar0 by exact Hlc_e.
    repeat rewrite res_models_and_iff.
    split; [exact Hwf|].
    split; [exact Hworld|].
    split.
    - eapply expr_basic_typing_tlete_ret_bvar0. exact Hbasic.
    - eapply tm_equiv_total.
      + apply tm_total_equiv_on_tlete_ret_bvar0.
      + apply lc_lete_iff_body. split; [exact Hlc_e|apply body_tret_bvar0].
      + cbn [fv_tm fv_value].
        apply expr_basic_typing_formula_models_iff in Hbasic
          as [_ [_ Hty_src]].
        pose proof (basic_tm_has_ltype_lvars _ _ _ Hty_src) as Hfv_lvars.
        apply basic_world_formula_models_iff in Hworld
          as [_ [Hdom_m _]].
        intros a Ha.
        apply Hdom_m.
        apply lvars_fv_elem.
        apply Hfv_lvars.
        unfold lvars_of_atoms.
        apply elem_of_map. exists a. split; [reflexivity|set_solver].
      + exact Htotal.
  }
  assert (Htlet :
      m ⊨ ty_denote_gas gas Σ τ (tlete e (tret (vbvar 0)))).
  {
    eapply ty_denote_gas_tm_equiv.
    - split.
      + apply tm_equiv_on_tlete_ret_bvar0.
      + split.
        * apply tm_total_equiv_on_tlete_ret_bvar0.
        * split; [exact Hzero_source|exact Hzero_tlet].
    - exact Hsource.
  }
  assert (Hclosed_base :
      wfworld_closed_on (fv_tm e)
        (res_restrict m (world_dom (m : WorldT) ∖ {[x]}))).
	  {
	    eapply wfworld_closed_on_restrict.
	    - intros a Ha.
	      assert (a ∈ world_dom (m : WorldT)).
	      { eapply ty_denote_gas_fv_tm_subset; [exact Hsource|exact Ha]. }
	      assert (a <> x) by (intros ->; exact (Hxe Ha)).
	      set_solver.
    - eapply basic_world_formula_wfworld_closed_on_atoms.
      + apply expr_basic_typing_formula_models_iff in Hbasic as [_ [_ Hty]].
        eapply basic_tm_has_ltype_lvars. exact Hty.
      + exact Hworld.
  }
  assert (Htotal_base :
      expr_total_on_atom_world e
        (res_restrict m (world_dom (m : WorldT) ∖ {[x]}))).
  {
    assert (Hfv_total :
        formula_fv (expr_total_formula e) ⊆
          world_dom (m : WorldT) ∖ {[x]}).
    {
      rewrite formula_fv_expr_total_formula, tm_lvars_fv.
      intros a Ha.
      assert (a ∈ world_dom (m : WorldT)).
      { eapply ty_denote_gas_fv_tm_subset; [exact Hsource|exact Ha]. }
      assert (a <> x) by (intros ->; exact (Hxe Ha)).
      set_solver.
    }
    eapply expr_total_formula_to_atom_world.
    exact (proj1 (res_models_minimal_on
      (world_dom (m : WorldT) ∖ {[x]}) m
      (expr_total_formula e) Hfv_total) Htotal).
  }
  eapply result_graph_tlet_reverse_transport
    with (D := D) (e1 := e) (e2 := tret (vbvar 0)).
  - exact HlcD.
  - exact HeD.
  - exact HxD.
  - exact HDm.
  - cbn [fv_tm fv_value]. set_solver.
  - exact Hxτ.
  - pose proof (ty_denote_gas_fv_subset
      0 Σ τ (tret (vfvar x))) as Hfv.
    intros a Ha. pose proof (Hfv _ Ha) as Hrel.
    apply elem_of_union in Hrel as [Hret|Hτrel].
    + cbn [fv_tm fv_value] in Hret. set_solver.
    + apply elem_of_union_l.
      apply lvars_fv_elem. apply HτD.
      apply lvars_fv_elem. rewrite context_ty_lvars_fv. exact Hτrel.
  - pose proof (ty_denote_gas_fv_subset
      0 Σ τ (tlete e (tret (vbvar 0)))) as Hfv.
    intros a Ha. pose proof (Hfv _ Ha) as Hrel.
    apply elem_of_union in Hrel as [Htletfv|Hτrel].
    + cbn [fv_tm fv_value] in Htletfv.
      apply elem_of_union_l.
      apply lvars_fv_elem. apply HeD.
      apply lvars_fv_elem. rewrite tm_lvars_fv. set_solver.
    + apply elem_of_union_l.
      apply lvars_fv_elem. apply HτD.
      apply lvars_fv_elem. rewrite context_ty_lvars_fv. exact Hτrel.
  - pose proof (ty_denote_gas_fv_subset
      gas Σ τ (tret (vfvar x))) as Hfv.
    intros a Ha. pose proof (Hfv _ Ha) as Hrel.
    apply elem_of_union in Hrel as [Hret|Hτrel].
    + cbn [fv_tm fv_value] in Hret. set_solver.
    + apply elem_of_union_l.
      apply lvars_fv_elem. apply HτD.
      apply lvars_fv_elem. rewrite context_ty_lvars_fv. exact Hτrel.
  - pose proof (ty_denote_gas_fv_subset
      gas Σ τ (tlete e (tret (vbvar 0)))) as Hfv.
    intros a Ha. pose proof (Hfv _ Ha) as Hrel.
    apply elem_of_union in Hrel as [Htletfv|Hτrel].
    + cbn [fv_tm fv_value] in Htletfv.
      apply elem_of_union_l.
      apply lvars_fv_elem. apply HeD.
      apply lvars_fv_elem. rewrite tm_lvars_fv. set_solver.
    + apply elem_of_union_l.
      apply lvars_fv_elem. apply HτD.
      apply lvars_fv_elem. rewrite context_ty_lvars_fv. exact Hτrel.
  - exact Hlc_e.
  - exact Hres.
  - exact Hclosed_base.
  - exact Htotal_base.
  - exact Hzero_ret.
  - exact Hzero_tlet.
  - exact Htlet.
Qed.

Lemma ty_denote_gas_result_ext
    gas (Σ : lty_env) τ e x
    (m mx : WfWorldT) (Fx : FiberExtensionT) :
  lty_env_closed Σ ->
  LVFree x ∉ dom Σ ->
  expr_result_extension_witness e x Fx ->
  res_extend_by m Fx mx ->
  m ⊨ ty_denote_gas gas Σ τ e ->
  mx ⊨ ty_denote_gas gas
    (<[LVFree x := erase_ty τ]> Σ) τ (tret (vfvar x)).
Proof.
  intros HΣclosed HxΣ HFx Hext Hm.
  pose proof (ty_denote_gas_guard gas Σ τ e m Hm) as Hguard_full.
  pose proof Hguard_full as Hguard_parts.
  repeat rewrite res_models_and_iff in Hguard_parts.
  destruct Hguard_parts as [Hwf [Hworld [Hbasic Htotal]]].
  assert (Hxτ : LVFree x ∉ context_ty_lvars τ).
  {
    intros Hbad.
    apply context_ty_wf_formula_models_iff in Hwf as [_ [_ Hbasicτ]].
    destruct Hbasicτ as [Hτdom _].
    apply HxΣ.
    eapply relevant_env_dom_subset_direct.
    eapply Hτdom. exact Hbad.
  }
  assert (Hxe : x ∉ fv_tm e).
  { exact (expr_result_extension_witness_fresh _ _ _ HFx). }
  assert (HFx_ltype :
      extension_has_ltype (<[LVFree x := erase_ty τ]> ∅)
        (res_restrict m (ext_in Fx)) Fx).
  {
    eapply result_ext_typed_of_guard
      with (Σ := relevant_env Σ τ e) (τ := τ);
      [apply relevant_env_closed; exact HΣclosed| |exact HFx|exact Hext|].
    - intros Hxrel. apply HxΣ.
      eapply relevant_env_dom_subset_direct. exact Hxrel.
    - exact Hguard_full.
  }
  pose proof (ty_denote_gas_extend_typed_extension
    gas Σ τ e x (erase_ty τ) m mx Fx
    HxΣ Hxτ Hxe HFx_ltype Hext Hm) as Hmx_source.
  set (Σx := <[LVFree x := erase_ty τ]> Σ).
  assert (Hzero_m : m ⊨ ty_denote_gas 0 Σ τ e).
  {
    apply ty_denote_gas_zero_of_guard.
    eapply ty_denote_gas_guard. exact Hm.
  }
  assert (HlcD :
      lc_lvars (context_ty_lvars τ ∪ tm_lvars e)).
  { eapply ty_denote_gas_zero_lc_relevant_lvars. exact Hzero_m. }
  assert (Hlc_e : lc_tm e).
  {
    apply expr_basic_typing_formula_models_iff in Hbasic as [HlcΣ [_ Hty]].
    eapply basic_tm_has_ltype_lc; [exact HlcΣ|exact Hty].
  }
  assert (Hres_at :
      mx ⊨ expr_result_formula_at
        (context_ty_lvars τ ∪ tm_lvars e) e (LVFree x)).
  {
    eapply expr_result_formula_at_of_result_extends
      with (D := context_ty_lvars τ) (m := m) (F := Fx).
    - intros v Hv. apply HlcD. set_solver.
    - exact Hlc_e.
    - intros a Ha.
      eapply ty_denote_gas_zero_relevant_lvars_world; [exact Hzero_m|].
      rewrite lvars_fv_union. apply elem_of_union_l. exact Ha.
    - intros a Ha.
      eapply ty_denote_gas_zero_relevant_lvars_world; [exact Hzero_m|].
      rewrite lvars_fv_union. apply elem_of_union_r.
      rewrite tm_lvars_fv. exact Ha.
    - intros Hbad.
      apply elem_of_union in Hbad as [Hbad|Hbad].
      + apply Hxτ. apply lvars_fv_elem. exact Hbad.
      + exact (Hxe Hbad).
    - exact HFx.
    - exact Hext.
    - eapply expr_total_formula_to_atom_world. exact Htotal.
    - assert (Hfv_e :
          lvars_of_atoms (fv_tm e) ⊆ dom (relevant_env Σ τ e)).
      {
        apply expr_basic_typing_formula_models_iff in Hbasic as [_ [_ Hty]].
        eapply basic_tm_has_ltype_lvars. exact Hty.
      }
      eapply basic_world_formula_wfworld_closed_on_atoms;
        [exact Hfv_e|exact Hworld].
  }
  eapply (ty_denote_gas_result_alias_at gas Σx τ e x
    (context_ty_lvars τ ∪ tm_lvars e) mx).
  - subst Σx. apply lty_env_closed_insert_free. exact HΣclosed.
  - eapply ty_denote_gas_zero_lc_relevant_lvars.
    subst Σx. apply ty_denote_gas_zero_of_guard.
    eapply ty_denote_gas_guard. exact Hmx_source.
  - set_solver.
  - set_solver.
	  - intros Hbad.
	    apply elem_of_union in Hbad as [Hbad|Hbad].
	    + exact (Hxτ Hbad).
	    + apply Hxe. rewrite <- tm_lvars_fv.
	      apply lvars_fv_elem. exact Hbad.
  - eapply ty_denote_gas_zero_relevant_lvars_world.
    subst Σx. apply ty_denote_gas_zero_of_guard.
    eapply ty_denote_gas_guard. exact Hmx_source.
  - subst Σx. rewrite lookup_insert.
    destruct (decide (LVFree x = LVFree x)) as [_|Hneq];
      [reflexivity|contradiction].
  - exact Hres_at.
  - exact Hmx_source.
Qed.

Lemma formula_fv_ty_denote_gas_subset_relevant gas Σ τ e :
  formula_fv (ty_denote_gas gas Σ τ e) ⊆
  fv_tm e ∪ fv_cty τ.
Proof.
  apply ty_denote_gas_fv_subset.
Qed.

Lemma ty_denote_gas_restrict_ret_fvar_closed
    gas (Σ : lty_env) τ x (m : WfWorldT) :
  wf_context_ty_at 0 ∅ τ ->
  m ⊨ ty_denote_gas gas Σ τ (tret (vfvar x)) ->
  res_restrict m ({[x]} : aset) ⊨
    ty_denote_gas gas Σ τ (tret (vfvar x)).
Proof.
  intros Hτ_closed Hden.
  assert (Hfv :
      formula_fv (ty_denote_gas gas Σ τ (tret (vfvar x))) ⊆ {[x]}).
  {
    pose proof (ty_denote_gas_fv_subset
      gas Σ τ (tret (vfvar x))) as Hrel.
    pose proof (wf_context_ty_at_fv_subset 0 ∅ τ Hτ_closed) as Hτ_fv.
    intros y Hy.
    pose proof (Hrel y Hy) as Hyrel.
    support_lvars_norm_in Hyrel.
    better_set_solver.
  }
  exact (proj1 (res_models_minimal_on ({[x]} : aset) m
    (ty_denote_gas gas Σ τ (tret (vfvar x))) Hfv) Hden).
Qed.

Lemma ty_denote_gas_restrict_delete_fresh
    gas (Σ : lty_env) τ e x (m : WfWorldT) :
  x ∉ fv_tm e ∪ fv_cty τ ->
  m ⊨ ty_denote_gas gas Σ τ e ->
  res_restrict m (world_dom (m : WorldT) ∖ {[x]}) ⊨
    ty_denote_gas gas Σ τ e.
Proof.
  intros Hfresh Hden.
  assert (Hfv_drop :
      formula_fv (ty_denote_gas gas Σ τ e) ⊆
      world_dom (m : WorldT) ∖ {[x]}).
  {
    pose proof (res_models_scoped _ _ Hden) as Hscope.
    pose proof (ty_denote_gas_fv_subset gas Σ τ e) as Hfv.
    intros z Hz.
    pose proof (Hscope z Hz) as Hzdom.
    pose proof (Hfv z Hz) as Hzrel.
    apply elem_of_difference. split; [exact Hzdom|].
    intros Hzx.
    apply elem_of_singleton in Hzx. subst z.
    exact (Hfresh Hzrel).
  }
  exact (proj1 (res_models_minimal_on
    (world_dom (m : WorldT) ∖ {[x]}) m
    (ty_denote_gas gas Σ τ e) Hfv_drop) Hden).
Qed.

Lemma ty_denote_ret_fvar_base_const
    gas Σ τ b x (m : WfWorldT) :
  erase_ty τ = TBase b ->
  m ⊨ ty_denote_gas gas Σ τ (tret (vfvar x)) ->
  forall σ,
    (m : WorldT) σ ->
    exists c,
      σ !! x = Some (vconst c) /\
      base_ty_of_const c = b.
Proof.
  intros Hτ Hden σ Hσ.
  pose proof (ty_denote_gas_guard gas Σ τ (tret (vfvar x)) m Hden)
    as Hguard.
  repeat rewrite res_models_and_iff in Hguard.
  destruct Hguard as [_ [Hworld [Hbasic _]]].
  pose proof Hbasic as Hbasic_lookup.
  apply expr_basic_typing_formula_models_iff in Hbasic_lookup
    as [_ [_ Hty_lookup]].
  apply basic_tm_has_ltype_ret_fvar_lookup in Hty_lookup
    as HΣx_rel.
  pose proof (ty_denote_gas_ret_fvar_world_dom
    gas Σ τ x m Hden) as Hx_dom.
  pose proof (wfworld_store_dom m σ Hσ) as Hdomσ.
  assert (Hxσdom : x ∈ dom (σ : StoreT)).
  { better_set_solver. }
  change (x ∈ dom (σ : gmap atom value)) in Hxσdom.
  apply elem_of_dom in Hxσdom as [v Hσx].
  apply basic_world_formula_models_iff in Hworld as [_ [_ Htyped]].
  unfold lworld_has_type, worldA_has_type in Htyped.
  destruct Htyped as [_ Hstores].
  specialize (Hstores (lstore_lift_free σ)
    ltac:(exists σ; split; [exact Hσ|reflexivity])).
  assert (Hlookup_lift :
      (lstore_lift_free σ : LStoreT) !! LVFree x = Some v).
  { rewrite lstore_lift_free_lookup_free. exact Hσx. }
  pose proof (Hstores (LVFree x) (erase_ty τ) v HΣx_rel Hlookup_lift)
    as HvT.
  rewrite Hτ in HvT.
  apply empty_basic_value_base_inv in HvT as [c [Hv Hc]].
  exists c.
  split; [|exact Hc].
  subst v. exact Hσx.
Qed.

Lemma ty_denote_gas_drop_fresh_ext
    gas (Σ : lty_env) τ e x T (m mx : WfWorldT) Fx :
  fv_tm e ∪ fv_cty τ ⊆ world_dom (m : WorldT) ->
  LVFree x ∉ dom Σ ->
  LVFree x ∉ context_ty_lvars τ ->
  x ∉ fv_tm e ->
  res_extend_by m Fx mx ->
  mx ⊨ ty_denote_gas gas (<[LVFree x := T]> Σ) τ e ->
  m ⊨ ty_denote_gas gas Σ τ e.
Proof.
  intros Hfv_world HxΣ Hxτ Hxe Hext Hmx.
  rewrite (ty_denote_gas_insert_fresh_lty_env_eq
    gas Σ τ e x T HxΣ Hxτ Hxe) in Hmx.
  eapply res_models_from_restrict_extension_on_fv
    with (X := fv_tm e ∪ fv_cty τ) (n := mx).
  - apply ty_denote_gas_fv_subset.
  - transitivity (fv_tm e ∪ fv_cty τ).
    + apply ty_denote_gas_fv_subset.
    + exact Hfv_world.
  - transitivity m.
    + apply res_restrict_le.
    + eapply res_extend_by_le; eauto.
  - exact Hmx.
Qed.

Lemma expr_result_formula_of_result_extends_from_ty_guard
    (Σ : lty_env) τ e x (m mx : WfWorldT) Fx :
  expr_result_extension_witness e x Fx ->
  res_extend_by m Fx mx ->
  m ⊨ ty_guard_formula Σ τ e ->
  mx ⊨ expr_result_formula e (LVFree x).
Proof.
  intros HF Hext Hguard.
  unfold ty_guard_formula in Hguard.
  repeat rewrite res_models_and_iff in Hguard.
  destruct Hguard as [_ [Hworld [Hbasic Htotal]]].
  apply expr_basic_typing_formula_models_iff in Hbasic
    as [HlcΣ [_ Hty]].
  pose proof (basic_tm_has_ltype_lc Σ e (erase_ty τ) HlcΣ Hty) as Hlc_e.
  pose proof (basic_tm_has_ltype_lvars Σ e (erase_ty τ) Hty) as He_lvars.
  pose proof (basic_world_formula_models_iff Σ m) as Hworld_iff.
  apply Hworld_iff in Hworld as [_ [HΣdom _]].
  unfold expr_result_formula.
  eapply expr_result_formula_at_of_result_extends_on.
  - rewrite (tm_lvars_lc_eq_atoms e Hlc_e). unfold lvars_of_atoms.
    intros z Hz. apply elem_of_map in Hz as [a [-> _]]. exact I.
  - reflexivity.
  - intros Hx_lvars.
    apply (expr_result_extension_witness_fresh _ _ _ HF).
    rewrite <- tm_lvars_fv. apply lvars_fv_elem. exact Hx_lvars.
  - rewrite tm_lvars_fv.
    intros a Ha.
    apply HΣdom.
    apply lvars_fv_elem.
    apply He_lvars.
    unfold lvars_of_atoms. apply elem_of_map.
    exists a. split; [reflexivity|exact Ha].
  - rewrite tm_lvars_fv.
    apply expr_result_extension_witness_to_on. exact HF.
  - exact Hext.
  - eapply expr_total_formula_to_atom_world. exact Htotal.
Qed.

Lemma expr_result_formula_at_env_of_result_extends_from_ty_guard_on
    (Σ : lty_env) τ e x (m mx : WfWorldT) Fx :
  expr_result_extension_witness_on (world_dom (m : WorldT)) e x Fx ->
  res_extend_by m Fx mx ->
  m ⊨ ty_guard_formula Σ τ e ->
  mx ⊨ expr_result_formula_at (dom Σ) e (LVFree x).
Proof.
  intros HF Hext Hguard.
  unfold ty_guard_formula in Hguard.
  repeat rewrite res_models_and_iff in Hguard.
  destruct Hguard as [_ [Hworld [Hbasic Htotal]]].
  apply expr_basic_typing_formula_models_iff in Hbasic
    as [HlcΣ [_ Hty]].
  pose proof (basic_tm_has_ltype_lc Σ e (erase_ty τ) HlcΣ Hty) as Hlc_e.
  pose proof (basic_tm_has_ltype_lvars Σ e (erase_ty τ) Hty) as He_lvars.
  apply basic_world_formula_models_iff in Hworld as [HlcΣdom [HΣdom _]].
  eapply expr_result_formula_at_of_result_extends_on_coarsen
    with (X := world_dom (m : WorldT)) (F := Fx) (m := m).
  - exact HlcΣdom.
  - rewrite (tm_lvars_lc_eq_atoms e Hlc_e).
    exact He_lvars.
  - unfold lvars_of_atoms.
    intros v Hv.
    destruct v as [k|a].
    + exfalso. exact (HlcΣdom (LVBound k) Hv).
    + apply elem_of_map. exists a. split; [reflexivity|].
      apply HΣdom. apply lvars_fv_elem. exact Hv.
  - unfold lvars_of_atoms.
    intros Hx.
    apply elem_of_map in Hx as [a [Ha HaD]].
    inversion Ha. subst a.
    apply (expr_result_extension_witness_on_fresh _ _ _ _ HF).
    exact HaD.
  - set_solver.
  - exact HF.
  - exact Hext.
  - eapply expr_total_formula_to_atom_world. exact Htotal.
Qed.

Lemma expr_result_formula_of_result_extends_on_from_ty_guard
    (Σ : lty_env) τ e x (m mx : WfWorldT) Fx :
  expr_result_extension_witness_on (world_dom (m : WorldT)) e x Fx ->
  res_extend_by m Fx mx ->
  m ⊨ ty_guard_formula Σ τ e ->
  mx ⊨ expr_result_formula e (LVFree x).
Proof.
  intros HF Hext Hguard.
  unfold expr_result_formula.
  unfold ty_guard_formula in Hguard.
  repeat rewrite res_models_and_iff in Hguard.
  destruct Hguard as [_ [Hworld [Hbasic Htotal]]].
  apply expr_basic_typing_formula_models_iff in Hbasic
    as [HlcΣ [_ Hty]].
  pose proof (basic_tm_has_ltype_lc Σ e (erase_ty τ) HlcΣ Hty) as Hlc_e.
  pose proof (basic_tm_has_ltype_lvars Σ e (erase_ty τ) Hty) as He_lvars.
  apply basic_world_formula_models_iff in Hworld as [_ [HΣdom _]].
  eapply expr_result_formula_at_of_result_extends_on_coarsen
    with (X := world_dom (m : WorldT)) (F := Fx) (m := m).
  - rewrite (tm_lvars_lc_eq_atoms e Hlc_e).
    unfold lvars_of_atoms.
    intros v Hv.
    apply elem_of_map in Hv as [a [-> _]].
    exact I.
  - reflexivity.
  - rewrite (tm_lvars_lc_eq_atoms e Hlc_e).
    unfold lvars_of_atoms.
    intros v Hv.
    apply elem_of_map in Hv as [a [-> Ha]].
    apply elem_of_map. exists a. split; [reflexivity|].
    apply HΣdom. apply lvars_fv_elem.
    apply He_lvars.
    unfold lvars_of_atoms. apply elem_of_map.
    exists a. split; [reflexivity|exact Ha].
  - unfold lvars_of_atoms.
    intros Hx.
    apply elem_of_map in Hx as [a [Ha HaD]].
    inversion Ha. subst a.
    apply (expr_result_extension_witness_on_fresh _ _ _ _ HF).
    exact HaD.
  - set_solver.
  - exact HF.
  - exact Hext.
  - eapply expr_total_formula_to_atom_world. exact Htotal.
Qed.

Lemma denot_ty_lvar_guard_wfworld_closed_on_term
    (Σ : lty_env) τ e (m : WfWorldT) :
  m ⊨ ty_guard_formula Σ τ e ->
  wfworld_closed_on (fv_tm e) m.
Proof.
  intros Hguard.
  unfold ty_guard_formula in Hguard.
  repeat rewrite res_models_and_iff in Hguard.
  destruct Hguard as [_ [Hworld [Hbasic _]]].
  apply expr_basic_typing_formula_models_iff in Hbasic as [_ [_ Hty]].
  eapply basic_world_formula_wfworld_closed_on_atoms;
    [eapply basic_tm_has_ltype_lvars; exact Hty|exact Hworld].
Qed.

Lemma lam_intro_denotation
    gas (Σ : lty_env) τ T e y (m : WfWorldT) :
  wfworld_closed_on
    (fv_tm (tapp_tm (tret (vlam T e)) (vfvar y)) ∪ fv_tm (e ^^ y)) m ->
  body_tm e ->
  y ∉ fv_tm e ->
  y ∈ world_dom (m : WorldT) ->
  m ⊨ ty_denote_gas 0 Σ τ (e ^^ y) ->
  m ⊨ ty_denote_gas 0 Σ τ
    (tapp_tm (tret (vlam T e)) (vfvar y)) ->
  m ⊨ ty_denote_gas gas Σ τ (e ^^ y) ->
  m ⊨ ty_denote_gas gas Σ τ
    (tapp_tm (tret (vlam T e)) (vfvar y)).
Proof.
  intros Hclosed Hbody Hy_fresh Hy_dom Hzero_body Hzero_app Hbody_den.
  pose proof (ty_denote_gas_guard_of_zero
    Σ τ (e ^^ y) m Hzero_body) as Hguard_body.
  pose proof (ty_denote_gas_guard_of_zero
    Σ τ (tapp_tm (tret (vlam T e)) (vfvar y)) m Hzero_app) as Hguard_app.
  pose proof Hguard_body as Hguard_body_parts.
  pose proof Hguard_app as Hguard_app_parts.
  repeat rewrite res_models_and_iff in Hguard_body_parts.
  repeat rewrite res_models_and_iff in Hguard_app_parts.
  destruct Hguard_body_parts as [_ [_ [_ Htotal_body]]].
  destruct Hguard_app_parts as [_ [_ [_ Htotal_app]]].
  eapply ty_denote_gas_tm_equiv.
  - split.
    + intros σ v Hσ.
      pose proof (tm_equiv_lam_app_body T e y m
        Hclosed Hbody Hy_fresh Hy_dom σ v Hσ) as [Happ_body Hbody_app].
      split; [exact Hbody_app|exact Happ_body].
	    + split.
	      * eapply tm_total_equiv_of_total_formulas; eauto.
	      * split.
	        -- exact Hzero_body.
	        -- exact Hzero_app.
  - exact Hbody_den.
Qed.


End TypeDenote.
