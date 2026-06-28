(** * ContextTyping.SoundnessFix

    Fix proof support for the direct Fundamental theorem.  The outer Arrow
    proof mirrors [SoundnessLam]; the opened-result helper is where the
    well-founded induction over the current argument constant lives. *)

From Stdlib Require Import Lia.
From CoreLang Require Import BasicTyping BasicTypingProps InstantiationProps
  SmallStep StrongNormalization.
From ContextStore Require Import Store.
From ContextAlgebra Require Import ResourceInterface ResourceExtension.
From ContextBasicDenotation Require Import StoreTyping TermExtension TermTLet Qualifier
  BasicTypingFormula RelevantEnv.
From Denotation Require Import Context
  DenotationSetMapFacts
  TypeEquivCore
  TypeEquivTermBase TypeEquivTermResult
  TypeEquivFiberBaseCore TypeEquivFiberBaseProjected
  TypeEquivBody
  TypeEquivArrow
  TypeEquivWand
  TypeEquiv
  ConstDenote.
From ContextTyping Require Import Typing TypingRegular SoundnessLam.

Local Notation LStoreOnT := (LStoreOn (V := value)) (only parsing).

Ltac fix_union_member :=
  first
    [ assumption
    | apply elem_of_union_l; fix_union_member
    | apply elem_of_union_r; fix_union_member
    | apply elem_of_singleton_2; reflexivity ].

Ltac fix_break_union H :=
  repeat match type of H with
  | _ ∈ _ ∪ _ => apply elem_of_union in H as [H | H]
  | _ ∈ {[ _ ]} => apply elem_of_singleton in H; subst
  end.

Ltac fix_notin_union :=
  let Hbad := fresh "Hbad" in
  intros Hbad;
  fix_break_union Hbad;
  match type of Hbad with
  | ?x ∈ _ =>
    match goal with
    | H : x ∉ _ |- False =>
      apply H; fix_union_member
    end
  end.

Ltac fix_singleton_side :=
  cbn [fv_tm fv_value] in *;
  repeat match goal with
  | H : ?a ∈ {[?b]} |- _ =>
      apply elem_of_singleton in H; subst
  end;
  repeat match goal with
  | |- ?a ∈ {[?a]} => apply elem_of_singleton; reflexivity
  end.

Lemma ty_denote_lt_arg_fiber
    gas (Δ : lty_env) b x y (m : WfWorldT) :
  x <> y ->
  lty_env_closed Δ ->
  m ⊨ ty_denote_gas (S gas) Δ
        (over_ty b (mk_q_lt_base b (vbvar 0) (vfvar y)))
        (tret (vfvar x)) ->
  forall σ, (m : WorldT) σ ->
    exists cx cy,
      σ !! x = Some (vconst cx) /\
      σ !! y = Some (vconst cy) /\
      constant_lt_for_base b cx cy.
Proof.
  intros Hxy HΔclosed Hden σ Hσ.
  set (τlt := over_ty b (mk_q_lt_base b (vbvar 0) (vfvar y))) in *.
  pose proof (ty_denote_gas_guard _ _ _ _ _ Hden) as Hguard.
  pose proof Hguard as Hguard_parts.
  repeat rewrite res_models_and_iff in Hguard_parts.
  destruct Hguard_parts as [_ [Hworld [Hbasic Htotal]]].
  assert (Hxdom : x ∈ world_dom (m : WorldT)).
  { exact (ty_denote_gas_ret_fvar_world_dom (S gas) Δ τlt x m Hden). }
  pose proof (ty_denote_gas_ret_fvar_relevant_lookup
    (S gas) Δ τlt x m Hden) as Hxlookup_rel.
  pose proof Hden as Hden_body.
  cbn [ty_denote_gas] in Hden_body.
  rewrite res_models_and_iff in Hden_body.
  destruct Hden_body as [_ Hforall].
  destruct (res_models_forall_rev m _ Hforall) as [L Hforall_open].
  pose (z := fresh_for
    (L ∪ world_dom (m : WorldT) ∪ lvars_fv (dom Δ) ∪ {[x; y]})).
  assert (Hzfresh :
      z ∉ L ∪ world_dom (m : WorldT) ∪ lvars_fv (dom Δ) ∪ {[x; y]}).
  { subst z. apply fresh_for_not_in. }
  assert (HzL : z ∉ L).
  { intros HzL. apply Hzfresh. fix_union_member. }
  assert (Hzm : z ∉ world_dom (m : WorldT)).
  { intros Hzm. apply Hzfresh. fix_union_member. }
  assert (HzΔ : LVFree z ∉ dom Δ).
  {
    intros Hz.
    apply lvars_fv_elem in Hz.
    apply Hzfresh. fix_union_member.
  }
  assert (Hzx : z <> x).
  {
    intros ->. apply Hzfresh.
    apply elem_of_union_r.
    set_unfold. auto.
  }
  assert (Hzy : z <> y).
  {
    intros ->. apply Hzfresh.
    apply elem_of_union_r.
    set_unfold. auto.
  }
  assert (Hze : z ∉ fv_tm (tret (vfvar x))).
  {
    cbn [fv_tm fv_value].
    intros Hzx_mem.
    apply elem_of_singleton in Hzx_mem.
    exact (Hzx Hzx_mem).
  }
  destruct (expr_result_extension_witness_exists (tret (vfvar x)) z Hze)
    as [Fx HFx].
  assert (Happ : extension_applicable Fx m).
  {
    constructor.
    - destruct HFx as [_ [Hin _] _].
      unfold ext_in in Hin. rewrite Hin.
      cbn [fv_tm fv_value].
      intros a Ha.
      apply elem_of_singleton in Ha. subst a.
      exact Hxdom.
    - destruct HFx as [_ [_ Hout] _].
      unfold ext_out in Hout. rewrite Hout.
      intros a Ha.
      apply elem_of_singleton in Ha. subst a.
      exact Hzm.
  }
  destruct (res_extend_by_exists m Fx Happ) as [mx Hext].
  pose proof (res_extend_by_dom m Fx mx Hext) as Hmxdom.
  pose proof (res_extend_by_restrict_base m Fx mx Hext) as Hmxrestrict.
  assert (Hmxdom_forall :
      world_dom (mx : WorldT) = world_dom (m : WorldT) ∪ {[z]}).
  {
    rewrite Hmxdom.
    destruct HFx as [_ [_ Hout] _].
    unfold ext_out in Hout. rewrite Hout. reflexivity.
  }
  pose proof (Hforall_open z HzL mx Hmxdom_forall Hmxrestrict)
    as Hopened.
		  rewrite !formula_open_impl in Hopened.
  rewrite formula_open_expr_result_formula_at_shift0 in Hopened.
  2:{ apply lvars_shift_from_lc.
      apply relevant_env_closed. exact HΔclosed. }
  2:{
    rewrite lvars_shift_from_fv.
    intros Hzrel.
    pose proof (relevant_env_dom_subset_direct Δ τlt (tret (vfvar x)))
      as Hrel.
    apply HzΔ.
    apply Hrel.
    apply lvars_fv_elem in Hzrel.
    exact Hzrel.
  }
  2:{ apply LC_ret. apply LC_fvar. }
  2:{ exact Hze. }
			  rewrite formula_open_fibvars in Hopened.
		  replace
    (set_swap (LVBound 0) (LVFree z)
      (qual_vars (mk_q_lt_base b (vbvar 0) (vfvar y)) ∖ {[LVBound 0]}))
    with
      (qual_vars
        (qual_open_atom 0 z (mk_q_lt_base b (vbvar 0) (vfvar y))) ∖
        {[LVFree z]})
    in Hopened.
  2:{
    symmetry. apply lt_qual_open_fibvars_set. exact Hzy.
  }
  assert (Hzden :
      mx ⊨ ty_denote_gas (S gas) (<[LVFree z := erase_ty τlt]> Δ)
        τlt (tret (vfvar z))).
  {
    eapply ty_denote_gas_result_ext; eauto.
  }
  pose proof (ty_denote_gas_guard _ _ _ _ _ Hzden) as Hzguard.
  pose proof Hzguard as Hzguard_parts.
  repeat rewrite res_models_and_iff in Hzguard_parts.
  destruct Hzguard_parts as [_ [Hzworld _]].
  pose proof (ty_denote_gas_ret_fvar_relevant_lookup
    (S gas) (<[LVFree z := erase_ty τlt]> Δ) τlt z mx Hzden)
    as Hzlookup_rel.
  assert (Hexpr_z :
      mx ⊨ expr_result_formula_at
        (lvars_shift_from 0 (dom (relevant_env Δ τlt (tret (vfvar x)))))
        (tret (vfvar x)) (LVFree z)).
  {
    assert (HDm :
        lvars_fv
          (lvars_shift_from 0
            (dom (relevant_env Δ τlt (tret (vfvar x))))) ⊆
        world_dom (m : WorldT)).
    {
      rewrite lvars_shift_from_fv.
      intros a Ha.
      apply basic_world_formula_models_iff in Hworld as [_ [Hdom _]].
      apply Hdom. exact Ha.
    }
    assert (Hclosed_x : wfworld_closed_on (fv_tm (tret (vfvar x))) m).
    {
      eapply basic_world_formula_wfworld_closed_on_atoms; [|exact Hworld].
      cbn [fv_tm fv_value]. intros a Ha.
      unfold lvars_of_atoms in Ha.
      apply elem_of_map in Ha as [a0 [-> Ha]].
      apply elem_of_singleton in Ha. subst a0.
      eapply elem_of_dom_2.
      apply (storeA_restrict_lookup_some_2 _ _ _ _ Hxlookup_rel).
      unfold relevant_lvars.
      apply elem_of_union_r.
      cbn [tm_lvars tm_lvars_at value_lvars_at].
      apply elem_of_singleton. reflexivity.
    }
    pose proof (expr_total_formula_to_atom_world (tret (vfvar x)) m Htotal)
      as Htotal_atom.
    assert (Hbig :
      mx ⊨ expr_result_formula_at
        (lvars_shift_from 0 (dom (relevant_env Δ τlt (tret (vfvar x)))) ∪
          tm_lvars (tret (vfvar x)))
        (tret (vfvar x)) (LVFree z)).
    {
      eapply expr_result_formula_at_of_result_extends.
      - apply lvars_shift_from_lc.
        apply relevant_env_closed. exact HΔclosed.
      - apply LC_ret. apply LC_fvar.
      - exact HDm.
      - cbn [fv_tm fv_value].
        intros a Ha.
        apply elem_of_singleton in Ha. subst a.
        exact Hxdom.
      - intros Hzbad.
        apply elem_of_union in Hzbad as [Hzrel|Hze_bad].
        + rewrite lvars_shift_from_fv in Hzrel.
          apply HzΔ.
          pose proof (relevant_env_dom_subset_direct Δ τlt (tret (vfvar x)))
            as Hrel.
          apply Hrel. apply lvars_fv_elem in Hzrel. exact Hzrel.
        + exact (Hze Hze_bad).
      - exact HFx.
      - exact Hext.
      - exact Htotal_atom.
      - exact Hclosed_x.
    }
    eapply expr_result_formula_at_coarsen_domain; [| | |exact Hbig].
    - intros u Hu. apply elem_of_union_l. exact Hu.
    - cbn [tm_lvars tm_lvars_at value_lvars_at].
      intros u Hu.
      apply elem_of_singleton in Hu. subst u.
      unfold lvars_shift_from.
      apply elem_of_map. exists (LVFree x). split; [reflexivity|].
      unfold relevant_env, lty_env_restrict_lvars.
      rewrite storeA_restrict_dom.
      apply elem_of_intersection. split.
      + eapply elem_of_dom_2. exact Hxlookup_rel.
      + unfold relevant_lvars.
        cbn [tm_lvars tm_lvars_at value_lvars_at context_ty_lvars
          context_ty_lvars_at qual_vars qual_lvars].
        apply elem_of_union_r.
        apply elem_of_singleton. reflexivity.
    - intros Hzbad.
      apply elem_of_union in Hzbad as [Hzrel|Hze_bad].
      + apply lvars_fv_elem in Hzrel.
        rewrite lvars_shift_from_fv in Hzrel.
        apply lvars_fv_elem in Hzrel.
        apply HzΔ.
        pose proof (relevant_env_dom_subset_direct Δ τlt (tret (vfvar x)))
          as Hrel.
        apply Hrel. exact Hzrel.
      + apply Hze.
        rewrite <- tm_lvars_fv.
        apply lvars_fv_elem. exact Hze_bad.
  }
		  pose proof (res_models_impl_elim mx _ _ Hopened Hexpr_z)
		    as Hfib_over.
  pose proof (over_open_body_from_typed b
    (mk_q_lt_base b (vbvar 0) (vfvar y)) z mx Hfib_over)
    as Hfib_over_old.
	  assert (Hfib_y :
	      mx ⊨ FFibVars ({[LVFree y]} : lvset)
	        (FOver (FAtom
	          (qual_open_atom 0 z (mk_q_lt_base b (vbvar 0) (vfvar y)))))).
  {
    replace ({[LVFree y]} : lvset)
      with
	        (qual_vars
	          (qual_open_atom 0 z (mk_q_lt_base b (vbvar 0) (vfvar y))) ∖
	          {[LVFree z]})
	      by exact (lt_qual_open_vars_without_opened b z y Hzy).
	    exact Hfib_over_old.
	  }
  pose proof (res_models_scoped _ _ Hfib_y) as Hscope_fib.
  assert (Hy_mx_dom : y ∈ world_dom (mx : WorldT)).
  {
    unfold formula_scoped_in_world in Hscope_fib.
    apply Hscope_fib.
    rewrite formula_fv_fibvars.
    apply elem_of_union_l.
    rewrite lvars_fv_singleton_free.
    fix_singleton_side.
  }
  assert (Hy_m_dom : y ∈ world_dom (m : WorldT)).
  {
    rewrite Hmxdom in Hy_mx_dom.
    destruct HFx as [_ [_ Hout] _].
    unfold ext_out in Hout. rewrite Hout in Hy_mx_dom.
    apply elem_of_union in Hy_mx_dom as [Hy_m|Hy_z].
    - exact Hy_m.
    - apply elem_of_singleton in Hy_z. symmetry in Hy_z. contradiction.
  }
  assert (Hyσ_dom : y ∈ dom (σ : StoreT)).
  {
    change (y ∈ dom (σ : gmap atom value)).
    rewrite (wfworld_store_dom m σ Hσ). exact Hy_m_dom.
  }
  destruct (σ !! y) as [vy|] eqn:Hσy.
  2:{
    apply not_elem_of_dom in Hσy. contradiction.
  }
  assert (Hxσdom : x ∈ dom (σ : StoreT)).
  {
    change (x ∈ dom (σ : gmap atom value)).
    rewrite (wfworld_store_dom m σ Hσ). exact Hxdom.
  }
  destruct (σ !! x) as [vx|] eqn:Hσx.
  2:{
    apply not_elem_of_dom in Hσx. contradiction.
  }
  set (σX := store_restrict σ (ext_in Fx)).
  assert (HσXdom : dom (σX : StoreT) = ext_in Fx).
  {
    subst σX.
    eapply extA_projection_dom; eauto.
  }
  destruct (extA_rel_nonempty Fx σX HσXdom)
    as [we [σe [HFrel Hσe]]].
  set (σmx := σ ∪ σe : StoreT).
  assert (Hσmx : (mx : WorldT) σmx).
  {
    apply (proj2 (resA_extend_by_store_iff m Fx mx σmx Hext)).
    exists σ, we, σe. repeat split; eauto.
  }
  destruct (res_fiber_from_projection_of_store mx {[y]} σmx)
    as [mfib [Hfiber Hσmx_fib]].
  {
    intros a Ha.
    apply elem_of_singleton in Ha. subst a. exact Hy_mx_dom.
  }
  { exact Hσmx. }
  unfold res_models in Hfib_y.
  cbn [formula_measure res_models_fuel] in Hfib_y.
  destruct Hfib_y as [_ [_ Hfib_y_body]].
  rewrite lvars_fv_singleton_free in Hfib_y_body.
  specialize (Hfib_y_body (store_restrict σmx {[y]}) mfib Hfiber).
  unfold res_models in Hfib_y_body.
  cbn [formula_measure res_models_fuel] in Hfib_y_body.
  destruct Hfib_y_body as [_ [mo [Hsub_fib_mo Hqual_mo]]].
  assert (Hqual_model :
      mo ⊨ formula_msubst_store (store_restrict σmx {[y]})
        (FAtom
          (qual_open_atom 0 z (mk_q_lt_base b (vbvar 0) (vfvar y))))).
  {
    unfold res_models. models_fuel_irrel Hqual_mo.
  }
  destruct Hsub_fib_mo as [_ Hsub_stores].
  assert (Hσmx_mo : (mo : WorldT) σmx).
  { apply Hsub_stores. exact Hσmx_fib. }
  assert (Hσy_proj_dom :
      dom (store_restrict σmx {[y]} : StoreT) = {[y]}).
  {
    change (dom (storeA_restrict σmx ({[y]} : aset) : gmap atom value) =
      {[y]}).
    rewrite storeA_restrict_dom.
    rewrite (wfworld_store_dom mx σmx Hσmx).
    apply set_eq. intros a. split.
    - intros Ha. apply elem_of_intersection in Ha as [_ Ha]. exact Ha.
    - intros Ha. apply elem_of_intersection. split; [|exact Ha].
      apply elem_of_singleton in Ha. subst a. exact Hy_mx_dom.
  }
  pose proof (lt_type_qualifier_open_msubst_lookup b z y Hzy
    (store_restrict σmx {[y]}) mo σmx Hσy_proj_dom
    Hqual_model Hσmx_mo)
    as [cz [cy [Hσmx_z [Hσproj_y Hlt]]]].
  assert (Hσmx_x : σmx !! x = Some vx).
  {
    subst σmx.
    apply map_lookup_union_Some_raw. left. exact Hσx.
  }
  assert (Hσmx_y : σmx !! y = Some vy).
  {
    subst σmx.
    apply map_lookup_union_Some_raw. left. exact Hσy.
  }
  assert (Hclosed_ret_m : wfworld_closed_on (fv_tm (tret (vfvar x))) m).
  { eapply expr_basic_typing_world_closed_on_term; eauto. }
  assert (Hrestrict_eq :
      store_restrict σmx (fv_tm (tret (vfvar x))) =
      store_restrict σ (fv_tm (tret (vfvar x)))).
  {
    apply storeA_map_eq. intros a.
    rewrite !storeA_restrict_lookup.
    destruct (decide (a ∈ fv_tm (tret (vfvar x)))) as [Ha|Ha].
    - cbn [fv_tm fv_value] in Ha.
      apply elem_of_singleton in Ha. subst a.
      transitivity (Some vx); [exact Hσmx_x|symmetry; exact Hσx].
    - reflexivity.
  }
  assert (Hclosed_ret :
      store_closed (store_restrict σmx (fv_tm (tret (vfvar x))))).
  { rewrite Hrestrict_eq. exact (Hclosed_ret_m σ Hσ). }
  assert (Heval_ret :
      tm_eval_in_store (store_restrict σmx (fv_tm (tret (vfvar x))))
        (tret (vfvar x)) vx).
  {
    apply tm_eval_in_store_ret_fvar_lookup; [exact Hclosed_ret|].
    apply storeA_restrict_lookup_some_2.
    - exact Hσmx_x.
    - fix_singleton_side.
  }
  destruct (result_extension_store_lookup_output
    (tret (vfvar x)) z Fx m mx σmx HFx Hext Hσmx
    ltac:(exists vx; exact Heval_ret))
    as [vz [Hσmx_z_vz Heval_vz]].
  assert (Hvz_vx : vz = vx).
  {
    pose proof (tm_eval_in_store_ret_fvar_inv
      (store_restrict σmx (fv_tm (tret (vfvar x)))) x vz)
      as Hret_inv.
    specialize (Hret_inv Hclosed_ret).
    assert (Hx_restrict_dom :
        x ∈ dom (store_restrict σmx (fv_tm (tret (vfvar x))) : StoreT)).
    {
      change (x ∈ dom
        (storeA_restrict σmx (fv_tm (tret (vfvar x))) : gmap atom value)).
      rewrite storeA_restrict_dom.
      apply elem_of_intersection. split.
      - eapply elem_of_dom_2. exact Hσmx_x.
      - fix_singleton_side.
    }
    specialize (Hret_inv Hx_restrict_dom Heval_vz).
    assert (Hx_restrict_lookup :
        (store_restrict σmx (fv_tm (tret (vfvar x))) : StoreT) !! x =
        Some vx).
    {
      apply (storeA_restrict_lookup_some_2 _ _ _ _ Hσmx_x).
      fix_singleton_side.
    }
    change ((store_restrict σmx (fv_tm (tret (vfvar x))) : StoreT) !! x =
      Some vz) in Hret_inv.
    congruence.
  }
  assert (Hσmx_z_vx : σmx !! z = Some vx).
  { rewrite Hvz_vx in Hσmx_z_vz. exact Hσmx_z_vz. }
  assert (Hσproj_y' :
      (store_restrict σmx {[y]} : StoreT) !! y = Some vy).
  {
    apply (storeA_restrict_lookup_some_2 _ _ _ _ Hσmx_y).
    fix_singleton_side.
  }
  exists cz, cy.
  split; [|split].
  - congruence.
  - congruence.
  - exact Hlt.
Qed.

(** Opened-argument and unfolded-result support for the Fix case. *)

Lemma fix_arrow_opened_app_static_guard_full
    (Σ : tyctx) Γ τx τ vf b t
    (my : WfWorldT) y :
  context_typing_wf Σ Γ
    (tret (vfix (TBase b →ₜ t) vf)) (CTArrow τx τ) ->
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_value vf ∪
      fv_cty τx ∪ fv_cty τ ->
  my ⊨ ctx_denote_under Σ (CtxComma Γ (CtxBind y τx)) ->
  my ⊨ ty_static_guard_formula
    ((<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ))))
    (cty_open 0 y τ)
    (tapp_tm (tret (vfix (TBase b →ₜ t) vf)) (vfvar y)).
Proof.
  intros Hwf Hy Hctx_comma.
  assert (Hwf_app :
      context_typing_wf Σ (CtxComma Γ (CtxBind y τx))
        (tapp_tm (tret (vfix (TBase b →ₜ t) vf)) (vfvar y))
        (cty_open 0 y τ)).
  {
    unfold context_typing_wf.
    pose proof (context_typing_wf_ctx Σ Γ
      (tret (vfix (TBase b →ₜ t) vf)) (CTArrow τx τ) Hwf) as Hwfctx.
    pose proof (wf_ctx_under_basic Σ Γ Hwfctx) as HbasicΓ.
    pose proof (basic_ctx_erase_dom (dom Σ) Γ HbasicΓ) as HdomΓ.
    pose proof (context_typing_wf_context_ty Σ Γ
      (tret (vfix (TBase b →ₜ t) vf)) (CTArrow τx τ) Hwf) as Hτ.
    cbn [wf_context_ty_at] in Hτ.
    destruct Hτ as [Hτx Hτ].
    split.
    + unfold wf_ctx_under. cbn [basic_ctx]. split; [exact HbasicΓ|]. split.
      * apply basic_ctx_bind.
        -- rewrite <- HdomΓ.
           eapply context_union_fresh_env_erase_ctx. exact Hy.
        -- eapply (wf_context_ty_at_mono_env
             0 (dom (erase_ctx Γ)) (dom Σ ∪ ctx_dom Γ)).
           ++ rewrite HdomΓ. better_set_solver.
           ++ exact Hτx.
      * cbn [ctx_dom]. rewrite <- HdomΓ.
        apply elem_of_disjoint. intros a Ha Hay.
        apply elem_of_singleton in Hay. subst a.
        eapply context_union_fresh_erase_ctx_from_erasure_under. exact Hy. exact Ha.
    + split.
      * eapply (wf_context_ty_at_mono_env
          0 (dom (erase_ctx Γ) ∪ {[y]})
          (dom (erase_ctx (CtxComma Γ (CtxBind y τx))))).
        -- rewrite erase_ctx_comma_bind_dom. reflexivity.
        -- apply wf_context_ty_at_open_at.
           ++ eapply context_union_fresh_erase_ctx_from_erasure_under. exact Hy.
           ++ exact Hτ.
      * rewrite cty_open_preserves_erasure.
        replace (erase_ctx (CtxComma Γ (CtxBind y τx)))
          with (<[y := erase_ty τx]> (erase_ctx Γ)).
        -- apply basic_typing_tapp_tm_fvar_insert.
           ++ eapply context_union_fresh_erase_ctx_from_erasure_under. exact Hy.
           ++ exact (context_typing_wf_basic_typing Σ Γ
                (tret (vfix (TBase b →ₜ t) vf)) (CTArrow τx τ) Hwf).
        -- symmetry. apply erase_ctx_comma_bind_fresh.
           eapply context_union_fresh_erase_ctx_from_erasure_under. exact Hy.
  }
  eapply context_typing_wf_denot_static_guard_comma_bind_insert; eauto.
  eapply context_union_fresh_erase_ctx_from_erasure_under. exact Hy.
Qed.

Lemma fix_arrow_open_arg_normalize
    (Σ : tyctx) Γ τx τ vf b t
    (my : WfWorldT) y :
  context_typing_wf Σ Γ
    (tret (vfix (TBase b →ₜ t) vf)) (CTArrow τx τ) ->
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_value vf ∪
      fv_cty τx ∪ fv_cty τ ->
  my ⊨ formula_open 0 y
    (ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
      (typed_lty_env_bind
        (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
          (CTArrow τx τ) (tret (vfix (TBase b →ₜ t) vf)))
        (erase_ty τx))
      (cty_shift 0 τx) (tret (vbvar 0))) ->
  my ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
    ((<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ))))
    τx (tret (vfvar y)).
Proof.
  intros Hwf Hy Harg.
  assert (Hlcτx : lc_context_ty τx).
  {
    apply (context_typing_wf_arrow_arg_lc Σ Γ
      (tret (vfix (TBase b →ₜ t) vf)) τx τ).
    exact Hwf.
  }
  rewrite formula_open_ty_denote_gas_bind_ret_bvar0 in Harg.
  2:{ apply relevant_env_closed. apply atom_store_to_lvar_store_closed. }
  2:{
    apply relevant_env_arrow_fresh_free.
    - clear -Hy. better_set_solver.
    - clear -Hy. better_set_solver.
    - cbn [fv_tm fv_value]. clear -Hy. better_set_solver.
  }
  2:{ clear -Hy. better_set_solver. }
  2:{ exact Hlcτx. }
  exact (arrow_open_arg_to_inserted_env
    (Nat.max (cty_depth τx) (cty_depth τ))
    (atom_env_to_lty_env (erase_ctx Γ)) τx τ
    (tret (vfix (TBase b →ₜ t) vf)) my y Harg).
Qed.

Lemma fix_arrow_open_arg_to_bind_denotation
    (Σ : tyctx) Γ τx τ vf b t
    (my : WfWorldT) y :
  context_typing_wf Σ Γ
    (tret (vfix (TBase b →ₜ t) vf)) (CTArrow τx τ) ->
  my ⊨ ty_denote_gas (cty_depth τx)
      ((<[LVFree y := erase_ty τx]>
        (atom_env_to_lty_env (erase_ctx Γ))))
      τx (tret (vfvar y)) ->
  my ⊨ ty_denote_gas (cty_depth τx)
    (atom_env_to_lty_env (<[y:=erase_ty τx]> (ctx_erasure_under Σ Γ)))
    τx (tret (vfvar y)).
Proof.
  intros Hwf Harg.
  eapply ty_denote_gas_ret_fvar_insert_ctx_erasure_under.
  - pose proof (context_typing_wf_ctx Σ Γ
      (tret (vfix (TBase b →ₜ t) vf)) (CTArrow τx τ) Hwf) as Hwfctx.
    exact (wf_ctx_under_basic Σ Γ Hwfctx).
  - pose proof (context_typing_wf_context_ty Σ Γ
      (tret (vfix (TBase b →ₜ t) vf)) (CTArrow τx τ) Hwf) as Hτ.
    cbn [wf_context_ty_at] in Hτ.
    destruct Hτ as [Hτx _].
    eapply wf_context_ty_at_fv_subset. exact Hτx.
  - exact Harg.
Qed.

Lemma fix_arrow_open_arg_to_bind_ctx
    (Σ : tyctx) Γ τx τ vf b t
    (m my : WfWorldT) y :
  context_typing_wf Σ Γ
    (tret (vfix (TBase b →ₜ t) vf)) (CTArrow τx τ) ->
  my ⊨ ctx_denote_under Σ Γ ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_restrict my (world_dom (m : WorldT)) = m ->
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_value vf ∪
      fv_cty τx ∪ fv_cty τ ->
  my ⊨ ty_denote_gas (cty_depth τx)
      ((<[LVFree y := erase_ty τx]>
        (atom_env_to_lty_env (erase_ctx Γ))))
      τx (tret (vfvar y)) ->
  my ⊨ ctx_denote_under (Σ ∪ erase_ctx Γ) (CtxBind y τx).
Proof.
  intros Hwf Hctx_my Hdom Hrestrict Hy Harg.
  pose proof (fix_arrow_open_arg_to_bind_denotation
    Σ Γ τx τ vf b t my y Hwf Harg)
    as Hbind_den.
  eapply ctx_bind_from_inserted_erasure_arg_denotation.
  - eapply context_union_fresh_ctx_erasure_under. exact Hy.
  - pose proof (context_typing_wf_ctx Σ Γ
      (tret (vfix (TBase b →ₜ t) vf)) (CTArrow τx τ) Hwf) as Hwfctx.
    pose proof (wf_ctx_under_basic Σ Γ Hwfctx) as HbasicΓ.
    pose proof (context_typing_wf_context_ty Σ Γ
      (tret (vfix (TBase b →ₜ t) vf)) (CTArrow τx τ) Hwf) as Hτwf.
    cbn [wf_context_ty_at] in Hτwf.
    destruct Hτwf as [Hτx _].
    eapply ty_env_agree_ctx_erasure_under_of_basic_ctx.
    + exact HbasicΓ.
    + eapply wf_context_ty_at_fv_subset. exact Hτx.
  - exact Hctx_my.
  - exact Hbind_den.
Qed.

Lemma fix_arrow_open_arg_to_comma_ctx
    (Σ : tyctx) Γ τx τ vf b t
    (m my : WfWorldT) y :
  context_typing_wf Σ Γ
    (tret (vfix (TBase b →ₜ t) vf)) (CTArrow τx τ) ->
  m ⊨ ctx_denote_under Σ Γ ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_restrict my (world_dom (m : WorldT)) = m ->
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_value vf ∪
      fv_cty τx ∪ fv_cty τ ->
  my ⊨ ty_denote_gas (cty_depth τx)
      ((<[LVFree y := erase_ty τx]>
        (atom_env_to_lty_env (erase_ctx Γ))))
      τx (tret (vfvar y)) ->
  my ⊨ ctx_denote_under Σ (CtxComma Γ (CtxBind y τx)).
Proof.
  intros Hwf Hctx Hdom Hrestrict Hy Harg.
  pose proof (context_typing_wf_ctx Σ Γ
    (tret (vfix (TBase b →ₜ t) vf)) (CTArrow τx τ) Hwf) as Hwfctx.
  pose proof (wf_ctx_under_basic Σ Γ Hwfctx) as HbasicΓ.
  assert (Hle : m ⊑ my).
  { rewrite <- Hrestrict. apply res_restrict_le. }
  assert (Hctx_my : my ⊨ ctx_denote_under Σ Γ).
  { eapply res_models_kripke; eauto. }
  eapply ctx_denote_under_comma_intro; [exact HbasicΓ|exact Hctx_my|].
  eapply fix_arrow_open_arg_to_bind_ctx; eauto.
Qed.

Lemma fix_tapp_unfold_tm_equiv_on
    b t vf y (my : WfWorldT) :
  body_val vf ->
  y ∈ world_dom (my : WorldT) ->
  wfworld_closed_on
    (fv_tm (tapp_tm (tret (vfix (TBase b →ₜ t) vf)) (vfvar y)) ∪
     fv_tm (tapp_tm (tret (open_value 0 (vfvar y) vf))
       (vfix (TBase b →ₜ t) vf))) my ->
  tm_equiv_on my
    (tapp_tm (tret (vfix (TBase b →ₜ t) vf)) (vfvar y))
    (tapp_tm (tret (open_value 0 (vfvar y) vf))
      (vfix (TBase b →ₜ t) vf)).
Proof.
  intros Hbody Hy_dom Hclosed σ v Hσ.
  pose proof (tm_equiv_fix_unfold (TBase b →ₜ t) vf y my
    Hclosed Hbody Hy_dom σ v Hσ) as [Hfix_unfold Hunfold_fix].
  split; [exact Hfix_unfold|exact Hunfold_fix].
Qed.

Lemma fix_unfolded_result_to_opened_goal
    (Σ : tyctx) Γ τx τ vf b t
    (my : WfWorldT) y :
  context_typing_wf Σ Γ
    (tret (vfix (TBase b →ₜ t) vf)) (CTArrow τx τ) ->
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_value vf ∪
      fv_cty τx ∪ fv_cty τ ->
  my ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
    ((<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ))))
    (cty_open 0 y τ)
    (tapp_tm (tret (open_value 0 (vfvar y) vf))
      (vfix (TBase b →ₜ t) vf)) ->
  my ⊨ ty_static_guard_formula
    ((<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ))))
    (cty_open 0 y τ)
    (tapp_tm (tret (vfix (TBase b →ₜ t) vf)) (vfvar y)) ->
  my ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
    (<[LVFree y := erase_ty τx]>
      (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
        (CTArrow τx τ) (tret (vfix (TBase b →ₜ t) vf))))
    (cty_open 0 y τ)
    (tapp_tm (tret (vfix (TBase b →ₜ t) vf)) (vfvar y)).
Proof.
  intros Hwf Hy Hunfolded Hstatic.
  set (efix := tret (vfix (TBase b →ₜ t) vf)).
  assert (Hlc_efix : lc_tm efix).
  {
    subst efix.
    exact (context_typing_wf_lc_tm
      Σ Γ (tret (vfix (TBase b →ₜ t) vf)) (CTArrow τx τ) Hwf).
  }
  assert (Hbody_vf : body_val vf).
  {
    subst efix.
    apply lc_ret_iff_value in Hlc_efix.
    apply lc_fix_iff_body in Hlc_efix.
    exact Hlc_efix.
  }
  assert (Hτ_lc1 : cty_lc_at 1 τ).
  {
    apply (context_typing_wf_arrow_result_lc1 Σ Γ
      (tret (vfix (TBase b →ₜ t) vf)) τx τ).
    exact Hwf.
  }
  assert (Hzero_unfolded :
      my ⊨ ty_denote_gas 0
        (<[LVFree y := erase_ty τx]>
          (atom_env_to_lty_env (erase_ctx Γ)))
        (cty_open 0 y τ)
        (tapp_tm (tret (open_value 0 (vfvar y) vf))
          (vfix (TBase b →ₜ t) vf))).
  {
    apply ty_denote_gas_zero_of_guard.
    eapply ty_denote_gas_guard. exact Hunfolded.
  }
  assert (Hclosed_fix :
      wfworld_closed_on
        (fv_tm (tapp_tm (tret (vfix (TBase b →ₜ t) vf)) (vfvar y))) my).
  { eapply ty_static_guard_wfworld_closed_on_term. exact Hstatic. }
  assert (Hclosed_unfolded :
      wfworld_closed_on
        (fv_tm (tapp_tm (tret (open_value 0 (vfvar y) vf))
          (vfix (TBase b →ₜ t) vf))) my).
  {
    eapply denot_ty_lvar_guard_wfworld_closed_on_term.
    eapply ty_denote_gas_guard_of_zero. exact Hzero_unfolded.
  }
  assert (Hclosed :
      wfworld_closed_on
        (fv_tm (tapp_tm (tret (vfix (TBase b →ₜ t) vf)) (vfvar y)) ∪
         fv_tm (tapp_tm (tret (open_value 0 (vfvar y) vf))
           (vfix (TBase b →ₜ t) vf))) my).
  { apply wfworld_closed_on_union; assumption. }
  assert (Hy_dom : y ∈ world_dom (my : WorldT)).
  {
    pose proof (ty_static_guard_fv_tm_subset _ _ _ _ Hstatic)
      as Hfv_app.
    apply Hfv_app.
    rewrite fv_tapp_tm. cbn [fv_tm fv_value]. better_set_solver.
  }
  pose proof (fix_tapp_unfold_tm_equiv_on
    b t vf y my Hbody_vf Hy_dom Hclosed) as Heq.
  assert (Hzero_fix :
      my ⊨ ty_denote_gas 0
        (<[LVFree y := erase_ty τx]>
          (atom_env_to_lty_env (erase_ctx Γ)))
        (cty_open 0 y τ)
        (tapp_tm (tret (vfix (TBase b →ₜ t) vf)) (vfvar y))).
  {
	    pose proof (ty_denote_gas_guard_of_zero
	      (<[LVFree y := erase_ty τx]>
	        (atom_env_to_lty_env (erase_ctx Γ)))
	      (cty_open 0 y τ)
	      (tapp_tm (tret (open_value 0 (vfvar y) vf))
	        (vfix (TBase b →ₜ t) vf)) my Hzero_unfolded)
	      as Hguard_unfolded.
	    repeat rewrite res_models_and_iff in Hguard_unfolded.
	    destruct Hguard_unfolded as [_ [_ [_ Htotal_unfolded]]].
	    assert (Heq_unfold_fix :
	        tm_equiv_on my
	          (tapp_tm (tret (open_value 0 (vfvar y) vf))
	            (vfix (TBase b →ₜ t) vf))
	          (tapp_tm (tret (vfix (TBase b →ₜ t) vf)) (vfvar y))).
	    {
	      intros σ v Hσ.
	      specialize (Heq σ v Hσ) as [Hfix_unfold Hunfold_fix].
	      split; [exact Hunfold_fix|exact Hfix_unfold].
	    }
			    eapply ty_denote_gas_zero_transport_static_tm_equiv.
		    - exact Heq_unfold_fix.
		    - intros σ Hσ.
		      pose proof (tm_total_equiv_fix_unfold (TBase b →ₜ t) vf y my
		        Hclosed Hbody_vf Hy_dom σ Hσ) as Htotal_fix_unfold.
		      split; [exact (proj2 Htotal_fix_unfold)|exact (proj1 Htotal_fix_unfold)].
			    - exact Hstatic.
		    - apply lc_tapp_tm; [exact Hlc_efix|constructor].
		    - eapply ty_static_guard_fv_tm_subset. exact Hstatic.
		    - exact Hzero_unfolded.
	  }
	  assert (Hfix_open :
	      my ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
	        (<[LVFree y := erase_ty τx]>
	          (atom_env_to_lty_env (erase_ctx Γ)))
	        (cty_open 0 y τ)
	        (tapp_tm (tret (vfix (TBase b →ₜ t) vf)) (vfvar y))).
		  {
		    pose proof (ty_denote_gas_guard_of_zero
		      (<[LVFree y := erase_ty τx]>
		        (atom_env_to_lty_env (erase_ctx Γ)))
		      (cty_open 0 y τ)
		      (tapp_tm (tret (open_value 0 (vfvar y) vf))
		        (vfix (TBase b →ₜ t) vf)) my Hzero_unfolded)
		      as Hguard_unfolded.
		    pose proof (ty_denote_gas_guard_of_zero
		      (<[LVFree y := erase_ty τx]>
		        (atom_env_to_lty_env (erase_ctx Γ)))
		      (cty_open 0 y τ)
		      (tapp_tm (tret (vfix (TBase b →ₜ t) vf)) (vfvar y)) my
	      Hzero_fix) as Hguard_fix.
	    repeat rewrite res_models_and_iff in Hguard_unfolded.
	    repeat rewrite res_models_and_iff in Hguard_fix.
	    destruct Hguard_unfolded as [_ [_ [_ Htotal_unfolded]]].
		    destruct Hguard_fix as [_ [_ [_ Htotal_fix]]].
				    eapply ty_denote_gas_tm_equiv.
				    - refine (conj _ (conj _ (conj _ _))).
					      + intros σ0 v0 Hσ0. symmetry. exact (Heq σ0 v0 Hσ0).
						      + eapply tm_total_equiv_of_total_formulas; eauto.
						      + exact Hzero_unfolded.
					      + exact Hzero_fix.
				    - exact Hunfolded.
		  }
	  eapply ty_equiv_arrow_result_tgt_goal.
	  - clear -Hy. set_solver.
	  - apply arrow_result_open_vars_subset; [exact Hτ_lc1|clear -Hy; set_solver].
	  - exact Hfix_open.
Qed.

Lemma fix_unfolded_app_static_guard_full
    (Σ : tyctx) Γ τx τ vf b t
    (my : WfWorldT) y :
  erase_ty τx = TBase b ->
  erase_ty τ = t ->
  context_typing_wf Σ Γ
    (tret (vfix (TBase b →ₜ t) vf)) (CTArrow τx τ) ->
  context_typing_wf Σ
    (CtxComma Γ (CtxBind y τx))
    (tret ({0 ~> vfvar y} vf))
    (CTArrow (fix_rec_call_ty b y τx τ) ({0 ~> y} τ)) ->
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_value vf ∪
      fv_cty τx ∪ fv_cty τ ->
  my ⊨ ctx_denote_under Σ (CtxComma Γ (CtxBind y τx)) ->
  my ⊨ ty_static_guard_formula
    ((<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ))))
    (cty_open 0 y τ)
    (tapp_tm (tret (open_value 0 (vfvar y) vf))
      (vfix (TBase b →ₜ t) vf)).
Proof.
  intros Hτx Hτ Hwf Hbody_wf Hy Hctx_comma.
  assert (Hwf_app :
      context_typing_wf Σ (CtxComma Γ (CtxBind y τx))
        (tapp_tm (tret (open_value 0 (vfvar y) vf))
          (vfix (TBase b →ₜ t) vf))
        (cty_open 0 y τ)).
  {
    unfold context_typing_wf.
    pose proof (context_typing_wf_ctx Σ
      (CtxComma Γ (CtxBind y τx))
      (tret ({0 ~> vfvar y} vf))
      (CTArrow (fix_rec_call_ty b y τx τ) ({0 ~> y} τ))
      Hbody_wf) as Hwfctx_body.
    pose proof (context_typing_wf_context_ty Σ Γ
      (tret (vfix (TBase b →ₜ t) vf)) (CTArrow τx τ) Hwf) as Hτ_outer.
    cbn [wf_context_ty_at] in Hτ_outer.
    destruct Hτ_outer as [_ Hτres_outer].
    split.
    - exact Hwfctx_body.
    - split.
      + eapply (wf_context_ty_at_mono_env
          0 (dom (erase_ctx Γ) ∪ {[y]})
          (dom (erase_ctx (CtxComma Γ (CtxBind y τx))))).
        * rewrite erase_ctx_comma_bind_dom. reflexivity.
        * apply wf_context_ty_at_open_at.
          -- eapply context_union_fresh_erase_ctx_from_erasure_under. exact Hy.
          -- exact Hτres_outer.
      + rewrite cty_open_preserves_erasure.
        eapply basic_typing_tapp_tm.
        * pose proof (context_typing_wf_basic_typing Σ
            (CtxComma Γ (CtxBind y τx))
            (tret ({0 ~> vfvar y} vf))
            (CTArrow (fix_rec_call_ty b y τx τ) ({0 ~> y} τ))
            Hbody_wf) as Hbody_basic.
          change (erase_ctx (CtxComma Γ (CtxBind y τx)) ⊢ₑ
            tret (open_value 0 (vfvar y) vf)
            ⋮ (erase_ty (fix_rec_call_ty b y τx τ) →ₜ
               erase_ty (cty_open 0 y τ))) in Hbody_basic.
          rewrite cty_open_preserves_erasure in Hbody_basic.
          exact Hbody_basic.
        * pose proof (context_typing_wf_basic_typing Σ Γ
            (tret (vfix (TBase b →ₜ t) vf)) (CTArrow τx τ) Hwf)
            as Hfix_basic_tm.
          inversion Hfix_basic_tm; subst.
          match goal with
          | Hfix_val : erase_ctx Γ ⊢ᵥ
              vfix _ vf ⋮ _ |- _ =>
              eapply basic_typing_weaken_value; [exact Hfix_val|]
          end.
          rewrite erase_ctx_comma_bind_fresh.
          -- apply insert_subseteq.
             apply not_elem_of_dom.
             eapply context_union_fresh_erase_ctx_from_erasure_under. exact Hy.
          -- eapply context_union_fresh_erase_ctx_from_erasure_under. exact Hy.
  }
  eapply context_typing_wf_denot_static_guard_comma_bind_insert; eauto.
  eapply context_union_fresh_erase_ctx_from_erasure_under. exact Hy.
Qed.
