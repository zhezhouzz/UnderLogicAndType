(** * ChoiceTyping.TLetTotal

    Context-preservation helpers for the [tlet] result world.

    These lemmas build the comma-extended denotation context after evaluating
    the let-bound expression. *)

From CoreLang Require Import Instantiation InstantiationProps OperationalProps BasicTypingProps
  LocallyNamelessProps StrongNormalization.
From ChoiceTyping Require Export RegularDenotation.
From ChoiceTyping Require Import Naming ResultWorldClosed ResultWorldExprCont
  SoundnessCommon.
From ChoiceType Require Import BasicStore LocallyNamelessProps.

Lemma tlet_e1_choice_typing_wf
    (Σ : gmap atom ty) (Γ : ctx) (τ1 : choice_ty) e1
    (m : WfWorld) :
  erase_ctx_under Σ Γ ⊢ₑ e1 ⋮ erase_ty τ1 →
  m ⊨ denot_ctx_in_env Σ Γ →
  denot_ty_total_model_in_ctx_under Σ Γ τ1 e1 m →
  choice_typing_wf Σ Γ e1 τ1.
Proof.
  intros Herase Hm Hmodel.
  eapply denot_ty_total_model_choice_typing_wf; eauto.
Qed.

Lemma let_result_world_on_preserves_context Σ Γ e x (w : WfWorld) Hfresh Hresult :
  w ⊨ denot_ctx_in_env Σ Γ →
  let_result_world_on e x w Hfresh Hresult ⊨ denot_ctx_in_env Σ Γ.
Proof.
  intros Hctx.
  eapply res_models_kripke; eauto 6 using let_result_world_on_le.
Qed.

Lemma let_result_world_on_ret_decompose
    X e x ν (m : WfWorld)
    Hfreshx Hresultx Hfreshν_ret Hresultν_ret Hfreshν_e Hresultν_e :
  fv_tm e ⊆ X →
  lc_tm e →
  world_dom (m : World) = X →
  x ∉ X →
  ν ∉ X ∪ {[x]} →
  world_closed_on X m →
  res_restrict
    (let_result_world_on (tret (vfvar x)) ν
      (let_result_world_on e x m Hfreshx Hresultx)
      Hfreshν_ret Hresultν_ret)
    (X ∪ {[ν]}) =
  let_result_world_on e ν m Hfreshν_e Hresultν_e.
Proof.
  intros Hfv Hlc Hdom HxX Hν Hclosed.
  apply wfworld_ext. apply world_ext.
  - simpl. rewrite Hdom. clear -HxX Hν. set_solver.
  - intros σν. simpl. split.
    + intros [σxν [Hnested Hrestrict]].
      destruct (let_result_world_on_elim (tret (vfvar x)) ν
        (let_result_world_on e x m Hfreshx Hresultx)
        Hfreshν_ret Hresultν_ret σxν Hnested)
        as [σx [vν [Hσx [Hret ->]]]].
      destruct (let_result_world_on_elim e x m Hfreshx Hresultx σx Hσx)
        as [σ [vx [Hσ [He_steps ->]]]].
      assert (Hvx_reg : stale vx = ∅ ∧ is_lc vx).
      {
        eapply steps_closed_result_of_restrict_world.
        - rewrite Hdom; eauto 6.
        - set_solver.
        - eauto 6.
        - eapply world_closed_on_mono; eauto 6.
        - exists σ. split; eauto 6.
        - replace (store_restrict (store_restrict σ (fv_tm e)) (fv_tm e))
            with (store_restrict σ (fv_tm e)).
          + eauto 6.
          + symmetry. apply store_restrict_twice_same.
      }
      assert (Hlookupx :
        store_restrict (<[x:=vx]> σ : Store) {[x]} !! x = Some vx).
      {
        apply (store_restrict_lookup_some_2
          (<[x:=vx]> σ : Store) ({[x]} : aset) x vx).
        - change ((<[x:=vx]> σ : Store) !! x = Some vx).
          rewrite lookup_insert_eq. reflexivity.
        - apply elem_of_singleton. reflexivity.
      }
      simpl in Hret.
      change (m{store_restrict (<[x:=vx]> σ : Store) {[x]}}
        (tret (vfvar x)) →* tret vν) in Hret.
      rewrite (msubst_ret_fvar_lookup_closed_value
        (store_restrict (<[x:=vx]> σ : Store) {[x]}) x vx
        (proj1 Hvx_reg) Hlookupx) in Hret.
      pose proof (value_steps_self vx (tret vν) Hret) as Heq.
      inversion Heq. subst vν.
      exists σ, vx. split; [exact Hσ |].
      split; [exact He_steps |].
      rewrite <- Hrestrict.
      rewrite store_restrict_insert_fresh_union.
      * rewrite store_restrict_insert_notin by exact HxX.
        replace (store_restrict σ X) with σ.
        -- reflexivity.
        -- symmetry. apply store_restrict_idemp_eq.
           pose proof (wfworld_store_dom m σ Hσ) as Hσdom.
           rewrite Hdom in Hσdom. exact Hσdom.
      * eapply store_lookup_none_of_dom.
        -- apply wfworld_store_dom. exact Hσx.
        -- rewrite let_result_world_on_dom, Hdom. exact Hν.
      * clear -HxX Hν. set_solver.
    + intros [σ [vx [Hσ [He_steps ->]]]].
      exists (<[ν:=vx]> (<[x:=vx]> σ)). split.
      * exists (<[x:=vx]> σ), vx. split.
        -- exists σ, vx. split; [exact Hσ |]. split; [exact He_steps | reflexivity].
        -- split.
           ++ simpl.
              assert (Hvx_reg : stale vx = ∅ ∧ is_lc vx).
              {
                eapply steps_closed_result_of_restrict_world.
                - rewrite Hdom. exact Hfv.
                - set_solver.
                - exact Hlc.
                - eapply world_closed_on_mono; [exact Hfv | exact Hclosed].
                - exists σ. split; [exact Hσ | reflexivity].
                - replace (store_restrict (store_restrict σ (fv_tm e)) (fv_tm e))
                    with (store_restrict σ (fv_tm e)).
                  + exact He_steps.
                  + symmetry. apply store_restrict_twice_same.
              }
              change (m{store_restrict (<[x:=vx]> σ : Store) {[x]}}
                (tret (vfvar x)) →* tret vx).
              rewrite (msubst_ret_fvar_lookup_closed_value
                (store_restrict (<[x:=vx]> σ : Store) {[x]}) x vx).
              ** apply Steps_refl. constructor. exact (proj2 Hvx_reg).
              ** exact (proj1 Hvx_reg).
	              ** apply (store_restrict_lookup_some_2
	                  (<[x:=vx]> σ : Store) ({[x]} : aset) x vx).
	                 --- change ((<[x:=vx]> σ : Store) !! x = Some vx).
	                     rewrite lookup_insert_eq. reflexivity.
	                 --- apply elem_of_singleton. reflexivity.
           ++ reflexivity.
      * rewrite store_restrict_insert_fresh_union.
        -- rewrite store_restrict_insert_notin by exact HxX.
           replace (store_restrict σ X) with σ.
           ++ reflexivity.
           ++ symmetry. apply store_restrict_idemp_eq.
              pose proof (wfworld_store_dom m σ Hσ) as Hσdom.
              rewrite Hdom in Hσdom. exact Hσdom.
        -- eapply store_lookup_none_of_dom.
           ++ assert (Hσx :
                (let_result_world_on e x m Hfreshx Hresultx : World)
                  (<[x:=vx]> σ)).
              { apply let_result_world_on_member; [exact Hσ | exact He_steps]. }
              apply (wfworld_store_dom
                (let_result_world_on e x m Hfreshx Hresultx)
                (<[x:=vx]> σ) Hσx).
           ++ rewrite let_result_world_on_dom, Hdom. exact Hν.
	        -- clear -HxX Hν. set_solver.
Qed.

Lemma FExprContIn_let_result_bound
    Σ T e x Q (m : WfWorld) Hfresh Hresult :
  Σ ⊢ₑ e ⋮ T →
  world_dom (m : World) = dom Σ →
  world_closed_on (dom Σ) m →
  expr_total_on (dom Σ) e m →
  formula_fv Q ⊆ dom Σ →
  x ∉ dom Σ ∪ fv_tm e →
  m ⊨ FExprContIn Σ e Q →
  let_result_world_on e x m Hfresh Hresult
    ⊨ FExprContIn (<[x := T]> Σ) (tret (vfvar x)) Q.
Proof.
  intros Htyped Hdom Hclosed Htotal HQfv Hx Hcont.
  pose proof (proj1 (FExprContIn_iff_let_result_world
    Σ T e Q m Htyped Hdom Hclosed Htotal HQfv) Hcont)
    as [L [HLdom Hbody]].
  set (m1 := let_result_world_on e x m Hfresh Hresult).
  assert (Hdom1 : world_dom (m1 : World) = dom (<[x:=T]> Σ)).
  { subst m1. rewrite let_result_world_on_dom, Hdom, dom_insert_L.
    set_solver. }
  assert (Hclosed1 : world_closed_on (dom (<[x:=T]> Σ)) m1).
  {
    subst m1. eapply let_result_world_on_closed_insert_from_basic; eauto.
    set_solver.
  }
  assert (Htotal_ret : expr_total_on (dom (<[x:=T]> Σ)) (tret (vfvar x)) m1).
  {
    split.
    - simpl. rewrite dom_insert_L. set_solver.
    - intros σx Hσx.
      destruct (let_result_world_on_elim e x m Hfresh Hresult σx Hσx)
        as [σ [vx [Hσ [Hsteps ->]]]].
      assert (Hvx_reg : stale vx = ∅ ∧ is_lc vx).
      {
        eapply steps_closed_result_of_restrict_world.
        - rewrite Hdom. exact (proj1 Htotal).
        - set_solver.
        - eapply typing_tm_lc. exact Htyped.
        - eapply world_closed_on_mono; [exact (proj1 Htotal) | exact Hclosed].
        - exists σ. split; [exact Hσ | reflexivity].
        - replace (store_restrict (store_restrict σ (fv_tm e)) (fv_tm e))
            with (store_restrict σ (fv_tm e)).
          + exact Hsteps.
          + symmetry. apply store_restrict_twice_same.
      }
      exists vx.
      change (m{store_restrict (<[x:=vx]> σ) (dom (<[x:=T]> Σ))}
        (tret (vfvar x)) →* tret vx).
      rewrite (msubst_ret_fvar_lookup_closed_value _ x vx).
      * apply Steps_refl. constructor. exact (proj2 Hvx_reg).
      * exact (proj1 Hvx_reg).
      * apply (store_restrict_lookup_some_2
          (<[x:=vx]> σ : Store) (dom (<[x:=T]> Σ)) x vx).
	        -- change ((<[x:=vx]> σ : Store) !! x = Some vx).
	           rewrite lookup_insert_eq. reflexivity.
	        -- rewrite dom_insert_L. clear. set_solver.
  }
  assert (HQfv_insert : formula_fv Q ⊆ dom (<[x:=T]> Σ)).
  { rewrite dom_insert_L. clear -HQfv. set_solver. }
  apply (proj2 (FExprContIn_iff_let_result_world
    (<[x:=T]> Σ) T (tret (vfvar x)) Q m1
    ltac:(apply TT_Ret; apply VT_FVar; rewrite lookup_insert_eq; reflexivity)
    Hdom1 Hclosed1 Htotal_ret HQfv_insert)).
  exists (L ∪ dom Σ ∪ {[x]} ∪ fv_tm e).
  split; [rewrite dom_insert_L; clear; set_solver |].
  intros ν Hν Hfreshν_ret Hresultν_ret.
  rewrite !not_elem_of_union in Hν.
  destruct Hν as [[[HνL HνΣ] Hνx] Hνe].
  assert (Hfreshν_e : ν ∉ world_dom (m : World)).
  { rewrite Hdom. exact HνΣ. }
  assert (Hresultν_e :
    ∀ σ, (m : World) σ →
      ∃ vx, subst_map (store_restrict σ (fv_tm e)) e →* tret vx).
  {
    eapply expr_total_on_to_fv_result; eauto.
  }
  pose proof (Hbody ν HνL Hfreshν_e Hresultν_e) as Hdirect.
  assert (HQopen_fv :
    formula_fv (formula_open 0 ν Q) ⊆ dom Σ ∪ {[ν]}).
  {
    apply formula_open_fv_subset_env.
    exact HQfv.
  }
  apply (proj2 (res_models_minimal_on
    (dom Σ ∪ {[ν]})
    (let_result_world_on (tret (vfvar x)) ν m1
      Hfreshν_ret Hresultν_ret)
    (formula_open 0 ν Q) HQopen_fv)).
  replace (res_restrict
      (let_result_world_on (tret (vfvar x)) ν m1
        Hfreshν_ret Hresultν_ret)
      (dom Σ ∪ {[ν]}))
    with (let_result_world_on e ν m Hfreshν_e Hresultν_e).
  - eauto 6.
  - subst m1.
    symmetry.
    eapply (let_result_world_on_ret_decompose
      (dom Σ) e x ν m Hfresh Hresult
      Hfreshν_ret Hresultν_ret Hfreshν_e Hresultν_e).
    + exact (proj1 Htotal).
    + eapply typing_tm_lc; eauto 6.
    + exact Hdom.
    + clear -Hx. set_solver.
    + clear -HνΣ Hνx. set_solver.
    + exact Hclosed.
Qed.

Lemma let_result_world_on_erased_basic
    Σ Γ τ e x (m : WfWorld) Hfresh Hresult :
  choice_typing_wf Σ Γ e τ →
  m ⊨ denot_ctx_in_env Σ Γ →
  x ∉ dom (erase_ctx_under Σ Γ) →
  let_result_world_on e x m Hfresh Hresult ⊨
    basic_world_formula
      (erase_ctx_under Σ (CtxComma Γ (CtxBind x τ)))
      (dom (erase_ctx_under Σ (CtxComma Γ (CtxBind x τ)))).
Proof.
  intros Hwf Hctx Hx.
  set (Δ := erase_ctx_under Σ Γ).
  set (Δx := erase_ctx_under Σ (CtxComma Γ (CtxBind x τ))).
  assert (HΔx_dom : dom Δx = dom Δ ∪ {[x]}).
  { subst Δ Δx. apply erase_ctx_under_comma_bind_dom. }
  assert (Hbasic_m : m ⊨ basic_world_formula Δ (dom Δ)).
  { subst Δ. apply denot_ctx_in_env_erased_basic. exact Hctx. }
  assert (Hcover_m : dom Δ ⊆ world_dom (m : World)).
  { eapply basic_world_formula_dom_subset. exact Hbasic_m. }
  assert (HΔx_env : Δx = <[x := erase_ty τ]> Δ).
  { subst Δ Δx. apply erase_ctx_under_comma_bind_env_fresh. exact Hx. }
  eapply res_models_atom_intro.
  - change (formula_scoped_in_world ∅
      (let_result_world_on e x m Hfresh Hresult)
      (basic_world_formula Δx (dom Δx))).
    unfold formula_scoped_in_world.
    rewrite dom_empty_L, basic_world_formula_fv.
    rewrite HΔx_dom. simpl. set_solver.
  - unfold basic_world_formula, basic_world_lqual, logic_qualifier_denote,
      lqual_fvars. simpl. rewrite lvars_fv_of_atoms.
    split.
    + simpl. rewrite HΔx_dom. simpl. set_solver.
    + intros σr Hσr z T v Hz HΣz Hlookup.
      simpl in Hσr.
      destruct Hσr as [σx [Hσx Hrestrict]].
      destruct (let_result_world_on_elim e x m Hfresh Hresult σx Hσx)
        as [σ [vx [Hσ [Hsteps ->]]]].
      rewrite <- Hrestrict in Hlookup.
      apply store_restrict_lookup_some in Hlookup as [_ Hlookup].
      destruct (decide (z = x)) as [->|Hzx].
      * rewrite (lookup_insert_eq σ x vx) in Hlookup. inversion Hlookup; subst v.
        rewrite HΔx_env in HΣz.
        rewrite lookup_insert_eq in HΣz. inversion HΣz; subst T.
        eapply choice_typing_wf_result_typed_restrict_in_ctx; eauto.
        subst Δ.
        assert (Hfv : fv_tm e ⊆ dom (erase_ctx_under Σ Γ)).
        { eapply choice_typing_wf_fv_tm_subset_erase_dom. exact Hwf. }
        assert (Hclosed :
          closed_env (store_restrict σ (dom (erase_ctx_under Σ Γ)))).
        {
          destruct Hwf as [Hty _].
          pose proof (wf_ctx_under_basic Σ Γ (wf_choice_ty_under_ctx Σ Γ τ Hty))
            as HbasicΓ.
          destruct (denot_ctx_in_env_store_erased_typed
            Σ Γ m σ HbasicΓ Hctx Hσ) as [Hclosed0 _].
          assert (Hdom_erase :
            dom (erase_ctx_under Σ Γ) = dom Σ ∪ ctx_dom Γ).
          { apply erase_ctx_under_dom_basic. exact HbasicΓ. }
          rewrite Hdom_erase. exact Hclosed0.
        }
        rewrite <- (subst_map_restrict_to_fv_from_superset e
          (dom (erase_ctx_under Σ Γ)) σ Hfv Hclosed).
        exact Hsteps.
      * rewrite HΔx_env in HΣz.
        rewrite lookup_insert_ne in HΣz by congruence.
        rewrite (lookup_insert_ne σ x z vx) in Hlookup by congruence.
        assert (HzΔ : z ∈ dom Δ).
        { subst Δ. subst Δx. rewrite erase_ctx_under_comma_bind_dom in Hz.
          set_solver. }
        pose proof (basic_world_formula_store_restrict_typed
          Δ (dom Δ) m σ Hbasic_m Hσ) as Htyped.
        eapply Htyped; eauto.
        apply store_restrict_lookup_some_2; [exact Hlookup | exact HzΔ].
Qed.

(** Result-binding compatibility for the let-result world.

    If [m] satisfies [τ] for the expression [e], then the world obtained by
    adding a fresh coordinate [x] containing exactly the possible results of
    [e] satisfies [τ] for [return x].

    The constructor-specific work is isolated in the body transport lemma
    below; this wrapper only rebuilds the standard denotation obligations. *)
Lemma denot_ty_body_let_result_bound
    X Σ τ e x (m : WfWorld) Hfresh Hresult :
  basic_choice_ty (dom Σ) τ →
  fv_tm e ⊆ X →
  x ∉ X ∪ fv_cty τ ∪ fv_tm e →
  m ⊨ basic_world_formula Σ (dom Σ) →
  m ⊨ denot_ty_on Σ τ e →
  let_result_world_on e x m Hfresh Hresult ⊨
    denot_ty_body (<[x := erase_ty τ]> Σ) τ (tret (vfvar x)).
(* This is the remaining total route bridge.  A previous attempt tried to
   recover [world_dom m = dom Σ] from [m ⊨ denot_ty_on Σ τ e], but that is too
   strong: the ambient world may contain extra coordinates.  The proof should
   either work under [dom Σ ⊆ world_dom m] directly, or restrict to [dom Σ]
   before applying exact-domain result-continuation lemmas. *)
Admitted.

Lemma denot_ty_on_let_result_bound
    X Σ τ e x (m : WfWorld) Hfresh Hresult :
  basic_choice_ty (dom Σ) τ →
  fv_tm e ⊆ X →
  x ∉ X ∪ fv_cty τ ∪ fv_tm e →
  m ⊨ basic_world_formula Σ (dom Σ) →
  m ⊨ denot_ty_on Σ τ e →
  let_result_world_on e x m Hfresh Hresult ⊨
    denot_ty_on (<[x := erase_ty τ]> Σ) τ (tret (vfvar x)).
Proof.
  intros Hbasic HfvX Hx Hbasic_world Hmodel.
  pose proof (denot_ty_basic_of_formula _ _ _ _ Hmodel)
    as [_ Htyped].
  assert (Hdom_world : dom Σ ⊆ world_dom (m : World)).
  { eapply basic_world_formula_dom_subset. exact Hbasic_world. }
  assert (Hxm : x ∉ dom Σ).
  { intros Hxin. apply Hfresh. apply Hdom_world. exact Hxin. }
  assert (Hclosed : world_closed_on (dom Σ) m).
  { eapply denot_ty_world_closed_on_of_formula. exact Hmodel. }
  eapply denot_ty_intro.
  - eapply basic_choice_ty_mono; [| exact Hbasic].
    rewrite dom_insert_L. set_solver.
  - apply TT_Ret. apply VT_FVar. rewrite lookup_insert_eq. reflexivity.
  - eapply let_result_world_on_closed_insert_from_basic_subset; eauto.
  - split.
    + simpl. rewrite dom_insert_L. set_solver.
    + intros σx Hσx.
      destruct (let_result_world_on_elim e x m Hfresh Hresult σx Hσx)
        as [σ [vx [Hσ [Hsteps ->]]]].
      assert (Hvx_reg : stale vx = ∅ ∧ is_lc vx).
      {
        eapply steps_closed_result_of_restrict_world.
        - intros z Hz. apply Hdom_world.
          eapply basic_typing_contains_fv_tm; [exact Htyped | exact Hz].
        - set_solver.
        - eapply typing_tm_lc. exact Htyped.
        - eapply world_closed_on_mono; [| exact Hclosed].
          eapply basic_typing_contains_fv_tm. exact Htyped.
        - exists σ. split; [exact Hσ | reflexivity].
        - replace (store_restrict (store_restrict σ (fv_tm e)) (fv_tm e))
            with (store_restrict σ (fv_tm e)).
          + exact Hsteps.
          + symmetry. apply store_restrict_twice_same.
      }
      exists vx.
      change (m{store_restrict (<[x:=vx]> σ) (dom (<[x:=erase_ty τ]> Σ))}
        (tret (vfvar x)) →* tret vx).
      rewrite (msubst_ret_fvar_lookup_closed_value _ x vx).
      * apply Steps_refl. constructor. exact (proj2 Hvx_reg).
      * exact (proj1 Hvx_reg).
      * apply (store_restrict_lookup_some_2
          (<[x:=vx]> σ : Store) (dom (<[x:=erase_ty τ]> Σ)) x vx).
	        -- change ((<[x:=vx]> σ : Store) !! x = Some vx).
	           rewrite lookup_insert_eq. reflexivity.
	        -- rewrite dom_insert_L. clear. set_solver.
  - eapply denot_ty_body_let_result_bound; eauto.
  - rewrite let_result_world_on_dom, dom_insert_L.
    set_solver.
Qed.

Lemma let_result_world_on_denot_ty_bound
    Σ Γ τ e x (m : WfWorld) Hfresh Hresult :
  choice_typing_wf Σ Γ e τ →
  m ⊨ denot_ctx_in_env Σ Γ →
  m ⊨ denot_ty_in_ctx_under Σ Γ τ e →
  x ∉ dom (erase_ctx_under Σ Γ) ∪ fv_cty τ ∪ fv_tm e →
  let_result_world_on e x m Hfresh Hresult ⊨
    denot_ty_on
      (<[x := erase_ty τ]> (erase_ctx_under Σ Γ))
      τ (tret (vfvar x)).
Proof.
  intros Hwf Hm Hτ Hx.
  eapply (denot_ty_on_let_result_bound
    (dom (erase_ctx_under Σ Γ)) (erase_ctx_under Σ Γ) τ e x m Hfresh Hresult);
    eauto 6 using choice_typing_wf_basic_choice_ty_erased,
      choice_typing_wf_fv_tm_subset_erase_dom, denot_ctx_in_env_erased_basic.
Qed.

Lemma let_result_world_on_denot_ctx_in_env
    Σ Γ τ e x (m : WfWorld) Hfresh Hresult :
  choice_typing_wf Σ Γ e τ →
  m ⊨ denot_ctx_in_env Σ Γ →
  m ⊨ denot_ty_in_ctx_under Σ Γ τ e →
  x ∉ dom (erase_ctx_under Σ Γ) ∪ fv_cty τ ∪ fv_tm e →
  let_result_world_on e x m Hfresh Hresult ⊨
    denot_ctx_in_env Σ (CtxComma Γ (CtxBind x τ)).
Proof.
  intros Hwf Hm Hτ Hx.
  unfold denot_ctx_in_env.
  apply res_models_and_intro_from_models.
  - eapply res_models_kripke.
    + apply let_result_world_on_le.
    + eapply denot_ctx_in_env_basic; eauto.
  - apply res_models_and_intro_from_models.
    + eapply let_result_world_on_erased_basic; eauto. set_solver.
    + apply denot_ctx_under_comma. split.
      * apply denot_ctx_in_env_ctx.
        eapply let_result_world_on_preserves_context; eauto 6.
      * simpl.        eapply let_result_world_on_denot_ty_bound; eauto.
Qed.

Lemma let_result_world_on_fresh_for_bound
    Σ Γ τ e x (m : WfWorld) :
  choice_typing_wf Σ Γ e τ →
  m ⊨ denot_ctx_in_env Σ Γ →
  expr_total_on (dom (erase_ctx_under Σ Γ)) e m →
  x ∉ world_dom (m : World) →
  x ∉ dom (erase_ctx_under Σ Γ) ∪ fv_cty τ ∪ fv_tm e.
Proof.
  intros Hwf Hm Htotal Hfresh.
  destruct Htotal as [Hfv_e _].
  assert (Hfv_τ : fv_cty τ ⊆ dom (erase_ctx_under Σ Γ)).
  {
    exact (choice_typing_wf_fv_cty_subset_erase_dom Σ Γ e τ Hwf).
  }
  assert (Hdom_world : dom (erase_ctx_under Σ Γ) ⊆ world_dom (m : World)).
  {
    pose proof (res_models_with_store_fuel_scoped
      (formula_measure (denot_ctx_in_env Σ Γ)) ∅ m
      (denot_ctx_in_env Σ Γ) Hm) as Hscope.
    unfold formula_scoped_in_world in Hscope.
    intros z Hz. apply Hscope.
    apply elem_of_union. right.
    apply denot_ctx_in_env_dom_subset_formula_fv.
    destruct Hwf as [Hwfτ _].
    replace (dom Σ ∪ ctx_dom Γ) with (dom (erase_ctx_under Σ Γ)).
    - exact Hz.
    - symmetry.
      pose proof (wf_ctx_under_basic Σ Γ (wf_choice_ty_under_ctx Σ Γ τ Hwfτ))
        as Hctx.      rewrite dom_union_L, (basic_ctx_erase_dom (dom Σ) Γ Hctx).
      reflexivity.
  }
  apply not_elem_of_union. split.
  - apply not_elem_of_union. split.
    + intros Hbad. apply Hfresh. apply Hdom_world. exact Hbad.
    + intros Hbad. apply Hfresh. apply Hdom_world. apply Hfv_τ. exact Hbad.
  - intros Hbad. apply Hfresh. apply Hdom_world. apply Hfv_e. exact Hbad.
Qed.

Lemma tlet_body_ctx_from_result_world
    (Σ : gmap atom ty) (Γ : ctx) (τ1 : choice_ty) e1 x
    (m : WfWorld)
    (Hfresh : x ∉ world_dom (m : World))
    (Hresult : ∀ σ, (m : World) σ →
      ∃ vx, subst_map (store_restrict σ (fv_tm e1)) e1 →* tret vx) :
  erase_ctx_under Σ Γ ⊢ₑ e1 ⋮ erase_ty τ1 →
  m ⊨ denot_ctx_in_env Σ Γ →
  denot_ty_total_model_in_ctx_under Σ Γ τ1 e1 m →
  let_result_world_on e1 x m Hfresh Hresult ⊨
    denot_ctx_in_env Σ (CtxComma Γ (CtxBind x τ1)).
Proof.
  intros Herase Hm Hmodel.
  eapply let_result_world_on_denot_ctx_in_env.
  - eapply tlet_e1_choice_typing_wf; eauto.
  - exact Hm.
  - exact (denot_ty_total_model_formula Σ Γ τ1 e1 m Hmodel).
  - eapply let_result_world_on_fresh_for_bound.
    + eapply tlet_e1_choice_typing_wf; eauto.
    + exact Hm.
    + exact (denot_ty_total_model_total Σ Γ τ1 e1 m Hmodel).
    + exact Hfresh.
Qed.

Lemma lc_env_restrict σ X :
  lc_env σ →
  lc_env (store_restrict σ X).
Proof.
  unfold lc_env. intros Hlc.
  apply map_Forall_lookup_2. intros y v Hlookup.
  apply store_restrict_lookup_some in Hlookup as [_ Hlookup].
  exact (map_Forall_lookup_1 _ _ _ _ Hlc Hlookup).
Qed.

Lemma expr_total_on_tlete_elim_e1_strong X e1 e2 (m : WfWorld) :
  expr_total_on X (tlete e1 e2) m →
  expr_total_on X e1 m.
Proof.
  intros [Hfv Htotal].
  split; [simpl in Hfv; set_solver |].
  intros σ Hσ.
  destruct (Htotal σ Hσ) as [v Hsteps].
  change (m{store_restrict σ X} (tlete e1 e2) →* tret v) in Hsteps.
  rewrite msubst_lete in Hsteps.
  apply reduction_lete in Hsteps as [vx [Hsteps1 _]].
  exists vx. exact Hsteps1.
Qed.

Lemma expr_total_on_tlete_elim_body_strong
    X e1 e2 x (m : WfWorld) Hfresh Hresult :
  X ⊆ world_dom (m : World) →
  x ∉ X →
  x ∉ fv_tm e2 →
  world_closed_on X m →
  lc_tm (tlete e1 e2) →
  expr_total_on X (tlete e1 e2) m →
  expr_total_on (X ∪ {[x]}) (e2 ^^ x)
    (let_result_world_on e1 x m Hfresh Hresult).
Proof.
  intros HXdom HxX Hxe2 Hclosed Hlclet [Hfv Htotal].
  apply lc_lete_iff_body in Hlclet as [Hlc1 Hbody2].
  split.
  - simpl in Hfv.
    pose proof (open_fv_tm e2 (vfvar x) 0) as Hopen_fv.
    simpl in Hopen_fv. set_solver.
  - intros σx Hσx.
    destruct (let_result_world_on_elim e1 x m Hfresh Hresult σx Hσx)
      as [σ [vx [Hσ [Hsteps_fv ->]]]].
    assert (HclosedX : store_closed (store_restrict σ X)).
    { exact (Hclosed σ Hσ). }
    assert (Hfv1 : fv_tm e1 ⊆ X) by (simpl in Hfv; set_solver).
    assert (HstepsX : subst_map (store_restrict σ X) e1 →* tret vx).
    {
      rewrite <- (subst_map_restrict_to_fv_from_superset e1 X σ Hfv1
        (proj1 HclosedX)).
      exact Hsteps_fv.
    }
    assert (Hvx_closed : stale vx = ∅ ∧ is_lc vx).
    {
      eapply steps_closed_result; [| exact HstepsX].
      apply msubst_closed_tm.
      - exact HclosedX.
      - exact Hlc1.
      - change (fv_tm e1 ⊆ dom (store_restrict σ X)).
        rewrite store_restrict_dom.
        pose proof (wfworld_store_dom m σ Hσ) as Hdomσ.
        set_solver.
    }
    destruct (Htotal σ Hσ) as [vout Hlet].
    change (m{store_restrict σ X} (tlete e1 e2) →* tret vout) in Hlet.
    rewrite msubst_lete in Hlet.
    apply reduction_lete in Hlet as [vx' [HstepsX' Hbody_steps]].
    assert (vx' = vx) as ->.
    { eapply steps_result_unique; eauto. }
    rewrite store_restrict_insert_fresh_union.
    + rewrite (msubst_open_body_result X σ e2 x vx)
        by (try exact HxX; try exact Hxe2; try exact (proj1 HclosedX);
            try exact (proj1 Hvx_closed); try exact (proj2 Hvx_closed);
            try exact (proj2 HclosedX)).
      exists vout. exact Hbody_steps.
    + eapply store_lookup_none_of_dom.
      * exact (wfworld_store_dom m σ Hσ).
      * exact Hfresh.
    + exact HxX.
Qed.

Lemma expr_total_on_tlete_intro_strong
    X e1 e2 x (m : WfWorld) Hfresh Hresult :
  X ⊆ world_dom (m : World) →
  x ∉ X →
  x ∉ fv_tm e2 →
  world_closed_on X m →
  lc_tm (tlete e1 e2) →
  expr_total_on X e1 m →
  expr_total_on (X ∪ {[x]}) (e2 ^^ x)
    (let_result_world_on e1 x m Hfresh Hresult) →
  expr_total_on X (tlete e1 e2) m.
Proof.
  intros HXdom HxX Hxe2 Hclosed Hlclet [Hfv1 Htotal1]
    [Hfv2 Htotal2].
  apply lc_lete_iff_body in Hlclet as [Hlc1 Hbody2].
  split.
  - simpl.
    intros z Hz.
    apply elem_of_union in Hz as [Hz | Hz].
    + apply Hfv1. exact Hz.
    + assert (Hzopen : z ∈ fv_tm (e2 ^^ x)).
      { apply open_fv_tm'. exact Hz. }
      specialize (Hfv2 z Hzopen).
      simpl in Hfv2.
      apply elem_of_union in Hfv2 as [HzX | Hzx]; [exact HzX |].
      apply elem_of_singleton in Hzx. subst z. contradiction.
  - intros σ Hσ.
    destruct (Htotal1 σ Hσ) as [vx HstepsX].
    assert (Hsteps_fv :
      subst_map (store_restrict σ (fv_tm e1)) e1 →* tret vx).
    {
      rewrite (subst_map_restrict_to_fv_from_superset e1 X σ
        Hfv1 (proj1 (Hclosed σ Hσ))).
      exact HstepsX.
    }
    assert (Hvx_closed : stale vx = ∅ ∧ is_lc vx).
    {
      eapply steps_closed_result; [| exact HstepsX].
      apply msubst_closed_tm.
      - exact (Hclosed σ Hσ).
      - exact Hlc1.
      - change (fv_tm e1 ⊆ dom (store_restrict σ X)).
        rewrite store_restrict_dom.
        pose proof (wfworld_store_dom m σ Hσ) as Hdomσ.
        set_solver.
    }
    pose proof (Htotal2 (<[x:=vx]> σ)) as Hbody_total.
    assert ((let_result_world_on e1 x m Hfresh Hresult : World)
      (<[x:=vx]> σ)) as Hσx.
    { exists σ, vx. split; [exact Hσ | split; [exact Hsteps_fv | reflexivity]]. }
    specialize (Hbody_total Hσx) as [vout Hbody_steps].
    exists vout.
    change (m{store_restrict σ X} (tlete e1 e2) →* tret vout).
    rewrite msubst_lete.
    eapply reduction_lete_intro.
    + apply body_tm_msubst.
      * exact (proj1 (Hclosed σ Hσ)).
      * exact (proj2 (Hclosed σ Hσ)).
      * exact Hbody2.
    + exact HstepsX.
    + rewrite store_restrict_insert_fresh_union in Hbody_steps.
      * rewrite (msubst_open_body_result X σ e2 x vx
          HxX Hxe2 (proj1 (Hclosed σ Hσ))
          (proj1 Hvx_closed) (proj2 Hvx_closed)
          (proj2 (Hclosed σ Hσ))) in Hbody_steps.
        exact Hbody_steps.
      * eapply store_lookup_none_of_dom.
        -- apply wfworld_store_dom. exact Hσ.
        -- exact Hfresh.
      * exact HxX.
Qed.

Lemma basic_typing_tlete_body_for_fresh Γ e1 e2 T1 T2 x :
  Γ ⊢ₑ e1 ⋮ T1 →
  Γ ⊢ₑ tlete e1 e2 ⋮ T2 →
  x ∉ dom Γ ∪ fv_tm e2 →
  <[x := T1]> Γ ⊢ₑ e2 ^^ x ⋮ T2.
Proof.
  intros He1 Hlet Hxfresh.
  inversion Hlet; subst.
  assert (T0 = T1) as ->.
  { eapply basic_typing_unique_tm; eauto. }
  pose (y := fresh_for (L ∪ dom Γ ∪ fv_tm e2 ∪ {[x]})).
  assert (Hy : y ∉ L ∪ dom Γ ∪ fv_tm e2 ∪ {[x]})
    by (subst y; apply fresh_for_not_in).
  match goal with
  | Hopen : ∀ z : atom, z ∉ L → <[z:=T1]> Γ ⊢ₑ e2 ^^ z ⋮ T2 |- _ =>
      pose proof (Hopen y ltac:(set_solver)) as Hybody
  end.
  eapply basic_typing_open_tm with (x := y) (U := T1).
  - set_solver.
  - constructor. apply lookup_insert_eq.
  - replace (<[y:=T1]> (<[x:=T1]> Γ))
      with (<[x:=T1]> (<[y:=T1]> Γ))
      by (rewrite insert_insert_ne by set_solver; reflexivity).
    eapply basic_typing_weaken_insert_tm.
    + rewrite dom_insert_L. set_solver.
    + exact Hybody.
Qed.
