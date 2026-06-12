(** * Denotation.TypeEquivFiberTransport

    Application and opened-result transport lemmas built on top of
    [TypeEquivTerm].  Kept separate so the core term/fiber definitions stay
    small and lower-level. *)

From Denotation Require Import Notation TypeDenote TypeEquivCore TypeEquivTerm.
From CoreLang Require Import StrongNormalization.

Section TypeDenote.

Lemma tm_equiv_tapp_value_arg_eq_on
    (m : WfWorldT) X e vx1 vx2 :
  fv_tm (tapp_tm e vx1) ∪ fv_tm (tapp_tm e vx2) ⊆ X ->
  wfworld_closed_on X m ->
  lc_value vx1 ->
  lc_value vx2 ->
  (forall σ,
    (m : WorldT) σ ->
    m{store_restrict σ X} vx1 = m{store_restrict σ X} vx2) ->
  tm_equiv_on m (tapp_tm e vx1) (tapp_tm e vx2).
Proof.
  intros HfvX Hclosed Hvx1 Hvx2 Heq σ v Hσ.
  assert (HσX_closed : store_closed (store_restrict σ X)).
  { exact (Hclosed σ Hσ). }
  assert (Hfv_app1 : fv_tm (tapp_tm e vx1) ⊆ X) by better_set_solver.
  assert (Hfv_app2 : fv_tm (tapp_tm e vx2) ⊆ X) by better_set_solver.
  pose proof (tm_eval_in_store_tapp_tm_arg_eq
    (store_restrict σ X) e vx1 vx2 v
    HσX_closed Hvx1 Hvx2 (Heq σ Hσ)) as Hequiv.
  split.
  - intros Heval.
    apply (proj1 (tm_eval_in_store_restrict_fv_subset
      σ (tapp_tm e vx2) v X Hfv_app2)).
    apply (proj1 Hequiv).
    apply (proj2 (tm_eval_in_store_restrict_fv_subset
      σ (tapp_tm e vx1) v X Hfv_app1)).
    exact Heval.
  - intros Heval.
    apply (proj1 (tm_eval_in_store_restrict_fv_subset
      σ (tapp_tm e vx1) v X Hfv_app1)).
    apply (proj2 Hequiv).
    apply (proj2 (tm_eval_in_store_restrict_fv_subset
      σ (tapp_tm e vx2) v X Hfv_app2)).
      exact Heval.
Qed.

Lemma tm_total_equiv_tapp_value_arg_eq_on
    (m : WfWorldT) X e vx1 vx2 :
  fv_tm (tapp_tm e vx1) ∪ fv_tm (tapp_tm e vx2) ⊆ X ->
  wfworld_closed_on X m ->
  lc_tm e ->
  lc_value vx1 ->
  lc_value vx2 ->
  (forall σ,
    (m : WorldT) σ ->
    m{store_restrict σ X} vx1 = m{store_restrict σ X} vx2) ->
  tm_total_equiv_on m (tapp_tm e vx1) (tapp_tm e vx2).
Proof.
  intros HfvX Hclosed Hlc_e Hvx1 Hvx2 Heq σ Hσ.
  assert (HσX_closed : store_closed (store_restrict σ X)).
  { exact (Hclosed σ Hσ). }
  assert (Hfv_app1 : fv_tm (tapp_tm e vx1) ⊆ X) by better_set_solver.
  assert (Hfv_app2 : fv_tm (tapp_tm e vx2) ⊆ X) by better_set_solver.
  pose proof (tm_must_terminating_tapp_tm_arg_eq
    (store_restrict σ X) e vx1 vx2
    HσX_closed Hvx1 Hvx2 (Heq σ Hσ)) as Hequiv.
  assert (Hsrc_agree :
      store_restrict σ (fv_tm (tapp_tm e vx1)) =
      store_restrict (store_restrict σ X) (fv_tm (tapp_tm e vx1))).
  { rewrite storeA_restrict_twice_subset; [reflexivity|exact Hfv_app1]. }
  assert (Htgt_agree :
      store_restrict σ (fv_tm (tapp_tm e vx2)) =
      store_restrict (store_restrict σ X) (fv_tm (tapp_tm e vx2))).
  { rewrite storeA_restrict_twice_subset; [reflexivity|exact Hfv_app2]. }
  assert (Hlc_src : lc_tm (tapp_tm e vx1)).
  { apply lc_tapp_tm; [exact Hlc_e|exact Hvx1]. }
  assert (Hlc_tgt : lc_tm (tapp_tm e vx2)).
  { apply lc_tapp_tm; [exact Hlc_e|exact Hvx2]. }
  pose proof (tm_must_terminating_agree_on_fv σ (store_restrict σ X)
    (tapp_tm e vx1) Hlc_src Hsrc_agree) as Hsrc_restrict.
  pose proof (tm_must_terminating_agree_on_fv σ (store_restrict σ X)
    (tapp_tm e vx2) Hlc_tgt Htgt_agree) as Htgt_restrict.
  split; intros Htotal.
  - apply (proj2 Htgt_restrict).
    apply (proj1 Hequiv).
    apply (proj1 Hsrc_restrict). exact Htotal.
  - apply (proj2 Hsrc_restrict).
    apply (proj2 Hequiv).
    apply (proj1 Htgt_restrict). exact Htotal.
Qed.

Lemma expr_result_formula_ret_value_inst_eq_on
    (m : WfWorldT) X vx z :
  z ∈ X ->
  fv_value vx ⊆ X ->
  wfworld_closed_on X m ->
  lc_value vx ->
  m ⊨ expr_result_formula (tret vx) (LVFree z) ->
  forall σ,
    (m : WorldT) σ ->
    m{store_restrict σ X} (vfvar z) =
    m{store_restrict σ X} vx.
Proof.
  intros HzX Hfvx Hclosed Hvx Hres σ Hσ.
  pose proof (expr_result_formula_to_atom_world
    (tret vx) (LVFree z) m Hres) as Hres_world.
  destruct Hres_world as [_ [_ Hstores]].
  specialize (Hstores (lstore_lift_free σ)).
  assert (Hlift :
      worldA_stores (res_lift_free m : LWorldT) (lstore_lift_free σ)).
  { exists σ. split; [exact Hσ | reflexivity]. }
  destruct (Hstores Hlift) as [_ [vz [Hz_lookup Heval_full]]].
  assert (HclosedX : store_closed (store_restrict σ X)).
  { exact (Hclosed σ Hσ). }
  assert (Hz_lookup_restrict :
      (store_restrict σ X : StoreT) !! z = Some vz).
  {
    apply storeA_restrict_lookup_some_2; [|exact HzX].
    change (((lstore_lift_free σ : LStoreT) : gmap logic_var value) !!
      LVFree z = Some vz) in Hz_lookup.
    rewrite lstore_lift_free_lookup_free in Hz_lookup.
    exact Hz_lookup.
  }
  assert (Heval_restrict :
      tm_eval_in_store (store_restrict σ X) (tret vx) vz).
  {
    pose proof (tm_eval_in_store_restrict_fv_subset
      σ (tret vx) vz X ltac:(cbn [fv_tm]; exact Hfvx)) as Hiff.
    apply (proj2 Hiff). exact Heval_full.
  }
  pose proof (tm_eval_in_store_ret_value_inv
    (store_restrict σ X) vx vz HclosedX Hvx Heval_restrict)
    as Hvz.
  rewrite (msubst_fvar_lookup_closed
    (store_restrict σ X) z vz)
    by (exact (proj1 HclosedX) || exact Hz_lookup_restrict).
  exact Hvz.
Qed.

Lemma tm_equiv_tapp_value_arg_result_alias_on
    (m : WfWorldT) X e vx z :
  fv_tm (tapp_tm e (vfvar z)) ∪ fv_tm (tapp_tm e vx) ⊆ X ->
  z ∈ X ->
  fv_value vx ⊆ X ->
  wfworld_closed_on X m ->
  lc_value vx ->
  m ⊨ expr_result_formula (tret vx) (LVFree z) ->
  tm_equiv_on m (tapp_tm e (vfvar z)) (tapp_tm e vx).
Proof.
  intros HfvX HzX Hfvx Hclosed Hvx Hres.
  assert (Heq :
      forall σ,
        (m : WorldT) σ ->
        m{store_restrict σ X} (vfvar z) =
        m{store_restrict σ X} vx).
  { eapply expr_result_formula_ret_value_inst_eq_on; eauto. }
  exact (tm_equiv_tapp_value_arg_eq_on
    m X e (vfvar z) vx HfvX Hclosed ltac:(constructor) Hvx Heq).
Qed.

Lemma tm_total_equiv_tapp_value_arg_result_alias_on
    (m : WfWorldT) X e vx z :
  fv_tm (tapp_tm e (vfvar z)) ∪ fv_tm (tapp_tm e vx) ⊆ X ->
  z ∈ X ->
  fv_value vx ⊆ X ->
  wfworld_closed_on X m ->
  lc_tm e ->
  lc_value vx ->
  m ⊨ expr_result_formula (tret vx) (LVFree z) ->
  tm_total_equiv_on m (tapp_tm e (vfvar z)) (tapp_tm e vx).
Proof.
  intros HfvX HzX Hfvx Hclosed Hlc_e Hvx Hres.
  assert (Heq :
      forall σ,
        (m : WorldT) σ ->
        m{store_restrict σ X} (vfvar z) =
        m{store_restrict σ X} vx).
  { eapply expr_result_formula_ret_value_inst_eq_on; eauto. }
  exact (tm_total_equiv_tapp_value_arg_eq_on
    m X e (vfvar z) vx HfvX Hclosed Hlc_e ltac:(constructor) Hvx Heq).
Qed.

Lemma tm_equiv_tapp_value_arg_result_alias
    (m : WfWorldT) e vx z :
  wfworld_closed_on
    (fv_tm (tapp_tm e (vfvar z)) ∪ fv_tm (tapp_tm e vx)) m ->
  lc_value vx ->
  m ⊨ expr_result_formula (tret vx) (LVFree z) ->
  tm_equiv_on m (tapp_tm e (vfvar z)) (tapp_tm e vx).
Proof.
  intros Hclosed Hvx Hres.
  eapply (tm_equiv_tapp_value_arg_result_alias_on
    m (fv_tm (tapp_tm e (vfvar z)) ∪ fv_tm (tapp_tm e vx)) e vx z).
  - intros a Ha. exact Ha.
  - apply elem_of_union_l.
    rewrite fv_tapp_tm.
    cbn [fv_tm fv_value].
    apply elem_of_union_r.
    apply elem_of_singleton_2. reflexivity.
  - intros a Ha.
    apply elem_of_union_r.
    rewrite fv_tapp_tm.
    cbn [fv_tm].
    apply elem_of_union_r. exact Ha.
  - exact Hclosed.
  - exact Hvx.
  - exact Hres.
Qed.

Lemma tm_total_equiv_tapp_value_arg_result_alias
    (m : WfWorldT) e vx z :
  wfworld_closed_on
    (fv_tm (tapp_tm e (vfvar z)) ∪ fv_tm (tapp_tm e vx)) m ->
  lc_tm e ->
  lc_value vx ->
  m ⊨ expr_result_formula (tret vx) (LVFree z) ->
  tm_total_equiv_on m (tapp_tm e (vfvar z)) (tapp_tm e vx).
Proof.
  intros Hclosed Hlc_e Hvx Hres.
  eapply (tm_total_equiv_tapp_value_arg_result_alias_on
    m (fv_tm (tapp_tm e (vfvar z)) ∪ fv_tm (tapp_tm e vx)) e vx z).
  - intros a Ha. exact Ha.
  - apply elem_of_union_l.
    rewrite fv_tapp_tm.
    cbn [fv_tm fv_value].
    apply elem_of_union_r.
    apply elem_of_singleton_2. reflexivity.
  - intros a Ha.
    apply elem_of_union_r.
    rewrite fv_tapp_tm.
    cbn [fv_tm].
    apply elem_of_union_r. exact Ha.
  - exact Hclosed.
  - exact Hlc_e.
  - exact Hvx.
  - exact Hres.
Qed.

Lemma tm_lvars_tapp_tm_fvar_without_arg_shift_lc e y :
  lc_tm e ->
  tm_lvars (tapp_tm e (vfvar y)) ∖ {[LVFree y]} ⊆
    lvars_shift_from 0 (tm_lvars e).
Proof.
  intros Hlc.
  rewrite (tm_lvars_lc_eq_atoms e Hlc).
  intros v Hv.
  apply elem_of_difference in Hv as [Hv Hvy].
  rewrite tm_lvars_tapp_tm_fvar in Hv.
  apply elem_of_union in Hv as [Hv|Hv].
  - rewrite (tm_lvars_lc_eq_atoms e Hlc) in Hv.
    unfold lvars_shift_from.
    apply elem_of_map.
    exists v. split; [|exact Hv].
    unfold lvars_of_atoms in Hv.
    apply elem_of_map in Hv as [x [-> _]].
    reflexivity.
  - rewrite elem_of_singleton in Hv. subst v.
    exfalso. apply Hvy. set_solver.
Qed.

Lemma basic_tm_has_ltype_tapp_tm_lvar
    (Σ : lty_env) ef vx Tx T :
  lc_lvars (dom (Σ : gmap logic_var ty)) ->
  basic_tm_has_ltype Σ ef (Tx →ₜ T) ->
  basic_value_has_ltype Σ vx Tx ->
  basic_tm_has_ltype Σ (tapp_tm ef vx) T.
Proof.
  intros HlcΣ Hef Hvx.
  pose proof (basic_value_has_ltype_lc Σ vx Tx HlcΣ Hvx) as Hlc_vx.
  unfold tapp_tm.
  eapply BTT_Let with (L := lvars_fv (dom (Σ : gmap logic_var ty)) ∪ fv_value vx).
  - exact Hef.
  - intros z Hz.
    cbn [open_one open_tm_atom_inst open_tm].
    assert (Hshift_lc : lc_value (value_shift 0 vx)).
    { rewrite value_shift_lc_id by exact Hlc_vx. exact Hlc_vx. }
    rewrite (open_rec_lc_value (value_shift 0 vx) Hshift_lc 0 (vfvar z)).
    rewrite value_shift_lc_id by exact Hlc_vx.
    eapply BTT_App.
    + eapply BVT_FVar.
      apply lty_env_open_one_typed_bind_lookup_current.
    + eapply basic_value_has_ltype_weaken; [exact Hvx|].
      apply map_subseteq_spec. intros v U Hlook.
      destruct v as [n|a].
      * exfalso.
        assert (LVBound n ∈ dom Σ) as Hdom.
        { eapply elem_of_dom_2. exact Hlook. }
        exact (HlcΣ (LVBound n) Hdom).
      * rewrite lty_env_open_one_typed_bind_lookup_free_ne.
        -- exact Hlook.
        -- intros Haz. subst a.
           apply Hz. apply elem_of_union_l.
           apply lvars_fv_elem. eapply elem_of_dom_2. exact Hlook.
Qed.

Lemma basic_value_has_ltype_open_result_target_arg
    (Σ : lty_env) τx τr e y :
  basic_value_has_ltype
    (relevant_env
      (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
      (cty_open 0 y τr) (tapp_tm e (vfvar y)))
    (vfvar y) (erase_ty τx).
Proof.
  eapply BVT_FVar.
  unfold relevant_env, lty_env_restrict_lvars.
  apply storeA_restrict_lookup_some_2.
  - apply lty_env_open_one_typed_bind_lookup_current.
  - unfold relevant_lvars, tapp_tm.
    cbn [context_ty_lvars tm_lvars tm_lvars_at value_lvars_at].
    set_solver.
Qed.

Lemma tm_equiv_full_world_extend_fresh
    (m my : WfWorldT) y e1 e2 :
  tm_equiv_on m e1 e2 ->
  fv_tm e1 ∪ fv_tm e2 ⊆ world_dom (m : WorldT) ->
  y ∉ fv_tm e1 ∪ fv_tm e2 ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_restrict my (world_dom (m : WorldT)) = m ->
  tm_equiv_on my e1 e2.
Proof.
  intros Heq Hfv _ _ Hrestrict σ v Hσ.
  assert (Hσm :
      (m : WorldT) (store_restrict σ (world_dom (m : WorldT)))).
  {
    assert (Hσr :
        (res_restrict my (world_dom (m : WorldT)) : WorldT)
          (store_restrict σ (world_dom (m : WorldT)))).
    { exists σ. split; [exact Hσ|reflexivity]. }
    rewrite Hrestrict in Hσr. exact Hσr.
  }
  specialize (Heq (store_restrict σ (world_dom (m : WorldT))) v Hσm)
    as [Heq12 Heq21].
  assert (Hfv1 : fv_tm e1 ⊆ world_dom (m : WorldT)) by set_solver.
  assert (Hfv2 : fv_tm e2 ⊆ world_dom (m : WorldT)) by set_solver.
  split.
  - intros Heval1.
    apply (proj1 (tm_eval_in_store_restrict_fv_subset
      σ e2 v (world_dom (m : WorldT)) Hfv2)).
    apply Heq12.
    apply (proj2 (tm_eval_in_store_restrict_fv_subset
      σ e1 v (world_dom (m : WorldT)) Hfv1)).
    exact Heval1.
  - intros Heval2.
    apply (proj1 (tm_eval_in_store_restrict_fv_subset
      σ e1 v (world_dom (m : WorldT)) Hfv1)).
    apply Heq21.
    apply (proj2 (tm_eval_in_store_restrict_fv_subset
      σ e2 v (world_dom (m : WorldT)) Hfv2)).
    exact Heval2.
Qed.

Lemma arrow_open_arg_to_inserted_env
    gas (Σ : lty_env) τx τr e
    (m : WfWorldT) y :
  lty_env_closed Σ ->
  LVFree y ∉ dom Σ ->
  y ∉ fv_cty τx ->
  y ∉ lvars_fv
    (dom (typed_lty_env_bind
      (relevant_env Σ (CTArrow τx τr) e) (erase_ty τx))) ->
  m ⊨ formula_open 0 y
    (ty_denote_gas gas
      (typed_lty_env_bind
        (relevant_env Σ (CTArrow τx τr) e)
        (erase_ty τx))
      (cty_shift 0 τx) (tret (vbvar 0))) ->
  m ⊨ ty_denote_gas gas
    (<[LVFree y := erase_ty τx]> Σ)
    (cty_open 0 y (cty_shift 0 τx)) (tret (vfvar y)).
Proof.
  intros HΣclosed HfreshΣ Hyτx Hfresh_arg Harg.
  assert (Hτa_fresh : y ∉ fv_cty (cty_shift 0 τx)).
  { rewrite cty_shift_fv. exact Hyτx. }
  assert (Hea_fresh : y ∉ fv_tm (tret (vbvar 0))).
  { cbn [fv_tm fv_value]. better_set_solver. }
  rewrite (formula_open_ty_denote_gas_singleton 0 y gas
    (typed_lty_env_bind
      (relevant_env Σ (CTArrow τx τr) e) (erase_ty τx))
    (cty_shift 0 τx) (tret (vbvar 0))) in Harg
    by (exact Hfresh_arg || exact Hea_fresh || exact Hτa_fresh).
  change (open_tm 0 (vfvar y) (tret (vbvar 0)))
    with (tret (vfvar y)) in Harg.
  pose proof (ty_denote_gas_env_agree_on gas
    (lty_env_open_one 0 y
      (typed_lty_env_bind
        (relevant_env Σ (CTArrow τx τr) e) (erase_ty τx)))
    (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
    (cty_open 0 y (cty_shift 0 τx)) (tret (vfvar y))
    (relevant_lvars (cty_open 0 y (cty_shift 0 τx))
      (tret (vfvar y)))
    ltac:(better_set_solver)
    (arrow_arg_relevant_env_agree_open_one_core
      Σ (erase_ty τx) y τx τr e Hyτx)) as Hagree.
  rewrite Hagree in Harg.
  rewrite typed_lty_env_bind_open_current in Harg
    by (exact HfreshΣ || exact HΣclosed).
  exact Harg.
Qed.

Lemma arrow_open_arg_to_inserted_env_normalized
    gas (Σ : lty_env) τx τr e
    (m : WfWorldT) y :
  lty_env_closed Σ ->
  LVFree y ∉ dom Σ ->
  y ∉ fv_cty τx ->
  lc_context_ty τx ->
  y ∉ lvars_fv
    (dom (typed_lty_env_bind
      (relevant_env Σ (CTArrow τx τr) e) (erase_ty τx))) ->
  m ⊨ formula_open 0 y
    (ty_denote_gas gas
      (typed_lty_env_bind
        (relevant_env Σ (CTArrow τx τr) e)
        (erase_ty τx))
      (cty_shift 0 τx) (tret (vbvar 0))) ->
  m ⊨ ty_denote_gas gas
    (<[LVFree y := erase_ty τx]> Σ)
    τx (tret (vfvar y)).
Proof.
  intros HΣclosed HfreshΣ Hyτx Hlc Hfresh_arg Harg.
  pose proof (arrow_open_arg_to_inserted_env
    gas Σ τx τr e m y HΣclosed HfreshΣ Hyτx Hfresh_arg Harg)
    as Harg_open.
  rewrite cty_open_shift_from_lc_fresh in Harg_open
    by (exact Hlc || exact Hyτx).
  exact Harg_open.
Qed.

Lemma ty_equiv_arrow_result_src_mid
    gas (Σ : lty_env) τx τr e1
    (my : WfWorldT) y :
  lc_tm e1 ->
  y ∉ fv_cty τr ->
  my ⊨ ty_denote_gas gas
    (lty_env_open_one 0 y
      (typed_lty_env_bind
        (relevant_env Σ (CTArrow τx τr) e1)
        (erase_ty τx)))
    (cty_open 0 y τr) (tapp_tm e1 (vfvar y)) ->
  my ⊨ ty_denote_gas gas
    (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
    (cty_open 0 y τr) (tapp_tm e1 (vfvar y)).
Proof.
  intros Hlc Hyτr Hsrc.
  pose proof (ty_denote_gas_env_agree_on gas
    (lty_env_open_one 0 y
      (typed_lty_env_bind
        (relevant_env Σ (CTArrow τx τr) e1)
        (erase_ty τx)))
    (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
    (cty_open 0 y τr) (tapp_tm e1 (vfvar y))
    (relevant_lvars (cty_open 0 y τr)
      (tapp_tm e1 (vfvar y)))
    ltac:(set_solver)
    (arrow_body_relevant_env_agree_open_one_core
      Σ (erase_ty τx) y τx τr e1 (tapp_tm e1 (vfvar y))
      Hyτr (tm_lvars_tapp_tm_fvar_without_arg_shift_lc e1 y Hlc)))
    as Hagree.
  rewrite <- Hagree.
  exact Hsrc.
Qed.

Lemma ty_equiv_arrow_result_tgt_goal
    gas (Σ : lty_env) τx τr e2
    (my : WfWorldT) y :
  lc_tm e2 ->
  y ∉ fv_cty τr ->
  my ⊨ ty_denote_gas gas
    (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
    (cty_open 0 y τr) (tapp_tm e2 (vfvar y)) ->
  my ⊨ ty_denote_gas gas
    (lty_env_open_one 0 y
      (typed_lty_env_bind
        (relevant_env Σ (CTArrow τx τr) e2)
        (erase_ty τx)))
    (cty_open 0 y τr) (tapp_tm e2 (vfvar y)).
Proof.
  intros Hlc Hyτr Hmid.
  pose proof (ty_denote_gas_env_agree_on gas
    (lty_env_open_one 0 y
      (typed_lty_env_bind
        (relevant_env Σ (CTArrow τx τr) e2)
        (erase_ty τx)))
    (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
    (cty_open 0 y τr) (tapp_tm e2 (vfvar y))
    (relevant_lvars (cty_open 0 y τr)
      (tapp_tm e2 (vfvar y)))
    ltac:(set_solver)
    (arrow_body_relevant_env_agree_open_one_core
      Σ (erase_ty τx) y τx τr e2 (tapp_tm e2 (vfvar y))
      Hyτr (tm_lvars_tapp_tm_fvar_without_arg_shift_lc e2 y Hlc)))
    as Hagree.
  rewrite Hagree.
  exact Hmid.
Qed.

Lemma ty_equiv_wand_result_src_mid
    gas (Σ : lty_env) τx τr e1
    (m : WfWorldT) y :
  lc_tm e1 ->
  y ∉ fv_cty τr ->
  m ⊨ ty_denote_gas gas
    (lty_env_open_one 0 y
      (typed_lty_env_bind
        (relevant_env Σ (CTWand τx τr) e1)
        (erase_ty τx)))
    (cty_open 0 y τr) (tapp_tm e1 (vfvar y)) ->
  m ⊨ ty_denote_gas gas
    (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
    (cty_open 0 y τr) (tapp_tm e1 (vfvar y)).
Proof.
  intros Hlc Hyτr Hsrc.
  pose proof (ty_denote_gas_env_agree_on gas
    (lty_env_open_one 0 y
      (typed_lty_env_bind
        (relevant_env Σ (CTWand τx τr) e1)
        (erase_ty τx)))
    (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
    (cty_open 0 y τr) (tapp_tm e1 (vfvar y))
    (relevant_lvars (cty_open 0 y τr)
      (tapp_tm e1 (vfvar y)))
    ltac:(set_solver)
    (wand_body_relevant_env_agree_open_one_core
      Σ (erase_ty τx) y τx τr e1 (tapp_tm e1 (vfvar y))
      Hyτr (tm_lvars_tapp_tm_fvar_without_arg_shift_lc e1 y Hlc)))
    as Hagree.
  rewrite <- Hagree.
  exact Hsrc.
Qed.

Lemma ty_equiv_wand_result_tgt_goal
    gas (Σ : lty_env) τx τr e2
    (m : WfWorldT) y :
  lc_tm e2 ->
  y ∉ fv_cty τr ->
  m ⊨ ty_denote_gas gas
    (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
    (cty_open 0 y τr) (tapp_tm e2 (vfvar y)) ->
  m ⊨ ty_denote_gas gas
    (lty_env_open_one 0 y
      (typed_lty_env_bind
        (relevant_env Σ (CTWand τx τr) e2)
        (erase_ty τx)))
    (cty_open 0 y τr) (tapp_tm e2 (vfvar y)).
Proof.
  intros Hlc Hyτr Hmid.
  pose proof (ty_denote_gas_env_agree_on gas
    (lty_env_open_one 0 y
      (typed_lty_env_bind
        (relevant_env Σ (CTWand τx τr) e2)
        (erase_ty τx)))
    (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
    (cty_open 0 y τr) (tapp_tm e2 (vfvar y))
    (relevant_lvars (cty_open 0 y τr)
      (tapp_tm e2 (vfvar y)))
    ltac:(set_solver)
    (wand_body_relevant_env_agree_open_one_core
      Σ (erase_ty τx) y τx τr e2 (tapp_tm e2 (vfvar y))
      Hyτr (tm_lvars_tapp_tm_fvar_without_arg_shift_lc e2 y Hlc)))
    as Hagree.
  rewrite Hagree.
  exact Hmid.
Qed.

End TypeDenote.
