(** * Denotation.TypeEquivFiberTransport

    Application and opened-result transport lemmas built on top of
    [TypeEquivTerm].  Kept separate so the core term/fiber definitions stay
    small and lower-level. *)

From Denotation Require Import Notation TypeDenote TypeEquivCore TypeEquivTerm
  DenotationSetMapFacts.
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
  { eapply wfworld_closed_on_store_restrict_closed; eauto. }
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
  { eapply wfworld_closed_on_store_restrict_closed; eauto. }
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
  { eapply wfworld_closed_on_store_restrict_closed; eauto. }
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

Lemma tm_equiv_ret_value_result_alias_on
    (m : WfWorldT) X vx z :
  fv_tm (tret (vfvar z)) ∪ fv_tm (tret vx) ⊆ X ->
  z ∈ X ->
  fv_value vx ⊆ X ->
  wfworld_closed_on X m ->
  lc_value vx ->
  m ⊨ expr_result_formula (tret vx) (LVFree z) ->
  tm_equiv_on m (tret (vfvar z)) (tret vx).
Proof.
  intros HfvX HzX Hfvx Hclosed Hvx Hres σ v Hσ.
  assert (HσX_closed : store_closed (store_restrict σ X)).
  { eapply wfworld_closed_on_store_restrict_closed; eauto. }
  assert (Hfv_z : fv_tm (tret (vfvar z)) ⊆ X) by set_solver.
  assert (Hfv_vx : fv_tm (tret vx) ⊆ X) by set_solver.
  pose proof (expr_result_formula_ret_value_inst_eq_on
    m X vx z HzX Hfvx Hclosed Hvx Hres σ Hσ) as Heq.
  split; intros Heval.
  - apply (proj1 (tm_eval_in_store_restrict_fv_subset
      σ (tret vx) v X Hfv_vx)).
    pose proof (proj2 (tm_eval_in_store_restrict_fv_subset
      σ (tret (vfvar z)) v X Hfv_z) Heval) as HevalX.
    pose proof (tm_eval_in_store_ret_value_inv
      (store_restrict σ X) (vfvar z) v HσX_closed ltac:(constructor)
      HevalX) as ->.
    rewrite Heq.
    apply tm_eval_in_store_ret_value; [exact HσX_closed|exact Hvx].
  - apply (proj1 (tm_eval_in_store_restrict_fv_subset
      σ (tret (vfvar z)) v X Hfv_z)).
    pose proof (proj2 (tm_eval_in_store_restrict_fv_subset
      σ (tret vx) v X Hfv_vx) Heval) as HevalX.
    pose proof (tm_eval_in_store_ret_value_inv
      (store_restrict σ X) vx v HσX_closed Hvx HevalX) as ->.
    rewrite <- Heq.
    apply tm_eval_in_store_ret_value; [exact HσX_closed|constructor].
Qed.

Lemma tm_equiv_ret_value_result_alias
    (m : WfWorldT) vx z :
  wfworld_closed_on (fv_tm (tret (vfvar z)) ∪ fv_tm (tret vx)) m ->
  lc_value vx ->
  m ⊨ expr_result_formula (tret vx) (LVFree z) ->
  tm_equiv_on m (tret (vfvar z)) (tret vx).
Proof.
  intros Hclosed Hvx Hres.
  eapply (tm_equiv_ret_value_result_alias_on
    m (fv_tm (tret (vfvar z)) ∪ fv_tm (tret vx)) vx z).
  - intros a Ha. exact Ha.
  - apply elem_of_union_l.
    cbn [fv_tm fv_value].
    apply elem_of_singleton_2. reflexivity.
  - intros a Ha. apply elem_of_union_r. exact Ha.
  - exact Hclosed.
  - exact Hvx.
  - exact Hres.
Qed.

Lemma tm_total_equiv_ret_value_result_alias_on
    (m : WfWorldT) X vx z :
  fv_tm (tret (vfvar z)) ∪ fv_tm (tret vx) ⊆ X ->
  z ∈ X ->
  fv_value vx ⊆ X ->
  wfworld_closed_on X m ->
  lc_value vx ->
  m ⊨ expr_result_formula (tret vx) (LVFree z) ->
  tm_total_equiv_on m (tret (vfvar z)) (tret vx).
Proof.
  intros HfvX HzX Hfvx Hclosed Hvx Hres σ Hσ.
  set (σX := store_restrict σ X : StoreT).
  assert (HσX_closed : store_closed σX).
  { subst σX. eapply wfworld_closed_on_store_restrict_closed; eauto. }
  assert (Hfv_z : fv_tm (tret (vfvar z)) ⊆ X) by set_solver.
  assert (Hfv_vx : fv_tm (tret vx) ⊆ X) by set_solver.
  pose proof (expr_result_formula_ret_value_inst_eq_on
    m X vx z HzX Hfvx Hclosed Hvx Hres σ Hσ) as Heq.
  assert (Htm_eq_X :
      lstore_instantiate_tm (lstore_lift_free σX) (tret (vfvar z)) =
      lstore_instantiate_tm (lstore_lift_free σX) (tret vx)).
  {
    subst σX.
    unfold lstore_instantiate_tm.
    rewrite !lstore_instantiate_tm_no_bvars by
      (try apply lc_lstore_lift_free;
       rewrite ?lstore_free_part_lift_free; exact (proj1 HσX_closed)).
    rewrite !lstore_free_part_lift_free.
    rewrite !subst_map_tm_eq_msubst.
    rewrite !msubst_ret.
    change (tret (m{store_restrict σ X} (vfvar z)) =
      tret (m{store_restrict σ X} vx)).
    rewrite Heq. reflexivity.
  }
  assert (HtotX :
      must_terminating
        (lstore_instantiate_tm (lstore_lift_free σX) (tret (vfvar z))) <->
      must_terminating
        (lstore_instantiate_tm (lstore_lift_free σX) (tret vx))).
  { rewrite Htm_eq_X. reflexivity. }
  assert (Hlc_z : lc_tm (tret (vfvar z))).
  { constructor. constructor. }
  assert (Hlc_vx : lc_tm (tret vx)) by (constructor; exact Hvx).
  assert (Hagree_z :
      store_restrict σX (fv_tm (tret (vfvar z))) =
      store_restrict σ (fv_tm (tret (vfvar z)))).
  { subst σX. rewrite storeA_restrict_twice_subset by exact Hfv_z.
    reflexivity. }
  assert (Hagree_vx :
      store_restrict σX (fv_tm (tret vx)) =
      store_restrict σ (fv_tm (tret vx))).
  { subst σX. rewrite storeA_restrict_twice_subset by exact Hfv_vx.
    reflexivity. }
  split; intros Htotal.
  - apply (proj1 (tm_must_terminating_agree_on_fv
      σX σ (tret vx) Hlc_vx Hagree_vx)).
    apply (proj1 HtotX).
    apply (proj2 (tm_must_terminating_agree_on_fv
      σX σ (tret (vfvar z)) Hlc_z Hagree_z)).
    exact Htotal.
  - apply (proj1 (tm_must_terminating_agree_on_fv
      σX σ (tret (vfvar z)) Hlc_z Hagree_z)).
    apply (proj2 HtotX).
    apply (proj2 (tm_must_terminating_agree_on_fv
      σX σ (tret vx) Hlc_vx Hagree_vx)).
    exact Htotal.
Qed.

Lemma tm_total_equiv_ret_value_result_alias
    (m : WfWorldT) vx z :
  wfworld_closed_on (fv_tm (tret (vfvar z)) ∪ fv_tm (tret vx)) m ->
  lc_value vx ->
  m ⊨ expr_result_formula (tret vx) (LVFree z) ->
  tm_total_equiv_on m (tret (vfvar z)) (tret vx).
Proof.
  intros Hclosed Hvx Hres.
  eapply (tm_total_equiv_ret_value_result_alias_on
    m (fv_tm (tret (vfvar z)) ∪ fv_tm (tret vx)) vx z).
  - intros a Ha. exact Ha.
  - apply elem_of_union_l.
    cbn [fv_tm fv_value].
    apply elem_of_singleton_2. reflexivity.
  - intros a Ha. apply elem_of_union_r. exact Ha.
  - exact Hclosed.
  - exact Hvx.
  - exact Hres.
Qed.

Lemma typed_total_equiv_ret_value_result_alias
    (Σ : lty_env) τ (m : WfWorldT) vx z :
  wfworld_closed_on (fv_tm (tret (vfvar z)) ∪ fv_tm (tret vx)) m ->
  lc_value vx ->
  m ⊨ expr_result_formula (tret vx) (LVFree z) ->
  m ⊨ ty_denote_gas 0 Σ τ (tret vx) ->
  m ⊨ ty_denote_gas 0 Σ τ (tret (vfvar z)) ->
  typed_total_equiv_on Σ τ m (tret vx) (tret (vfvar z)).
Proof.
  intros Hclosed Hvx Hres Hzero_v Hzero_z.
  split.
  - intros σ v Hσ.
    pose proof (tm_equiv_ret_value_result_alias
      m vx z Hclosed Hvx Hres σ v Hσ) as [Hzv Hvz].
    split; [exact Hvz|exact Hzv].
  - split.
    + intros σ Hσ.
      pose proof (tm_total_equiv_ret_value_result_alias
        m vx z Hclosed Hvx Hres σ Hσ) as [Hzv Hvz].
      split; [exact Hvz|exact Hzv].
    + split; assumption.
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

Lemma basic_tm_has_ltype_open_result_target_fun
    (Σ : lty_env) τtop τx τr e1 e2
    (m : WfWorldT) y :
  erase_ty τtop = erase_ty τx →ₜ erase_ty τr ->
  typed_total_equiv_on Σ τtop m e1 e2 ->
  y ∉ fv_tm e1 ∪ fv_tm e2 ->
  basic_tm_has_ltype
    (relevant_env
      (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
      (cty_open 0 y τr) (tapp_tm e2 (vfvar y)))
    e2 (erase_ty τx →ₜ erase_ty τr).
Proof.
  intros Herase Hequiv Hfresh.
  destruct Hequiv as [_ [_ [_ Hzero_tgt]]].
  pose proof (ty_denote_gas_guard_of_zero Σ τtop e2 m Hzero_tgt)
    as Hguard.
  repeat rewrite res_models_and_iff in Hguard.
  destruct Hguard as [_ [Hworld [Hbasic _]]].
  apply expr_basic_typing_formula_models_iff in Hbasic
    as [HlcΣ [_ Hty]].
  rewrite Herase in Hty.
  pose proof (basic_tm_has_ltype_lc _ e2
    (erase_ty τx →ₜ erase_ty τr) HlcΣ Hty) as Hlc_e2.
  eapply basic_tm_has_ltype_env_agree_lc; [exact Hty|exact Hlc_e2|].
  apply storeA_map_eq. intros v.
  unfold relevant_env, lty_env_restrict_lvars.
  rewrite !storeA_restrict_lookup.
  destruct (decide (v ∈ tm_lvars e2)) as [Hv|Hv]; [|reflexivity].
  assert (Hv_source : v ∈ relevant_lvars τtop e2).
  {
    unfold relevant_lvars. set_solver.
  }
  assert (Hv_target :
      v ∈ relevant_lvars (cty_open 0 y τr)
        (tapp_tm e2 (vfvar y))).
  {
    unfold relevant_lvars, tapp_tm.
      cbn [tm_lvars tm_lvars_at value_lvars_at].
    set_solver.
  }
  rewrite decide_True by exact Hv_source.
  rewrite decide_True by exact Hv_target.
  destruct v as [k|a].
  - exfalso. exact ((tm_lvars_lc e2 Hlc_e2) (LVBound k) Hv).
  - assert (Hay : a <> y).
    {
      intros ->. apply Hfresh. apply elem_of_union_r.
      rewrite <- tm_lvars_fv. apply lvars_fv_elem. exact Hv.
    }
    rewrite lty_env_open_one_typed_bind_lookup_free_ne by exact Hay.
    reflexivity.
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

Lemma tm_equiv_tapp_value_fun_result_alias_on
    (m : WfWorldT) X vf y z :
  fv_tm (tapp_tm (tret (vfvar z)) (vfvar y)) ∪
    fv_tm (tapp_tm (tret vf) (vfvar y)) ⊆ X ->
  z ∈ X ->
  fv_value vf ⊆ X ->
  wfworld_closed_on X m ->
  lc_value vf ->
  m ⊨ expr_result_formula (tret vf) (LVFree z) ->
  tm_equiv_on m
    (tapp_tm (tret (vfvar z)) (vfvar y))
    (tapp_tm (tret vf) (vfvar y)).
Proof.
  intros HfvX HzX Hfvf Hclosed Hvf Hres σ v Hσ.
  assert (HσX_closed : store_closed (store_restrict σ X)).
  { eapply wfworld_closed_on_store_restrict_closed; eauto. }
  assert (Hfv_app1 : fv_tm (tapp_tm (tret (vfvar z)) (vfvar y)) ⊆ X)
    by set_solver.
  assert (Hfv_app2 : fv_tm (tapp_tm (tret vf) (vfvar y)) ⊆ X)
    by set_solver.
  assert (Hfun_equiv :
      forall vf0,
        tm_eval_in_store (store_restrict σ X) (tret (vfvar z)) vf0 <->
        tm_eval_in_store (store_restrict σ X) (tret vf) vf0).
  {
    intros vf0.
    pose proof (expr_result_formula_ret_value_inst_eq_on
      m X vf z HzX Hfvf Hclosed Hvf Hres σ Hσ) as Heq.
    split; intros Heval.
    - pose proof (tm_eval_in_store_ret_value_inv
        (store_restrict σ X) (vfvar z) vf0 HσX_closed ltac:(constructor)
        Heval) as ->.
      rewrite Heq.
      apply tm_eval_in_store_ret_value.
      + exact HσX_closed.
      + exact Hvf.
    - pose proof (tm_eval_in_store_ret_value_inv
        (store_restrict σ X) vf vf0 HσX_closed Hvf Heval) as ->.
      rewrite <- Heq.
      apply tm_eval_in_store_ret_value.
      + exact HσX_closed.
      + constructor.
  }
  pose proof (tm_eval_in_store_tapp_tm_fun_equiv
    (store_restrict σ X) (tret (vfvar z)) (tret vf) y v
    HσX_closed ltac:(constructor; constructor)
    ltac:(constructor; exact Hvf) Hfun_equiv) as [H12 H21].
  split; intros Heval.
  - apply (proj1 (tm_eval_in_store_restrict_fv_subset
      σ (tapp_tm (tret vf) (vfvar y)) v X Hfv_app2)).
    apply H12.
    apply (proj2 (tm_eval_in_store_restrict_fv_subset
      σ (tapp_tm (tret (vfvar z)) (vfvar y)) v X Hfv_app1)).
    exact Heval.
  - apply (proj1 (tm_eval_in_store_restrict_fv_subset
      σ (tapp_tm (tret (vfvar z)) (vfvar y)) v X Hfv_app1)).
    apply H21.
    apply (proj2 (tm_eval_in_store_restrict_fv_subset
      σ (tapp_tm (tret vf) (vfvar y)) v X Hfv_app2)).
    exact Heval.
Qed.

Lemma tm_equiv_tapp_value_fun_result_alias
    (m : WfWorldT) vf y z :
  wfworld_closed_on
    (fv_tm (tapp_tm (tret (vfvar z)) (vfvar y)) ∪
     fv_tm (tapp_tm (tret vf) (vfvar y))) m ->
  lc_value vf ->
  m ⊨ expr_result_formula (tret vf) (LVFree z) ->
  tm_equiv_on m
    (tapp_tm (tret (vfvar z)) (vfvar y))
    (tapp_tm (tret vf) (vfvar y)).
Proof.
  intros Hclosed Hvf Hres.
  eapply (tm_equiv_tapp_value_fun_result_alias_on
    m (fv_tm (tapp_tm (tret (vfvar z)) (vfvar y)) ∪
       fv_tm (tapp_tm (tret vf) (vfvar y))) vf y z).
  - intros a Ha. exact Ha.
  - apply elem_of_union_l.
    rewrite fv_tapp_tm.
    cbn [fv_tm fv_value].
    apply elem_of_union_l.
    apply elem_of_singleton_2. reflexivity.
  - intros a Ha.
    apply elem_of_union_r.
    rewrite fv_tapp_tm.
    cbn [fv_tm].
    apply elem_of_union_l. exact Ha.
  - exact Hclosed.
  - exact Hvf.
  - exact Hres.
Qed.

Lemma tm_total_equiv_tapp_value_fun_result_alias_on
    (m : WfWorldT) X vf y z :
  fv_tm (tapp_tm (tret (vfvar z)) (vfvar y)) ∪
    fv_tm (tapp_tm (tret vf) (vfvar y)) ⊆ X ->
  z ∈ X ->
  fv_value vf ⊆ X ->
  wfworld_closed_on X m ->
  lc_value vf ->
  m ⊨ expr_result_formula (tret vf) (LVFree z) ->
  tm_total_equiv_on m
    (tapp_tm (tret (vfvar z)) (vfvar y))
    (tapp_tm (tret vf) (vfvar y)).
Proof.
  intros HfvX HzX Hfvf Hclosed Hvf Hres σ Hσ.
  set (σX := store_restrict σ X : StoreT).
  assert (HσX_closed : store_closed σX).
  { subst σX. eapply wfworld_closed_on_store_restrict_closed; eauto. }
  assert (Hfv_app1 : fv_tm (tapp_tm (tret (vfvar z)) (vfvar y)) ⊆ X)
    by set_solver.
  assert (Hfv_app2 : fv_tm (tapp_tm (tret vf) (vfvar y)) ⊆ X)
    by set_solver.
  pose proof (expr_result_formula_ret_value_inst_eq_on
    m X vf z HzX Hfvf Hclosed Hvf Hres σ Hσ) as Heq.
  assert (Htm_eq_X :
      lstore_instantiate_tm (lstore_lift_free σX)
        (tapp_tm (tret (vfvar z)) (vfvar y)) =
      lstore_instantiate_tm (lstore_lift_free σX)
        (tapp_tm (tret vf) (vfvar y))).
  {
    subst σX.
    unfold lstore_instantiate_tm.
    rewrite !lstore_instantiate_tm_no_bvars by
      (try apply lc_lstore_lift_free;
       rewrite ?lstore_free_part_lift_free; exact (proj1 HσX_closed)).
    rewrite !lstore_free_part_lift_free.
    rewrite !subst_map_tm_eq_msubst.
    rewrite !msubst_tapp_tm_lc_arg by
      (constructor || exact (proj2 HσX_closed)).
    rewrite !msubst_ret.
    change (tapp_tm (tret (m{store_restrict σ X} (vfvar z)))
      (m{store_restrict σ X} (vfvar y)) =
      tapp_tm (tret (m{store_restrict σ X} vf))
      (m{store_restrict σ X} (vfvar y))).
    rewrite Heq.
    reflexivity.
  }
  assert (HappsX :
      must_terminating
        (lstore_instantiate_tm (lstore_lift_free σX)
          (tapp_tm (tret (vfvar z)) (vfvar y))) <->
      must_terminating
        (lstore_instantiate_tm (lstore_lift_free σX)
          (tapp_tm (tret vf) (vfvar y)))).
  { rewrite Htm_eq_X. reflexivity. }
  assert (Hlc_app1 : lc_tm (tapp_tm (tret (vfvar z)) (vfvar y))).
  { apply lc_tapp_tm; constructor; constructor. }
  assert (Hlc_app2 : lc_tm (tapp_tm (tret vf) (vfvar y))).
  { apply lc_tapp_tm; [constructor; exact Hvf|constructor]. }
  assert (Hagree_app1 :
      store_restrict σX (fv_tm (tapp_tm (tret (vfvar z)) (vfvar y))) =
      store_restrict σ (fv_tm (tapp_tm (tret (vfvar z)) (vfvar y)))).
  { subst σX. rewrite storeA_restrict_twice_subset by exact Hfv_app1.
    reflexivity. }
  assert (Hagree_app2 :
      store_restrict σX (fv_tm (tapp_tm (tret vf) (vfvar y))) =
      store_restrict σ (fv_tm (tapp_tm (tret vf) (vfvar y)))).
  { subst σX. rewrite storeA_restrict_twice_subset by exact Hfv_app2.
    reflexivity. }
  split; intros Htotal.
  - apply (proj1 (tm_must_terminating_agree_on_fv
      σX σ (tapp_tm (tret vf) (vfvar y)) Hlc_app2 Hagree_app2)).
    apply (proj1 HappsX).
    apply (proj2 (tm_must_terminating_agree_on_fv
      σX σ (tapp_tm (tret (vfvar z)) (vfvar y)) Hlc_app1 Hagree_app1)).
    exact Htotal.
  - apply (proj1 (tm_must_terminating_agree_on_fv
      σX σ (tapp_tm (tret (vfvar z)) (vfvar y)) Hlc_app1 Hagree_app1)).
    apply (proj2 HappsX).
    apply (proj2 (tm_must_terminating_agree_on_fv
      σX σ (tapp_tm (tret vf) (vfvar y)) Hlc_app2 Hagree_app2)).
    exact Htotal.
Qed.

Lemma tm_total_equiv_tapp_value_fun_result_alias
    (m : WfWorldT) vf y z :
  wfworld_closed_on
    (fv_tm (tapp_tm (tret (vfvar z)) (vfvar y)) ∪
     fv_tm (tapp_tm (tret vf) (vfvar y))) m ->
  lc_value vf ->
  m ⊨ expr_result_formula (tret vf) (LVFree z) ->
  tm_total_equiv_on m
    (tapp_tm (tret (vfvar z)) (vfvar y))
    (tapp_tm (tret vf) (vfvar y)).
Proof.
  intros Hclosed Hvf Hres.
  eapply (tm_total_equiv_tapp_value_fun_result_alias_on
    m (fv_tm (tapp_tm (tret (vfvar z)) (vfvar y)) ∪
       fv_tm (tapp_tm (tret vf) (vfvar y))) vf y z).
  - intros a Ha. exact Ha.
  - apply elem_of_union_l.
    rewrite fv_tapp_tm.
    cbn [fv_tm fv_value].
    apply elem_of_union_l.
    apply elem_of_singleton_2. reflexivity.
  - intros a Ha.
    apply elem_of_union_r.
    rewrite fv_tapp_tm.
    cbn [fv_tm].
    apply elem_of_union_l. exact Ha.
  - exact Hclosed.
  - exact Hvf.
  - exact Hres.
Qed.

Lemma tm_equiv_tapp_value_fun_arg_result_alias
    (m : WfWorldT) vf vx z w :
  wfworld_closed_on
    (fv_tm (tapp_tm (tret (vfvar z)) (vfvar w)) ∪
     fv_tm (tapp_tm (tret vf) vx)) m ->
  lc_value vf ->
  lc_value vx ->
  m ⊨ expr_result_formula (tret vf) (LVFree z) ->
  m ⊨ expr_result_formula (tret vx) (LVFree w) ->
  tm_equiv_on m
    (tapp_tm (tret (vfvar z)) (vfvar w))
    (tapp_tm (tret vf) vx).
Proof.
  intros Hclosed Hvf Hvx Hfun Harg σ v Hσ.
  assert (Hclosed_fun :
      wfworld_closed_on
        (fv_tm (tapp_tm (tret (vfvar z)) (vfvar w)) ∪
         fv_tm (tapp_tm (tret vf) (vfvar w))) m).
  {
    eapply wfworld_closed_on_mono; [|exact Hclosed].
    cbn [fv_tm fv_value].
    set_solver.
  }
  assert (Hclosed_arg :
      wfworld_closed_on
        (fv_tm (tapp_tm (tret vf) (vfvar w)) ∪
         fv_tm (tapp_tm (tret vf) vx)) m).
  {
    eapply wfworld_closed_on_mono; [|exact Hclosed].
    cbn [fv_tm fv_value].
    set_solver.
  }
  pose proof (tm_equiv_tapp_value_fun_result_alias
    m vf w z Hclosed_fun Hvf Hfun σ v Hσ) as Hfun_eq.
  pose proof (tm_equiv_tapp_value_arg_result_alias
    m (tret vf) vx w Hclosed_arg Hvx Harg σ v Hσ) as Harg_eq.
  split; intros Heval.
  - apply (proj1 Harg_eq). apply (proj1 Hfun_eq). exact Heval.
  - apply (proj2 Hfun_eq). apply (proj2 Harg_eq). exact Heval.
Qed.

Lemma tm_total_equiv_tapp_value_fun_arg_result_alias
    (m : WfWorldT) vf vx z w :
  wfworld_closed_on
    (fv_tm (tapp_tm (tret (vfvar z)) (vfvar w)) ∪
     fv_tm (tapp_tm (tret vf) vx)) m ->
  lc_value vf ->
  lc_value vx ->
  m ⊨ expr_result_formula (tret vf) (LVFree z) ->
  m ⊨ expr_result_formula (tret vx) (LVFree w) ->
  tm_total_equiv_on m
    (tapp_tm (tret (vfvar z)) (vfvar w))
    (tapp_tm (tret vf) vx).
Proof.
  intros Hclosed Hvf Hvx Hfun Harg σ Hσ.
  assert (Hclosed_fun :
      wfworld_closed_on
        (fv_tm (tapp_tm (tret (vfvar z)) (vfvar w)) ∪
         fv_tm (tapp_tm (tret vf) (vfvar w))) m).
  {
    eapply wfworld_closed_on_mono; [|exact Hclosed].
    cbn [fv_tm fv_value].
    set_solver.
  }
  assert (Hclosed_arg :
      wfworld_closed_on
        (fv_tm (tapp_tm (tret vf) (vfvar w)) ∪
         fv_tm (tapp_tm (tret vf) vx)) m).
  {
    eapply wfworld_closed_on_mono; [|exact Hclosed].
    cbn [fv_tm fv_value].
    set_solver.
  }
  pose proof (tm_total_equiv_tapp_value_fun_result_alias
    m vf w z Hclosed_fun Hvf Hfun σ Hσ) as Hfun_total.
  pose proof (tm_total_equiv_tapp_value_arg_result_alias
    m (tret vf) vx w Hclosed_arg ltac:(constructor; exact Hvf)
    Hvx Harg σ Hσ) as Harg_total.
  split.
  - intros Hsrc.
    apply (proj1 Harg_total). apply (proj1 Hfun_total). exact Hsrc.
  - intros Htgt.
    apply (proj2 Hfun_total). apply (proj2 Harg_total). exact Htgt.
Qed.

End TypeDenote.
