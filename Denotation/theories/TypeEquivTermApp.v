(** * Denotation.TypeEquivTermApp

    Product, application, and totality transport support for terms. *)

From Denotation Require Import Notation TypeDenote TypeEquivCore
  TypeEquivTermBase DenotationSetMapFacts.
From CoreLang Require Import StrongNormalization.

Section TypeDenote.

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

Lemma tm_equiv_res_product_right
    (n my : WfWorldT) (Hc : world_compat n my) e1 e2 :
  tm_equiv_on my e1 e2 ->
  fv_tm e1 ∪ fv_tm e2 ⊆ world_dom (my : WorldT) ->
  tm_equiv_on (res_product n my Hc) e1 e2.
Proof.
  intros Heq Hfv σ v Hσ.
  pose proof (res_restrict_eq_of_le my (res_product n my Hc)
    (res_product_le_r n my Hc)) as Hrestrict.
  assert (Hσmy :
      (my : WorldT) (store_restrict σ (world_dom (my : WorldT)))).
  {
    assert (Hσr :
        (res_restrict (res_product n my Hc)
          (world_dom (my : WorldT)) : WorldT)
          (store_restrict σ (world_dom (my : WorldT)))).
    { exists σ. split; [exact Hσ|reflexivity]. }
    rewrite Hrestrict in Hσr. exact Hσr.
  }
  specialize (Heq (store_restrict σ (world_dom (my : WorldT))) v Hσmy)
    as [Heq12 Heq21].
  assert (Hfv1 : fv_tm e1 ⊆ world_dom (my : WorldT)) by set_solver.
  assert (Hfv2 : fv_tm e2 ⊆ world_dom (my : WorldT)) by set_solver.
  split.
  - intros Heval1.
    apply (proj1 (tm_eval_in_store_restrict_fv_subset
      σ e2 v (world_dom (my : WorldT)) Hfv2)).
    apply Heq12.
    apply (proj2 (tm_eval_in_store_restrict_fv_subset
      σ e1 v (world_dom (my : WorldT)) Hfv1)).
    exact Heval1.
  - intros Heval2.
    apply (proj1 (tm_eval_in_store_restrict_fv_subset
      σ e1 v (world_dom (my : WorldT)) Hfv1)).
    apply Heq21.
    apply (proj2 (tm_eval_in_store_restrict_fv_subset
      σ e2 v (world_dom (my : WorldT)) Hfv2)).
    exact Heval2.
Qed.

Lemma tm_total_equiv_res_product_right
    (n my : WfWorldT) (Hc : world_compat n my) e1 e2 :
  tm_total_equiv_on my e1 e2 ->
  lc_tm e1 ->
  lc_tm e2 ->
  fv_tm e1 ∪ fv_tm e2 ⊆ world_dom (my : WorldT) ->
  tm_total_equiv_on (res_product n my Hc) e1 e2.
Proof.
  intros Htotal Hlc1 Hlc2 Hfv σ Hσ.
  pose proof (res_restrict_eq_of_le my (res_product n my Hc)
    (res_product_le_r n my Hc)) as Hrestrict.
  assert (Hσmy :
      (my : WorldT) (store_restrict σ (world_dom (my : WorldT)))).
  {
    assert (Hσr :
        (res_restrict (res_product n my Hc)
          (world_dom (my : WorldT)) : WorldT)
          (store_restrict σ (world_dom (my : WorldT)))).
    { exists σ. split; [exact Hσ|reflexivity]. }
    rewrite Hrestrict in Hσr. exact Hσr.
  }
  specialize (Htotal (store_restrict σ (world_dom (my : WorldT))) Hσmy)
    as [Htotal12 Htotal21].
  assert (Hfv1 : fv_tm e1 ⊆ world_dom (my : WorldT)) by set_solver.
  assert (Hfv2 : fv_tm e2 ⊆ world_dom (my : WorldT)) by set_solver.
  assert (Hagree1 :
    store_restrict (store_restrict σ (world_dom (my : WorldT))) (fv_tm e1) =
    store_restrict σ (fv_tm e1)).
  { rewrite storeA_restrict_twice_subset by exact Hfv1. reflexivity. }
  assert (Hagree2 :
    store_restrict (store_restrict σ (world_dom (my : WorldT))) (fv_tm e2) =
    store_restrict σ (fv_tm e2)).
  { rewrite storeA_restrict_twice_subset by exact Hfv2. reflexivity. }
  split; intros Hsn.
  - apply (proj1 (tm_must_terminating_agree_on_fv
      (store_restrict σ (world_dom (my : WorldT))) σ e2 Hlc2 Hagree2)).
    apply Htotal12.
    apply (proj2 (tm_must_terminating_agree_on_fv
      (store_restrict σ (world_dom (my : WorldT))) σ e1 Hlc1 Hagree1)).
    exact Hsn.
  - apply (proj1 (tm_must_terminating_agree_on_fv
      (store_restrict σ (world_dom (my : WorldT))) σ e1 Hlc1 Hagree1)).
    apply Htotal21.
    apply (proj2 (tm_must_terminating_agree_on_fv
      (store_restrict σ (world_dom (my : WorldT))) σ e2 Hlc2 Hagree2)).
    exact Hsn.
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

Lemma tm_total_equiv_full_world_extend_fresh
    (m my : WfWorldT) y e1 e2 :
  tm_total_equiv_on m e1 e2 ->
  lc_tm e1 ->
  lc_tm e2 ->
  fv_tm e1 ∪ fv_tm e2 ⊆ world_dom (m : WorldT) ->
  y ∉ fv_tm e1 ∪ fv_tm e2 ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_restrict my (world_dom (m : WorldT)) = m ->
  tm_total_equiv_on my e1 e2.
Proof.
  intros Htotal Hlc1 Hlc2 Hfv _ _ Hrestrict σ Hσ.
  assert (Hσm :
      (m : WorldT) (store_restrict σ (world_dom (m : WorldT)))).
  {
    assert (Hσr :
        (res_restrict my (world_dom (m : WorldT)) : WorldT)
          (store_restrict σ (world_dom (m : WorldT)))).
    { exists σ. split; [exact Hσ|reflexivity]. }
    rewrite Hrestrict in Hσr. exact Hσr.
  }
  specialize (Htotal (store_restrict σ (world_dom (m : WorldT))) Hσm)
    as [Htotal12 Htotal21].
  assert (Hfv1 : fv_tm e1 ⊆ world_dom (m : WorldT)) by set_solver.
  assert (Hfv2 : fv_tm e2 ⊆ world_dom (m : WorldT)) by set_solver.
  assert (Hagree1 :
    store_restrict (store_restrict σ (world_dom (m : WorldT))) (fv_tm e1) =
    store_restrict σ (fv_tm e1)).
  { rewrite storeA_restrict_twice_subset by exact Hfv1. reflexivity. }
  assert (Hagree2 :
    store_restrict (store_restrict σ (world_dom (m : WorldT))) (fv_tm e2) =
    store_restrict σ (fv_tm e2)).
  { rewrite storeA_restrict_twice_subset by exact Hfv2. reflexivity. }
  split; intros Hsn.
  - apply (proj1 (tm_must_terminating_agree_on_fv
      (store_restrict σ (world_dom (m : WorldT))) σ e2 Hlc2 Hagree2)).
    apply Htotal12.
    apply (proj2 (tm_must_terminating_agree_on_fv
      (store_restrict σ (world_dom (m : WorldT))) σ e1 Hlc1 Hagree1)).
    exact Hsn.
  - apply (proj1 (tm_must_terminating_agree_on_fv
      (store_restrict σ (world_dom (m : WorldT))) σ e1 Hlc1 Hagree1)).
    apply Htotal21.
    apply (proj2 (tm_must_terminating_agree_on_fv
      (store_restrict σ (world_dom (m : WorldT))) σ e2 Hlc2 Hagree2)).
    exact Hsn.
Qed.

Lemma tm_equiv_total
    m e1 e2 :
  tm_total_equiv_on m e1 e2 ->
  lc_tm e2 ->
  fv_tm e2 ⊆ world_dom (m : WorldT) ->
  m ⊨ expr_total_formula e1 ->
  m ⊨ expr_total_formula e2.
Proof.
  intros Htotal_equiv Hlc2 Hfv2 Htotal.
  apply expr_total_formula_to_atom_world in Htotal.
  apply expr_total_atom_world_to_formula.
  unfold expr_total_on_atom_world, expr_total_on in *.
  destruct Htotal as [_ Hstores].
  split.
  - rewrite res_lift_free_dom.
    rewrite (tm_lvars_lc_eq_atoms e2 Hlc2).
    unfold lvars_of_atoms. set_solver.
  - intros τ Hτ.
    destruct Hτ as [σ [Hσ ->]].
    apply (proj1 (Htotal_equiv σ Hσ)).
    apply Hstores. exists σ. split; [exact Hσ | reflexivity].
Qed.

Lemma tm_equiv_tapp_fvar
    (m : WfWorldT) e1 e2 y :
  wfworld_closed_on
    (fv_tm (tapp_tm e1 (vfvar y)) ∪ fv_tm (tapp_tm e2 (vfvar y))) m ->
  lc_tm e1 ->
  lc_tm e2 ->
  tm_equiv_on m e1 e2 ->
  tm_equiv_on m
    (tapp_tm e1 (vfvar y))
    (tapp_tm e2 (vfvar y)).
Proof.
  intros Hclosed Hlc1 Hlc2 Heq σ v Hσ.
  set (X := fv_tm (tapp_tm e1 (vfvar y)) ∪
            fv_tm (tapp_tm e2 (vfvar y))).
  assert (HσX_closed : store_closed (store_restrict σ X)).
  { subst X. eapply wfworld_closed_on_store_restrict_closed; eauto. }
  assert (Hfv_app1 : fv_tm (tapp_tm e1 (vfvar y)) ⊆ X) by (subst X; set_solver).
  assert (Hfv_app2 : fv_tm (tapp_tm e2 (vfvar y)) ⊆ X) by (subst X; set_solver).
  assert (Hfv_e1 : fv_tm e1 ⊆ X).
  {
    subst X. cbn [fv_tm fv_value].
    unfold tapp_tm. cbn [fv_tm fv_value].
    set_solver.
  }
	  assert (Hfv_e2 : fv_tm e2 ⊆ X).
	  {
	    subst X. cbn [fv_tm fv_value].
	    unfold tapp_tm. cbn [fv_tm fv_value].
	    set_solver.
	  }
	  assert (Hfun_equiv : forall vf,
	      tm_eval_in_store (store_restrict σ X) e1 vf <->
	      tm_eval_in_store (store_restrict σ X) e2 vf).
	  {
	    intros vf. split; intros Heval_fun.
	    - apply (proj2 (tm_eval_in_store_restrict_fv_subset
	        σ e2 vf X Hfv_e2)).
	      apply (proj1 (Heq σ vf Hσ)).
	      apply (proj1 (tm_eval_in_store_restrict_fv_subset
	        σ e1 vf X Hfv_e1)).
	      exact Heval_fun.
	    - apply (proj2 (tm_eval_in_store_restrict_fv_subset
	        σ e1 vf X Hfv_e1)).
	      apply (proj2 (Heq σ vf Hσ)).
	      apply (proj1 (tm_eval_in_store_restrict_fv_subset
	        σ e2 vf X Hfv_e2)).
	      exact Heval_fun.
	  }
	  pose proof (tm_eval_in_store_tapp_tm_fun_equiv
	    (store_restrict σ X) e1 e2 y v HσX_closed Hlc1 Hlc2
	    Hfun_equiv) as [Happ12 Happ21].
	  split.
	  - intros Heval.
	    apply (proj1 (tm_eval_in_store_restrict_fv_subset
	      σ (tapp_tm e2 (vfvar y)) v X Hfv_app2)).
	    apply Happ12.
	    apply (proj2 (tm_eval_in_store_restrict_fv_subset
	        σ (tapp_tm e1 (vfvar y)) v X Hfv_app1)).
	    exact Heval.
	  - intros Heval.
	    apply (proj1 (tm_eval_in_store_restrict_fv_subset
	      σ (tapp_tm e1 (vfvar y)) v X Hfv_app1)).
	    apply Happ21.
	    apply (proj2 (tm_eval_in_store_restrict_fv_subset
	        σ (tapp_tm e2 (vfvar y)) v X Hfv_app2)).
	      exact Heval.
Qed.

Lemma tm_fiber_equiv_restrict_eval_iff
    (m : WfWorldT) X e1 e2 σ σ0 :
  fv_tm e1 ∪ fv_tm e2 ⊆ X ->
  tm_fiber_equiv_on m X e1 e2 ->
  (res_restrict m X : WorldT) σ0 ->
  (m : WorldT) σ ->
  store_restrict σ X = σ0 ->
  forall vf,
    tm_eval_in_store (store_restrict σ X) e1 vf <->
    tm_eval_in_store (store_restrict σ X) e2 vf.
Proof.
  intros HfvX Heq Hσ0 Hσ HσX vf.
  split; intros Heval_fun.
  - assert (Hres1 : tm_fiber_result_on m X e1 σ0 vf).
    {
      exists σ. split; [exact Hσ|]. split; [exact HσX|].
      apply (proj1 (tm_eval_in_store_restrict_fv_subset
        σ e1 vf X ltac:(set_solver))).
      exact Heval_fun.
    }
    destruct (proj1 (Heq σ0 Hσ0 vf) Hres1)
      as [σ2 [Hσ2 [Hσ2X Heval2]]].
    assert (Hσ_eq : store_restrict σ X = store_restrict σ2 X).
    { rewrite HσX, Hσ2X. reflexivity. }
    apply (proj2 (tm_eval_in_store_restrict_fv_subset
      σ e2 vf X ltac:(set_solver))).
    eapply tm_eval_in_store_agree_on_fv.
    2: exact Heval2.
    eapply storeA_restrict_eq_mono; [|exact Hσ_eq].
    set_solver.
  - assert (Hres2 : tm_fiber_result_on m X e2 σ0 vf).
    {
      exists σ. split; [exact Hσ|]. split; [exact HσX|].
      apply (proj1 (tm_eval_in_store_restrict_fv_subset
        σ e2 vf X ltac:(set_solver))).
      exact Heval_fun.
    }
    destruct (proj2 (Heq σ0 Hσ0 vf) Hres2)
      as [σ1 [Hσ1 [Hσ1X Heval1]]].
    assert (Hσ_eq : store_restrict σ X = store_restrict σ1 X).
    { rewrite HσX, Hσ1X. reflexivity. }
    apply (proj2 (tm_eval_in_store_restrict_fv_subset
      σ e1 vf X ltac:(set_solver))).
    eapply tm_eval_in_store_agree_on_fv.
    2: exact Heval1.
    eapply storeA_restrict_eq_mono; [|exact Hσ_eq].
    set_solver.
Qed.

Lemma tm_fiber_equiv_tapp_fvar
    (m : WfWorldT) X e1 e2 y :
  fv_tm (tapp_tm e1 (vfvar y)) ∪ fv_tm (tapp_tm e2 (vfvar y)) ⊆ X ->
  wfworld_closed_on X m ->
  lc_tm e1 ->
  lc_tm e2 ->
  tm_fiber_equiv_on m X e1 e2 ->
  tm_fiber_equiv_on m X
    (tapp_tm e1 (vfvar y))
    (tapp_tm e2 (vfvar y)).
Proof.
  intros HfvX Hclosed Hlc1 Hlc2 Heq σ0 Hσ0 v.
  split; intros [σ [Hσ [HσX Heval]]].
  - exists σ. split; [exact Hσ|]. split; [exact HσX|].
    assert (HσX_closed : store_closed (store_restrict σ X)).
    { eapply wfworld_closed_on_store_restrict_closed; eauto. }
    assert (Hfv_app1 : fv_tm (tapp_tm e1 (vfvar y)) ⊆ X) by set_solver.
    assert (Hfv_app2 : fv_tm (tapp_tm e2 (vfvar y)) ⊆ X) by set_solver.
    assert (Hfun_equiv :
        forall vf,
          tm_eval_in_store (store_restrict σ X) e1 vf <->
          tm_eval_in_store (store_restrict σ X) e2 vf).
    {
      eapply tm_fiber_equiv_restrict_eval_iff; eauto.
      cbn [fv_tm fv_value] in HfvX. set_solver.
    }
    apply (proj1 (tm_eval_in_store_restrict_fv_subset
      σ (tapp_tm e2 (vfvar y)) v X Hfv_app2)).
    apply (proj1 (tm_eval_in_store_tapp_tm_fun_equiv
      (store_restrict σ X) e1 e2 y v HσX_closed Hlc1 Hlc2 Hfun_equiv)).
    apply (proj2 (tm_eval_in_store_restrict_fv_subset
        σ (tapp_tm e1 (vfvar y)) v X Hfv_app1)).
    exact Heval.
  - exists σ. split; [exact Hσ|]. split; [exact HσX|].
    assert (HσX_closed : store_closed (store_restrict σ X)).
    { eapply wfworld_closed_on_store_restrict_closed; eauto. }
    assert (Hfv_app1 : fv_tm (tapp_tm e1 (vfvar y)) ⊆ X) by set_solver.
    assert (Hfv_app2 : fv_tm (tapp_tm e2 (vfvar y)) ⊆ X) by set_solver.
    assert (Hfun_equiv :
        forall vf,
          tm_eval_in_store (store_restrict σ X) e1 vf <->
          tm_eval_in_store (store_restrict σ X) e2 vf).
    {
      eapply tm_fiber_equiv_restrict_eval_iff; eauto.
      cbn [fv_tm fv_value] in HfvX. set_solver.
    }
    apply (proj1 (tm_eval_in_store_restrict_fv_subset
      σ (tapp_tm e1 (vfvar y)) v X Hfv_app1)).
    apply (proj2 (tm_eval_in_store_tapp_tm_fun_equiv
      (store_restrict σ X) e1 e2 y v HσX_closed Hlc1 Hlc2 Hfun_equiv)).
    apply (proj2 (tm_eval_in_store_restrict_fv_subset
        σ (tapp_tm e2 (vfvar y)) v X Hfv_app2)).
    exact Heval.
Qed.

Lemma tm_fiber_equiv_open_app_fvar
    (m : WfWorldT) X e1 e2 y :
  fv_tm (tapp_tm e1 (vfvar y)) ∪ fv_tm (tapp_tm e2 (vfvar y)) ⊆ X ->
  wfworld_closed_on X m ->
  lc_tm e1 ->
  lc_tm e2 ->
  tm_fiber_equiv_on m X e1 e2 ->
  tm_fiber_equiv_on m X
    (open_tm 0 (vfvar y) (tapp_tm (tm_shift 0 e1) (vbvar 0)))
    (open_tm 0 (vfvar y) (tapp_tm (tm_shift 0 e2) (vbvar 0))).
Proof.
  intros Hfv Hclosed Hlc1 Hlc2 Heq.
  rewrite !open_tapp_tm_shift_bvar0_lc by assumption.
  eapply tm_fiber_equiv_tapp_fvar; eauto.
Qed.

Lemma tm_total_equiv_tapp_fvar
    (m : WfWorldT) e1 e2 y :
  wfworld_closed_on
    (fv_tm (tapp_tm e1 (vfvar y)) ∪ fv_tm (tapp_tm e2 (vfvar y))) m ->
  lc_tm e1 ->
  lc_tm e2 ->
  tm_equiv_on m e1 e2 ->
  tm_total_equiv_on m e1 e2 ->
  tm_total_equiv_on m
    (tapp_tm e1 (vfvar y))
    (tapp_tm e2 (vfvar y)).
Proof.
  intros Hclosed Hlc1 Hlc2 Heq Htotal σ Hσ.
  set (X := fv_tm (tapp_tm e1 (vfvar y)) ∪
            fv_tm (tapp_tm e2 (vfvar y))).
  set (σX := store_restrict σ X : StoreT).
  assert (HσX_closed : store_closed σX).
  { subst σX X. eapply wfworld_closed_on_store_restrict_closed; eauto. }
  assert (Hfv_app1 : fv_tm (tapp_tm e1 (vfvar y)) ⊆ X)
    by (subst X; set_solver).
  assert (Hfv_app2 : fv_tm (tapp_tm e2 (vfvar y)) ⊆ X)
    by (subst X; set_solver).
  assert (Hfv_e1 : fv_tm e1 ⊆ X).
  {
    subst X. cbn [fv_tm fv_value].
    unfold tapp_tm. cbn [fv_tm fv_value].
    set_solver.
  }
  assert (Hfv_e2 : fv_tm e2 ⊆ X).
  {
    subst X. cbn [fv_tm fv_value].
    unfold tapp_tm. cbn [fv_tm fv_value].
    set_solver.
  }
  assert (Hfun_equiv : forall vf,
      tm_eval_in_store σX e1 vf <->
      tm_eval_in_store σX e2 vf).
  {
    intros vf. split; intros Heval_fun.
    - apply (proj2 (tm_eval_in_store_restrict_fv_subset
        σ e2 vf X Hfv_e2)).
      apply (proj1 (Heq σ vf Hσ)).
      apply (proj1 (tm_eval_in_store_restrict_fv_subset
        σ e1 vf X Hfv_e1)).
      subst σX. exact Heval_fun.
    - apply (proj2 (tm_eval_in_store_restrict_fv_subset
        σ e1 vf X Hfv_e1)).
      apply (proj2 (Heq σ vf Hσ)).
      apply (proj1 (tm_eval_in_store_restrict_fv_subset
        σ e2 vf X Hfv_e2)).
      subst σX. exact Heval_fun.
  }
  assert (Hfun_total :
      must_terminating (lstore_instantiate_tm (lstore_lift_free σX) e1) <->
      must_terminating (lstore_instantiate_tm (lstore_lift_free σX) e2)).
  {
    specialize (Htotal σ Hσ) as [Htotal12 Htotal21].
    assert (Hagree1 : store_restrict σX (fv_tm e1) =
      store_restrict σ (fv_tm e1)).
    { subst σX. rewrite storeA_restrict_twice_subset by exact Hfv_e1.
      reflexivity. }
    assert (Hagree2 : store_restrict σX (fv_tm e2) =
      store_restrict σ (fv_tm e2)).
    { subst σX. rewrite storeA_restrict_twice_subset by exact Hfv_e2.
      reflexivity. }
    split; intros Hsn.
    - apply (proj2 (tm_must_terminating_agree_on_fv
        σX σ e2 Hlc2 Hagree2)).
      apply Htotal12.
      apply (proj1 (tm_must_terminating_agree_on_fv
        σX σ e1 Hlc1 Hagree1)).
      exact Hsn.
    - apply (proj2 (tm_must_terminating_agree_on_fv
        σX σ e1 Hlc1 Hagree1)).
      apply Htotal21.
      apply (proj1 (tm_must_terminating_agree_on_fv
        σX σ e2 Hlc2 Hagree2)).
      exact Hsn.
  }
  assert (HappsX :
      must_terminating
        (lstore_instantiate_tm (lstore_lift_free σX)
          (tapp_tm e1 (vfvar y))) <->
      must_terminating
        (lstore_instantiate_tm (lstore_lift_free σX)
          (tapp_tm e2 (vfvar y)))).
  {
    unfold tm_eval_in_store, expr_eval_in_store in Hfun_equiv.
    rewrite !lstore_instantiate_tm_no_bvars in Hfun_equiv by
      (try apply lc_lstore_lift_free;
       rewrite ?lstore_free_part_lift_free; exact (proj1 HσX_closed)).
    rewrite !lstore_free_part_lift_free in Hfun_equiv.
    rewrite !lstore_instantiate_tm_no_bvars in Hfun_total by
      (try apply lc_lstore_lift_free;
       rewrite ?lstore_free_part_lift_free; exact (proj1 HσX_closed)).
    rewrite !lstore_free_part_lift_free in Hfun_total.
    rewrite !lstore_instantiate_tm_no_bvars by
      (try apply lc_lstore_lift_free;
       rewrite ?lstore_free_part_lift_free; exact (proj1 HσX_closed)).
    rewrite !lstore_free_part_lift_free.
    rewrite !subst_map_tm_eq_msubst.
    rewrite !msubst_tapp_tm_lc_arg by
      (constructor || exact (proj2 HσX_closed)).
    eapply must_terminating_tapp_tm_fun_equiv.
    - change (lc_tm (m{σX} e1)).
      apply msubst_lc; [exact (proj2 HσX_closed)|exact Hlc1].
    - change (lc_tm (m{σX} e2)).
      apply msubst_lc; [exact (proj2 HσX_closed)|exact Hlc2].
    - change (lc_value (m{σX} (vfvar y))).
      apply msubst_lc; [exact (proj2 HσX_closed)|constructor].
    - exact Hfun_equiv.
    - exact Hfun_total.
  }
  assert (Hagree_app1 : store_restrict σX (fv_tm (tapp_tm e1 (vfvar y))) =
    store_restrict σ (fv_tm (tapp_tm e1 (vfvar y)))).
  { subst σX. rewrite storeA_restrict_twice_subset by exact Hfv_app1.
    reflexivity. }
  assert (Hagree_app2 : store_restrict σX (fv_tm (tapp_tm e2 (vfvar y))) =
    store_restrict σ (fv_tm (tapp_tm e2 (vfvar y)))).
  { subst σX. rewrite storeA_restrict_twice_subset by exact Hfv_app2.
    reflexivity. }
  pose proof (lc_tapp_tm e1 (vfvar y) Hlc1 ltac:(constructor)) as Hlc_app1.
  pose proof (lc_tapp_tm e2 (vfvar y) Hlc2 ltac:(constructor)) as Hlc_app2.
  split; intros Hsn.
  - apply (proj1 (tm_must_terminating_agree_on_fv
      σX σ (tapp_tm e2 (vfvar y)) Hlc_app2 Hagree_app2)).
    apply (proj1 HappsX).
    apply (proj2 (tm_must_terminating_agree_on_fv
      σX σ (tapp_tm e1 (vfvar y)) Hlc_app1 Hagree_app1)).
    exact Hsn.
  - apply (proj1 (tm_must_terminating_agree_on_fv
      σX σ (tapp_tm e1 (vfvar y)) Hlc_app1 Hagree_app1)).
    apply (proj2 HappsX).
    apply (proj2 (tm_must_terminating_agree_on_fv
      σX σ (tapp_tm e2 (vfvar y)) Hlc_app2 Hagree_app2)).
    exact Hsn.
Qed.

Lemma tm_total_equiv_tapp_tm_ret
    (m : WfWorldT) vf y :
  wfworld_closed_on
    (fv_tm (tapp_tm (tret vf) (vfvar y)) ∪
     fv_tm (tapp vf (vfvar y))) m ->
  lc_value vf ->
  tm_total_equiv_on m
    (tapp_tm (tret vf) (vfvar y))
    (tapp vf (vfvar y)).
Proof.
  intros Hclosed Hvf σ Hσ.
  set (X := fv_tm (tapp_tm (tret vf) (vfvar y)) ∪
            fv_tm (tapp vf (vfvar y))).
  set (σX := store_restrict σ X : StoreT).
  assert (HσX_closed : store_closed σX).
  { subst σX X. eapply wfworld_closed_on_store_restrict_closed; eauto. }
  assert (Hfv_src : fv_tm (tapp_tm (tret vf) (vfvar y)) ⊆ X)
    by (subst X; set_solver).
  assert (Hfv_tgt : fv_tm (tapp vf (vfvar y)) ⊆ X)
    by (subst X; set_solver).
  assert (HappsX :
      must_terminating
        (lstore_instantiate_tm (lstore_lift_free σX)
          (tapp_tm (tret vf) (vfvar y))) <->
      must_terminating
        (lstore_instantiate_tm (lstore_lift_free σX)
          (tapp vf (vfvar y)))).
  {
    rewrite !lstore_instantiate_tm_no_bvars by
      (try apply lc_lstore_lift_free;
       rewrite ?lstore_free_part_lift_free; exact (proj1 HσX_closed)).
    rewrite !lstore_free_part_lift_free.
    rewrite !subst_map_tm_eq_msubst.
    rewrite msubst_tapp_tm_lc_arg by
      (constructor || exact (proj2 HσX_closed)).
    rewrite msubst_tapp, msubst_ret.
    eapply must_terminating_tapp_tm_ret_equiv.
    - change (lc_value (m{σX} vf)).
      apply msubst_lc; [exact (proj2 HσX_closed)|exact Hvf].
    - change (lc_value (m{σX} (vfvar y))).
      apply msubst_lc; [exact (proj2 HσX_closed)|constructor].
  }
  assert (Hagree_src : store_restrict σX
      (fv_tm (tapp_tm (tret vf) (vfvar y))) =
    store_restrict σ (fv_tm (tapp_tm (tret vf) (vfvar y)))).
  { subst σX. rewrite storeA_restrict_twice_subset by exact Hfv_src.
    reflexivity. }
  assert (Hagree_tgt : store_restrict σX (fv_tm (tapp vf (vfvar y))) =
    store_restrict σ (fv_tm (tapp vf (vfvar y)))).
  { subst σX. rewrite storeA_restrict_twice_subset by exact Hfv_tgt.
    reflexivity. }
  pose proof (lc_tapp_tm (tret vf) (vfvar y)
    ltac:(constructor; exact Hvf) ltac:(constructor)) as Hlc_src.
  assert (Hlc_tgt : lc_tm (tapp vf (vfvar y))).
  { constructor; [exact Hvf|constructor]. }
  split; intros Hsn.
  - apply (proj1 (tm_must_terminating_agree_on_fv
      σX σ (tapp vf (vfvar y)) Hlc_tgt Hagree_tgt)).
    apply (proj1 HappsX).
    apply (proj2 (tm_must_terminating_agree_on_fv
      σX σ (tapp_tm (tret vf) (vfvar y)) Hlc_src Hagree_src)).
    exact Hsn.
  - apply (proj1 (tm_must_terminating_agree_on_fv
      σX σ (tapp_tm (tret vf) (vfvar y)) Hlc_src Hagree_src)).
    apply (proj2 HappsX).
    apply (proj2 (tm_must_terminating_agree_on_fv
      σX σ (tapp vf (vfvar y)) Hlc_tgt Hagree_tgt)).
    exact Hsn.
Qed.


End TypeDenote.
