(** * BasicDenotation.TermTLet

    Split out from [Term.v] to keep individual proof files small. *)

From ContextBasicDenotation Require Import Notation StoreTyping.
From ContextBasicDenotation Require Import TermSyntax TermEval TermOpen TermExtension.

Section TermDenotation.

Lemma tm_eval_in_store_tlete_elim_core e1 e2 x σ v :
  store_closed σ ->
  x ∉ dom σ ∪ fv_tm e2 ->
  tm_eval_in_store σ (tlete e1 e2) v ->
  exists vx,
    tm_eval_in_store σ e1 vx /\
    tm_eval_in_store (<[x := vx]> σ) (open_tm 0 (vfvar x) e2) v.
Proof.
  intros Hclosed Hfresh Heval.
  unfold tm_eval_in_store, expr_eval_in_store in *.
  rewrite lstore_instantiate_tm_no_bvars in Heval.
  2:{ apply lc_lstore_lift_free. }
  2:{ rewrite lstore_free_part_lift_free. exact (proj1 Hclosed). }
  rewrite lstore_free_part_lift_free in Heval.
  rewrite subst_map_lete in Heval.
  apply reduction_lete in Heval as [vx [He1 He2]].
  exists vx. split.
  - rewrite lstore_instantiate_tm_no_bvars.
    + rewrite lstore_free_part_lift_free. exact He1.
    + apply lc_lstore_lift_free.
    + rewrite lstore_free_part_lift_free. exact (proj1 Hclosed).
  - pose proof (steps_regular2 _ _ He1) as Hret.
    apply lc_ret_iff_value in Hret as Hvx_lc.
    rewrite lstore_lift_free_insert.
    rewrite lstore_instantiate_tm_insert_open by
      (try exact Hclosed; try exact Hvx_lc; exact Hfresh).
    rewrite lstore_instantiate_tm_at_lc_lstore.
    + rewrite lstore_free_part_lift_free. exact He2.
    + apply lc_lstore_lift_free.
    + rewrite lstore_free_part_lift_free. exact (proj1 Hclosed).
Qed.

Lemma tm_eval_in_store_tlete_intro_core e1 e2 x σ vx v :
  store_closed σ ->
  x ∉ dom σ ∪ fv_tm e2 ->
  body_tm (lstore_instantiate_tm_at 1 (lstore_lift_free σ : LStoreT) e2) ->
  tm_eval_in_store σ e1 vx ->
  tm_eval_in_store (<[x := vx]> σ) (open_tm 0 (vfvar x) e2) v ->
  tm_eval_in_store σ (tlete e1 e2) v.
Proof.
  intros Hclosed Hfresh Hbody He1 He2.
  unfold tm_eval_in_store, expr_eval_in_store in *.
  rewrite lstore_instantiate_tm_no_bvars in He1.
  2:{ apply lc_lstore_lift_free. }
  2:{ rewrite lstore_free_part_lift_free. exact (proj1 Hclosed). }
  rewrite lstore_free_part_lift_free in He1.
  pose proof (steps_regular2 _ _ He1) as Hret.
  apply lc_ret_iff_value in Hret as Hvx_lc.
  rewrite lstore_lift_free_insert in He2.
  rewrite lstore_instantiate_tm_insert_open in He2 by
    (try exact Hclosed; try exact Hvx_lc; exact Hfresh).
  rewrite lstore_instantiate_tm_at_lc_lstore in He2.
  2:{ apply lc_lstore_lift_free. }
  2:{ rewrite lstore_free_part_lift_free. exact (proj1 Hclosed). }
  rewrite lstore_free_part_lift_free in He2.
  rewrite lstore_instantiate_tm_at_lc_lstore in Hbody.
  2:{ apply lc_lstore_lift_free. }
  2:{ rewrite lstore_free_part_lift_free. exact (proj1 Hclosed). }
  rewrite lstore_free_part_lift_free in Hbody.
  rewrite lstore_instantiate_tm_no_bvars.
  2:{ apply lc_lstore_lift_free. }
  2:{ rewrite lstore_free_part_lift_free. exact (proj1 Hclosed). }
  rewrite lstore_free_part_lift_free, subst_map_lete.
  eapply reduction_lete_intro; eauto.
Qed.

Lemma tm_eval_in_store_tlete_intro_closed_on e1 e2 x σ vx v :
  store_closed (store_restrict σ (fv_tm (tlete e1 e2))) ->
  lc_tm (tlete e1 e2) ->
  x ∉ dom σ ∪ fv_tm e2 ->
  tm_eval_in_store (store_restrict σ (fv_tm (tlete e1 e2))) e1 vx ->
  tm_eval_in_store
    (<[x := vx]> (store_restrict σ (fv_tm (tlete e1 e2))))
    (open_tm 0 (vfvar x) e2) v ->
  tm_eval_in_store σ (tlete e1 e2) v.
Proof.
  intros Hclosed Hlc Hfresh He1 He2.
  apply (proj1 (tm_eval_in_store_restrict_fv_closed_on
    σ (tlete e1 e2) v (proj1 Hclosed))).
  eapply tm_eval_in_store_tlete_intro_core.
  - exact Hclosed.
  - intros Hbad. apply Hfresh.
    apply elem_of_union in Hbad as [Hbad|Hbad].
    + apply elem_of_union. left.
      apply elem_of_dom in Hbad as [u Hlook].
      apply storeA_restrict_lookup_some in Hlook as [_ Hlook].
      apply elem_of_dom_2 in Hlook. exact Hlook.
    + apply elem_of_union. right. exact Hbad.
  - apply lc_lete_iff_body in Hlc as [_ Hbody].
    rewrite lstore_instantiate_tm_at_lc_lstore.
    + rewrite lstore_free_part_lift_free.
      eapply body_tm_msubst.
      * exact (proj1 Hclosed).
      * exact (proj2 Hclosed).
      * exact Hbody.
    + apply lc_lstore_lift_free.
    + rewrite lstore_free_part_lift_free. exact (proj1 Hclosed).
  - exact He1.
  - exact He2.
Qed.

Lemma tm_eval_in_store_tlete_elim_closed_on e1 e2 x σ v :
  store_closed (store_restrict σ (fv_tm (tlete e1 e2))) ->
  x ∉ fv_tm (tlete e1 e2) ->
  x ∉ fv_tm e2 ->
  tm_eval_in_store σ (tlete e1 e2) v ->
  exists vx,
    tm_eval_in_store (store_restrict σ (fv_tm e1)) e1 vx /\
    tm_eval_in_store
      (<[x := vx]> (store_restrict σ (fv_tm (tlete e1 e2))))
      (e2 ^^ x) v.
Proof.
  intros Hclosed Hxlet Hxe2 Heval.
  set (σT := store_restrict σ (fv_tm (tlete e1 e2))).
  assert (HevalT : tm_eval_in_store σT (tlete e1 e2) v).
  {
    subst σT.
    apply (proj2 (tm_eval_in_store_restrict_fv_closed_on
      σ (tlete e1 e2) v (proj1 Hclosed))).
    exact Heval.
  }
  assert (HfreshT : x ∉ dom (σT : gmap atom value) ∪ fv_tm e2).
  {
    subst σT.
    intros Hbad. apply elem_of_union in Hbad as [Hbad|Hbad].
    - rewrite storeA_restrict_dom in Hbad. set_solver.
    - exact (Hxe2 Hbad).
  }
  destruct (tm_eval_in_store_tlete_elim_core e1 e2 x σT v
    Hclosed HfreshT HevalT) as [vx [He1T He2]].
  exists vx. split; [|exact He2].
  assert (Hagree :
    store_restrict σT (fv_tm e1) =
    store_restrict (store_restrict σ (fv_tm e1)) (fv_tm e1)).
  {
    subst σT.
    rewrite (storeA_restrict_twice_subset σ (fv_tm (tlete e1 e2)) (fv_tm e1)).
    - rewrite storeA_restrict_twice_same. reflexivity.
    - cbn [fv_tm]. set_solver.
  }
  apply (proj1 (tm_eval_in_store_agree_on_fv
    σT (store_restrict σ (fv_tm e1)) e1 vx Hagree)).
  exact He1T.
Qed.

Lemma result_extension_store_lookup_output e x Fx m mx σ vx :
  expr_result_extension_witness e x Fx ->
  res_extend_by m Fx mx ->
  worldA_stores (mx : WorldT) σ ->
  tm_eval_in_store (store_restrict σ (fv_tm e)) e vx ->
  σ !! x = Some vx.
Proof.
  intros HFx Hext Hσmx Heσ.
  destruct HFx as [Hx_fv [Hin Hout] Hrel].
  apply (proj1 (resA_extend_by_store_iff m Fx mx σ Hext)) in Hσmx.
  destruct Hσmx as [σm [we [σe [Hσm [HFrel [Hσe ->]]]]]].
  set (σX := store_restrict σm (fv_tm e)).
  assert (HσX_dom : dom (σX : StoreT) = fv_tm e).
  {
    subst σX.
    change (dom (storeA_restrict σm (fv_tm e) : gmap atom value) =
      fv_tm e).
    rewrite storeA_restrict_dom.
    pose proof (wfworldA_store_dom m σm Hσm) as Hdomσm.
    change (dom (σm : StoreT) = world_dom (m : WorldT)) in Hdomσm.
    pose proof (res_extend_by_input_dom m Fx mx Hext) as Hin_sub.
    unfold ext_in in Hin. rewrite Hin in Hin_sub.
    set_solver.
  }
  assert (HFσX : ext_rel Fx σX we).
  {
    subst σX.
    replace (store_restrict σm (fv_tm e))
      with (store_restrict σm (ext_in Fx)) by
      (unfold ext_in; unfold ext_in in Hin; rewrite Hin; reflexivity).
    exact HFrel.
  }
  assert (HeσX : tm_eval_in_store σX e vx).
  {
    subst σX.
    apply (proj2 (tm_eval_in_store_restrict_fv_exact σm e vx)).
    pose proof (tm_eval_in_store_agree_on_fv
      (σm ∪ σe) σm e vx) as Hagree_eval.
    apply Hagree_eval.
    + apply storeA_map_eq. intros a.
      rewrite !storeA_restrict_lookup.
      destruct (decide (a ∈ fv_tm e)) as [Ha|Ha]; [|reflexivity].
      pose proof (res_extend_by_output_fresh m Fx mx Hext) as Hfresh_out.
      change (ext_out Fx ## world_dom (m : WorldT)) in Hfresh_out.
      rewrite Hout in Hfresh_out.
      pose proof (wfworldA_store_dom m σm Hσm) as Hdomσm.
      change (dom (σm : StoreT) = world_dom (m : WorldT)) in Hdomσm.
      assert (a ∈ dom (σm : StoreT)).
      {
        pose proof (res_extend_by_input_dom m Fx mx Hext) as Hin_sub.
        unfold ext_in in Hin. rewrite Hin in Hin_sub.
        rewrite Hdomσm. set_solver.
      }
      change (a ∈ dom (σm : gmap atom value)) in H.
      apply elem_of_dom in H as [u Hu].
      apply lookup_union_l'. exists u. exact Hu.
    + apply (proj1 (tm_eval_in_store_agree_on_fv
        (store_restrict (σm ∪ σe) (fv_tm e)) (σm ∪ σe) e vx
        ltac:(apply storeA_restrict_twice_same))).
      exact Heσ.
  }
  pose proof (expr_result_extension_apply_total_iff
    e x Fx σX we
    {| expr_result_extension_witness_fresh := Hx_fv;
       expr_result_extension_witness_shape := conj Hin Hout;
       expr_result_extension_witness_rel := Hrel |}
    HσX_dom HFσX (ex_intro _ vx HeσX) σe) as Hσe_iff.
  apply Hσe_iff in Hσe as [u [He_u ->]].
  assert (u = vx).
  {
    unfold tm_eval_in_store, expr_eval_in_store in He_u, HeσX.
    eapply steps_result_unique; eauto.
  }
  subst u.
  assert (Hxσm : x ∉ dom (σm : gmap atom value)).
  {
    pose proof (res_extend_by_output_fresh m Fx mx Hext) as Hfresh_out.
    change (ext_out Fx ## world_dom (m : WorldT)) in Hfresh_out.
    rewrite Hout in Hfresh_out.
    pose proof (wfworldA_store_dom m σm Hσm) as Hdomσm.
    change (dom (σm : StoreT) = world_dom (m : WorldT)) in Hdomσm.
    rewrite <- Hdomσm in Hfresh_out. set_solver.
  }
  change (((σm : gmap atom value) ∪ ({[x := vx]} : gmap atom value)) !! x =
    Some vx).
  transitivity (({[x := vx]} : gmap atom value) !! x).
  - apply (lookup_union_r (M:=gmap atom) (A:=value)
      (σm : gmap atom value) ({[x := vx]} : gmap atom value) x).
    apply not_elem_of_dom. exact Hxσm.
  - apply map_lookup_singleton.
Qed.

Lemma lstore_open_alias_restrict
    (e : tm) (σ : StoreT) x y vx :
  σ !! x = Some vx ->
  y ∉ dom (σ : gmap atom value) ->
  x ∉ fv_tm e ->
  y ∉ fv_tm e ->
  storeA_restrict
    (lstore_swap (LVBound 0) (LVFree x) (lstore_lift_free σ) : LStoreT)
    (tm_lvars e) =
  storeA_restrict
    (lstore_swap (LVBound 0) (LVFree y)
      (lstore_lift_free (<[y := vx]> σ)))
    (tm_lvars e).
Proof.
  intros Hx Hyσ Hxe Hye.
  apply storeA_map_eq. intros z.
  rewrite !storeA_restrict_lookup.
  destruct (decide (z ∈ tm_lvars e)) as [Hz|Hz]; [|reflexivity].
  rewrite !lstore_swap_lookup_inv_value.
  destruct z as [k|a].
  - destruct k as [|k].
    + base_swap_normalize.
      rewrite !lstore_lift_free_lookup_free.
      change (σ !! x =
        ((<[y := vx]> (σ : gmap atom value) : gmap atom value) !! y)).
      transitivity (Some vx).
      * exact Hx.
      * symmetry. apply map_lookup_insert.
    + base_swap_normalize.
      rewrite !lstore_lift_free_lookup_bound. reflexivity.
  - cbn [swap].
    destruct (decide (a = x)) as [->|Hax].
    {
      exfalso. apply Hxe.
      rewrite <- tm_lvars_fv.
      apply lvars_fv_elem. exact Hz.
    }
    destruct (decide (a = y)) as [->|Hay].
    {
      exfalso. apply Hye.
      rewrite <- tm_lvars_fv.
      apply lvars_fv_elem. exact Hz.
    }
    base_swap_normalize.
    rewrite !lstore_lift_free_lookup_free.
    transitivity (σ !! a).
    { reflexivity. }
    { symmetry. apply map_lookup_insert_ne. congruence. }
Qed.

Lemma tm_eval_in_store_open_alias
    e σ x y vx v :
  σ !! x = Some vx ->
  y ∉ dom (σ : gmap atom value) ->
  x ∉ fv_tm e ->
  y ∉ fv_tm e ->
  tm_lvars (e ^^ x) ⊆ lvars_of_atoms (dom (σ : gmap atom value)) ->
  tm_eval_in_store σ (e ^^ x) v <->
  tm_eval_in_store (<[y := vx]> σ) (e ^^ y) v.
Proof.
  intros Hx Hyσ Hxe Hye Hscope.
  unfold tm_eval_in_store.
  change (tm_lvars (e ^^ x)) with
    (tm_lvars (open_tm 0 (vfvar x) e)) in Hscope.
  change (e ^^ x) with (open_tm 0 (vfvar x) e).
  change (e ^^ y) with (open_tm 0 (vfvar y) e).
  assert (Hdomx :
      lvars_open 0 x (tm_lvars e) ⊆
      dom (lstore_lift_free σ : LStoreT)).
  {
    rewrite <- (tm_lvars_open 0 x e Hxe).
    rewrite dom_lstore_lift_free. exact Hscope.
  }
  assert (Hdomy :
      lvars_open 0 y (tm_lvars e) ⊆
      dom (lstore_lift_free (<[y := vx]> σ) : LStoreT)).
  {
    rewrite <- (tm_lvars_open 0 y e Hye).
    rewrite dom_lstore_lift_free.
    intros z Hz.
    rewrite (tm_lvars_open 0 y e Hye) in Hz.
    rewrite (tm_lvars_open 0 x e Hxe) in Hscope.
    assert (Hzx_or : z ∈ lvars_open 0 x (tm_lvars e) ∪ {[LVFree y]}).
    {
      clear -Hz Hxe Hye.
      assert (HxLV : LVFree x ∉ tm_lvars e).
      { apply tm_lvars_free_notin_of_fv. exact Hxe. }
      assert (HyLV : LVFree y ∉ tm_lvars e).
      { apply tm_lvars_free_notin_of_fv. exact Hye. }
      clear Hxe Hye.
      rewrite set_swap_elem in Hz.
      apply elem_of_union.
      destruct z as [k|a].
      - destruct k as [|k].
        + rewrite swap_l in Hz.
          exfalso. exact (HyLV Hz).
        + left. apply set_swap_elem.
          rewrite swap_fresh in Hz by discriminate.
          rewrite swap_fresh by discriminate.
          exact Hz.
      - destruct (decide (a = y)) as [->|Hay].
        + right. apply elem_of_singleton. reflexivity.
        + destruct (decide (a = x)) as [->|Hax].
          * rewrite swap_fresh in Hz by (try discriminate; congruence).
            exfalso. exact (HxLV Hz).
          * left. apply set_swap_elem.
            rewrite swap_fresh in Hz by (try discriminate; congruence).
            rewrite swap_fresh by (try discriminate; congruence).
            exact Hz.
    }
    apply elem_of_union in Hzx_or as [Hzx|Hzy].
    - specialize (Hscope _ Hzx).
      unfold lvars_of_atoms in *.
      apply elem_of_map in Hscope as [a [-> Ha]].
      apply elem_of_map. exists a. split; [reflexivity|].
      apply elem_of_dom in Ha as [u Hu].
      apply elem_of_dom.
      destruct (decide (a = y)) as [->|Hay].
      + exists vx. apply map_lookup_insert.
      + exists u.
        change (((<[y := vx]> (σ : gmap atom value) : gmap atom value) !! a) =
          Some u).
        transitivity (σ !! a).
        * apply lookup_insert_ne. congruence.
        * exact Hu.
    - apply elem_of_singleton in Hzy. subst z.
      unfold lvars_of_atoms. apply elem_of_map.
      exists y. split; [reflexivity|].
      apply elem_of_dom. exists vx.
      change (((<[y := vx]> (σ : gmap atom value) : gmap atom value) !! y) =
        Some vx).
      apply map_lookup_insert.
  }
  rewrite <- (expr_eval_in_store_open_back_iff 0 x e v
    (lstore_lift_free σ)) by (exact Hxe || exact Hdomx).
  rewrite <- (expr_eval_in_store_open_back_iff 0 y e v
    (lstore_lift_free (<[y := vx]> σ))) by (exact Hye || exact Hdomy).
  unfold expr_eval_in_store.
  rewrite <- (expr_eval_in_store_restrict_lvars e
    (lstore_swap (LVBound 0) (LVFree x) (lstore_lift_free σ)) (tm_lvars e) v
    ltac:(set_solver)).
  rewrite <- (expr_eval_in_store_restrict_lvars e
    (lstore_swap (LVBound 0) (LVFree y) (lstore_lift_free (<[y := vx]> σ)))
    (tm_lvars e) v ltac:(set_solver)).
  rewrite (lstore_open_alias_restrict e σ x y vx Hx Hyσ Hxe Hye).
  reflexivity.
Qed.

Lemma expr_total_formula_models_iff e (m : WfWorldT) :
  res_models m (expr_total_formula e) <->
  logic_qualifier_denote (expr_total_lqual e) m.
Proof.
  unfold res_models, expr_total_formula.
  cbn [formula_measure res_models_fuel].
  split; [tauto |].
  intros Hden. split; [| exact Hden].
  destruct Hden as [_ [Hsub _]].
  exact Hsub.
Qed.

Lemma expr_total_formula_to_atom_world e (m : WfWorldT) :
  res_models m (expr_total_formula e) ->
  expr_total_on_atom_world e m.
Proof.
  intros Hmodels.
  apply expr_total_formula_models_iff in Hmodels.
  unfold expr_total_lqual, logic_qualifier_denote in Hmodels.
  destruct Hmodels as [Hlc [Hsub Htotal]].
  unfold expr_total_on_atom_world, expr_total_on in *.
  destruct Htotal as [_ Hstores].
  split.
  - rewrite res_lift_free_dom.
    intros v Hv.
    destruct v as [k|a].
    + exfalso. exact (Hlc _ Hv).
    + unfold lvars_of_atoms. apply elem_of_map.
      exists a. split; [reflexivity|].
      apply Hsub. apply lvars_fv_elem. exact Hv.
  - intros τ Hτ.
    destruct Hτ as [σ [Hσ ->]].
    assert (HτD :
        (@lw value _ (lworld_on_lift (tm_lvars e) m Hlc Hsub) : LWorldT)
        (storeA_restrict (lstore_lift_free σ : LStoreT) (tm_lvars e))).
    {
      unfold lworld_on_lift.
      cbn [lw lraw_world raw_worldA worldA_stores].
      exists (lstore_lift_free (storeA_restrict σ (lvars_fv (tm_lvars e))) : LStoreT).
      split.
      - exists (storeA_restrict σ (lvars_fv (tm_lvars e))). split.
        + change ((res_restrict m (lvars_fv (tm_lvars e)) : WorldT)
            (storeA_restrict σ (lvars_fv (tm_lvars e)))).
          exists σ. split; [exact Hσ|reflexivity].
        + reflexivity.
      - apply lstore_lift_free_restrict_fv_lvars_eq. exact Hlc.
    }
    destruct (Hstores _ HτD) as [v Heval].
    exists v.
    apply (proj1 (expr_eval_in_store_restrict_lvars e
      (lstore_lift_free σ : LStoreT) (tm_lvars e) v ltac:(set_solver))).
    exact Heval.
Qed.

Lemma expr_total_atom_world_to_formula e (m : WfWorldT) :
  expr_total_on_atom_world e m ->
  res_models m (expr_total_formula e).
Proof.
  intros Htotal.
  apply expr_total_formula_models_iff.
  unfold expr_total_lqual, logic_qualifier_denote.
  destruct Htotal as [Hdom Hstores].
  assert (Hlc : lc_lvars (tm_lvars e)).
  {
    unfold lc_lvars. intros v Hv.
    specialize (Hdom _ Hv).
    rewrite res_lift_free_dom in Hdom.
    unfold lvars_of_atoms in Hdom.
    apply elem_of_map in Hdom as [a [Hbad _]].
    destruct v as [k|b]; [discriminate|exact I].
  }
  assert (Hsub : lvars_fv (tm_lvars e) ⊆ world_dom (m : WorldT)).
  {
    intros a Ha.
    assert (LVFree a ∈ tm_lvars e) as HaD.
    { apply lvars_fv_elem. exact Ha. }
    specialize (Hdom _ HaD).
    rewrite res_lift_free_dom in Hdom.
    unfold lvars_of_atoms in Hdom.
    apply elem_of_map in Hdom as [b [Heq Hb]].
    inversion Heq. subst b. exact Hb.
  }
  exists Hlc, Hsub.
  unfold expr_total_on_atom_world, expr_total_on in Hstores.
  split.
  - unfold lworld_on_lift. cbn. intros v Hv.
    apply elem_of_intersection. split; [|exact Hv].
    destruct v as [k|a].
    + exfalso. exact (Hlc _ Hv).
    + unfold lvars_of_atoms. apply elem_of_map.
      exists a. split; [reflexivity|].
      apply elem_of_intersection. split.
      * apply Hsub. apply lvars_fv_elem. exact Hv.
      * apply lvars_fv_elem. exact Hv.
  - intros τ Hτ.
    unfold lworld_on_lift in Hτ.
    cbn [lw lraw_world raw_worldA worldA_stores] in Hτ.
    destruct Hτ as [τ0 [Hτ0 Hrestrict]]. subst τ.
    destruct Hτ0 as [σr [Hσr ->]].
    destruct Hσr as [σ [Hσ Hσr_eq]].
    subst σr.
    destruct (Hstores (lstore_lift_free σ)) as [v Heval].
    { exists σ. split; [exact Hσ|reflexivity]. }
    exists v.
    replace (storeA_restrict
        (lstore_lift_free (storeA_restrict σ (lvars_fv (tm_lvars e))) : LStoreT)
        (tm_lvars e))
      with (storeA_restrict (lstore_lift_free σ : LStoreT) (tm_lvars e)).
    2:{
      symmetry. apply lstore_lift_free_restrict_fv_lvars_eq. exact Hlc.
    }
    apply (proj2 (expr_eval_in_store_restrict_lvars e
      (lstore_lift_free σ : LStoreT) (tm_lvars e) v ltac:(set_solver))).
    exact Heval.
Qed.

Lemma expr_total_formula_res_subset e (m n : WfWorldT) :
  res_subset n m ->
  res_models m (expr_total_formula e) ->
  res_models n (expr_total_formula e).
Proof.
  intros Hsub Hm.
  apply expr_total_atom_world_to_formula.
  apply expr_total_formula_to_atom_world in Hm.
  destruct Hsub as [Hdom Hstores].
  destruct Hm as [Hdom_e Htotal].
  split.
  - rewrite !res_lift_free_dom in Hdom_e |- *.
    set_solver.
  - intros τ Hτ.
    destruct Hτ as [σ [Hσ ->]].
    apply Htotal.
    exists σ. split; [apply Hstores; exact Hσ | reflexivity].
Qed.

Lemma tlete_total_of_result_ext
    (Σ : lty_env) T e1 e2 x (m mx : WfWorldT) Fx :
  LVFree x ∉ dom Σ ->
  lty_env_to_atom_env Σ ⊢ₑ tlete e1 e2 ⋮ T ->
  res_models m (basic_world_formula Σ) ->
  expr_result_extension_witness e1 x Fx ->
  res_extend_by m Fx mx ->
  res_models m (expr_total_formula e1) ->
  res_models mx (expr_total_formula (e2 ^^ x)) ->
  res_models m (expr_total_formula (tlete e1 e2)).
Proof.
  intros HxΣ Hty Hbasic HFx Hext Htotal1 Htotal2.
  apply expr_total_atom_world_to_formula.
  pose proof (typing_tm_lc _ _ _ Hty) as Hlc_let.
  assert (Hfv_let : fv_tm (tlete e1 e2) ⊆ lvars_fv (dom Σ)).
  {
    pose proof (basic_typing_contains_fv_tm _ _ _ Hty) as Hfv_atom.
    pose proof (lvar_store_to_atom_store_dom_subset Σ) as Hdom.
    unfold lty_env_atom_dom in Hdom. set_solver.
  }
  pose proof (expr_total_formula_to_atom_world _ _ Htotal1) as Htotal1_atom.
  pose proof (expr_total_formula_to_atom_world _ _ Htotal2) as Htotal2_atom.
  pose proof Hbasic as Hbasic_den.
  apply basic_world_formula_models_iff in Hbasic_den as [_ [HΣdom _]].
  unfold expr_total_on_atom_world, expr_total_on in *.
  destruct Htotal1_atom as [_ Htotal1_stores].
  destruct Htotal2_atom as [_ Htotal2_stores].
  split.
  - rewrite (tm_lvars_lc_eq_atoms _ Hlc_let), res_lift_free_dom.
    unfold lvars_of_atoms.
    intros v Hv.
    apply elem_of_map in Hv as [a [-> Ha]].
    apply elem_of_map. exists a. split; [reflexivity|].
    apply HΣdom. apply Hfv_let. exact Ha.
  - intros τ Hτ.
    destruct Hτ as [σ [Hσ ->]].
    destruct (Htotal1_stores (lstore_lift_free σ)) as [vx He1].
    { exists σ. split; [exact Hσ|reflexivity]. }
    destruct HFx as [Hx_fv [Hin Hout] Hrel].
    assert (Hx_dom : x ∉ dom (σ : gmap atom value)).
    {
      pose proof (res_extend_by_output_fresh m Fx mx Hext) as Hfresh.
      change (ext_out Fx ## world_dom (m : WorldT)) in Hfresh.
      pose proof (wfworldA_store_dom m σ Hσ) as Hσdom.
      change (dom (σ : gmap atom value) = world_dom (m : WorldT)) in Hσdom.
      rewrite Hσdom.
      rewrite Hout in Hfresh. set_solver.
    }
    assert (Hx_let : x ∉ fv_tm (tlete e1 e2)).
    {
      intros Hx.
      apply HxΣ.
      apply lvars_fv_elem.
      apply Hfv_let in Hx.
      exact Hx.
    }
    assert (Hx_e2 : x ∉ fv_tm e2).
    { cbn [fv_tm] in Hx_let. set_solver. }
    set (σX := store_restrict σ (fv_tm e1)).
    assert (HσX_dom : dom (σX : gmap atom value) = fv_tm e1).
    {
      subst σX. rewrite storeA_restrict_dom.
      pose proof (res_extend_by_input_dom m Fx mx Hext) as Hin_sub.
      unfold ext_in in Hin_sub. rewrite <- Hin.
      pose proof (wfworldA_store_dom m σ Hσ) as Hσdom.
      change (dom (σ : gmap atom value) = world_dom (m : WorldT)) in Hσdom.
      rewrite Hσdom. set_solver.
    }
    assert (HFrel : ext_rel Fx σX (expr_result_output_world e1 x σX)).
    { subst σX. apply Hrel. exact HσX_dom. }
    assert (He1X : tm_eval_in_store σX e1 vx).
    {
      subst σX.
      apply (proj2 (tm_eval_in_store_restrict_fv_exact σ e1 vx)).
      exact He1.
    }
    pose proof (expr_result_extension_apply_total_iff
      e1 x Fx σX (expr_result_output_world e1 x σX)
      {| expr_result_extension_witness_fresh := Hx_fv;
         expr_result_extension_witness_shape := conj Hin Hout;
         expr_result_extension_witness_rel := Hrel |}
      HσX_dom HFrel (ex_intro _ vx He1X) ({[x := vx]} : StoreT)) as Hout_store.
    assert (Hσe :
      (expr_result_output_world e1 x σX : WorldT) ({[x := vx]} : StoreT)).
    {
      apply Hout_store.
      exists vx. split; [exact He1X|reflexivity].
    }
    assert (Hmx_store :
      (mx : WorldT) (σ ∪ ({[x := vx]} : StoreT))).
    {
      apply (proj2 (resA_extend_by_store_iff m Fx mx _ Hext)).
      exists σ, (expr_result_output_world e1 x σX), ({[x := vx]} : StoreT).
      split; [exact Hσ|].
      split.
      - replace (storeA_restrict σ (extA_in Fx)) with σX.
        + exact HFrel.
        + subst σX. unfold ext_in in Hin. rewrite Hin. reflexivity.
      - split; [exact Hσe|reflexivity].
    }
    destruct (Htotal2_stores (lstore_lift_free (σ ∪ ({[x := vx]} : StoreT))))
      as [v He2_union].
    { exists (σ ∪ ({[x := vx]} : StoreT)). split; [exact Hmx_store|reflexivity]. }
    assert (He2_insert :
      tm_eval_in_store
        (<[x := vx]> (store_restrict σ (fv_tm (tlete e1 e2))))
        (e2 ^^ x) v).
    {
      assert (Hagree :
        store_restrict (σ ∪ ({[x := vx]} : StoreT)) (fv_tm (e2 ^^ x)) =
        store_restrict (<[x := vx]> (store_restrict σ (fv_tm (tlete e1 e2))))
          (fv_tm (e2 ^^ x))).
      {
        apply store_insert_restrict_agree_on_open_fv.
        - cbn [fv_tm] in Hfv_let. set_solver.
        - exact Hx_let.
        - exact Hx_dom.
      }
      apply (proj1 (tm_eval_in_store_agree_on_fv
        (σ ∪ ({[x := vx]} : StoreT))
        (<[x := vx]> (store_restrict σ (fv_tm (tlete e1 e2))))
        (e2 ^^ x) v Hagree)).
      exact He2_union.
    }
    exists v.
    eapply tm_eval_in_store_tlete_intro_closed_on.
    + assert (Hsub_atoms :
        lvars_of_atoms (fv_tm (tlete e1 e2)) ⊆ dom Σ).
      {
        unfold lvars_of_atoms. intros lv Hlv.
        apply elem_of_map in Hlv as [a [-> Ha]].
        apply lvars_fv_elem. apply Hfv_let. exact Ha.
      }
      exact ((basic_world_formula_wfworld_closed_on_atoms
        Σ (fv_tm (tlete e1 e2)) m Hsub_atoms Hbasic) σ Hσ).
    + exact Hlc_let.
    + intros Hbad. apply elem_of_union in Hbad as [Hbad|Hbad].
      * exact (Hx_dom Hbad).
      * exact (Hx_e2 Hbad).
    + apply (proj2 (tm_eval_in_store_restrict_fv_subset
        σ e1 vx (fv_tm (tlete e1 e2)) ltac:(cbn [fv_tm]; set_solver))).
      exact He1.
    + exact He2_insert.
Qed.

Lemma expr_result_formula_models_iff e x (m : WfWorldT) :
  res_models m (expr_result_formula e x) <->
  logic_qualifier_denote (expr_result_lqual e x) m.
Proof.
  unfold res_models, expr_result_formula.
  cbn [formula_measure res_models_fuel].
  split; [tauto |].
  intros Hden. split; [| exact Hden].
  destruct Hden as [_ [Hsub _]].
  exact Hsub.
Qed.

Lemma expr_result_formula_to_atom_world e x (m : WfWorldT) :
  res_models m (expr_result_formula e x) ->
  expr_result_at_world e x (res_lift_free m : LWorldT).
Proof.
  intros Hmodels.
  apply expr_result_formula_models_iff in Hmodels.
  unfold expr_result_lqual, logic_qualifier_denote in Hmodels.
  destruct Hmodels as [Hlc [Hsub Hresult]].
  destruct Hresult as [Hx [Hdom Hstores]].
  split; [exact Hx|]. split.
  - rewrite res_lift_free_dom.
    intros v Hv.
    destruct v as [k|a].
    + exfalso. exact (Hlc _ Hv).
    + unfold lvars_of_atoms. apply elem_of_map.
      exists a. split; [reflexivity|].
      apply Hsub. apply lvars_fv_elem. exact Hv.
  - intros τ Hτ.
    destruct Hτ as [σ [Hσ ->]].
    assert (HτD :
        (@lw value _ (lworld_on_lift (tm_lvars e ∪ {[x]}) m Hlc Hsub) : LWorldT)
        (storeA_restrict (lstore_lift_free σ : LStoreT) (tm_lvars e ∪ {[x]}))).
    {
      unfold lworld_on_lift.
      cbn [lw lraw_world raw_worldA worldA_stores].
      exists (lstore_lift_free
        (storeA_restrict σ (lvars_fv (tm_lvars e ∪ {[x]}))) : LStoreT).
      split.
      - exists (storeA_restrict σ (lvars_fv (tm_lvars e ∪ {[x]}))). split.
        + change ((res_restrict m (lvars_fv (tm_lvars e ∪ {[x]})) : WorldT)
            (storeA_restrict σ (lvars_fv (tm_lvars e ∪ {[x]})))).
          exists σ. split; [exact Hσ|reflexivity].
        + reflexivity.
      - apply lstore_lift_free_restrict_fv_lvars_eq. exact Hlc.
    }
    specialize (Hstores _ HτD).
    destruct Hstores as [Hx' [v [Hlookup Heval]]].
    split; [exact Hx'|].
    exists v. split.
    + apply storeA_restrict_lookup_some in Hlookup as [_ Hlookup].
      exact Hlookup.
    + apply (proj1 (expr_eval_in_store_restrict_lvars e
        (lstore_lift_free σ : LStoreT) (tm_lvars e ∪ {[x]}) v
        ltac:(set_solver))).
      exact Heval.
Qed.

Lemma expr_result_atom_world_to_formula e x (m : WfWorldT) :
  expr_result_at_world e x (res_lift_free m : LWorldT) ->
  res_models m (expr_result_formula e x).
Proof.
  intros Hres.
  apply expr_result_formula_models_iff.
  unfold expr_result_lqual, logic_qualifier_denote.
  destruct Hres as [Hx [Hdom Hstores]].
  assert (Hlc : lc_lvars (tm_lvars e ∪ {[x]})).
  {
    unfold lc_lvars. intros v Hv.
    specialize (Hdom _ Hv).
    rewrite res_lift_free_dom in Hdom.
    unfold lvars_of_atoms in Hdom.
    apply elem_of_map in Hdom as [a [Hbad _]].
    destruct v as [k|b]; [discriminate|exact I].
  }
  assert (Hsub :
      lvars_fv (tm_lvars e ∪ {[x]}) ⊆ world_dom (m : WorldT)).
  {
    intros y Hy.
    assert (LVFree y ∈ tm_lvars e ∪ {[x]}) as HyD.
    { apply lvars_fv_elem. exact Hy. }
    specialize (Hdom _ HyD).
    rewrite res_lift_free_dom in Hdom.
    unfold lvars_of_atoms in Hdom.
    apply elem_of_map in Hdom as [a [Heq Ha]].
    inversion Heq. subst a. exact Ha.
  }
  exists Hlc, Hsub.
  apply expr_result_at_world_lworld_on_lift.
  exact (conj Hx (conj Hdom Hstores)).
Qed.

Lemma expr_result_extension_world_models_closed
    e x F (m mx : WfWorldT) :
  wfworld_closed_on (fv_tm e) m ->
  expr_result_extension_witness e x F ->
  res_extend_by m F mx ->
  expr_total_on_atom_world e m ->
  expr_result_at_world e (LVFree x) (res_lift_free mx : LWorldT).
Proof.
  intros Hclosed Hwitness Hext Htotal.
  destruct Hwitness as [Hx_fresh [Hin Hout] Hrel].
  unfold ext_in in Hin.
  unfold ext_out in Hout.
  destruct Htotal as [Htotal_dom Htotal_eval].
  split.
  - intros Hxin.
    apply Hx_fresh.
    rewrite <- tm_lvars_fv.
    apply lvars_fv_elem. exact Hxin.
  - split.
    + rewrite res_lift_free_dom.
      pose proof (res_extend_by_dom m F mx Hext) as Hmx_dom.
      replace (lvars_of_atoms (world_dom mx)) with
        (lvars_of_atoms (world_dom m ∪ {[x]})).
      2:{ rewrite Hmx_dom, Hout. reflexivity. }
      intros z Hz.
      apply elem_of_union in Hz as [Hz|Hz].
      * specialize (Htotal_dom _ Hz).
        rewrite res_lift_free_dom in Htotal_dom.
        unfold lvars_of_atoms in *.
        apply elem_of_map in Htotal_dom as [a [-> Ha]].
        apply elem_of_map. exists a. split; [reflexivity|set_solver].
      * rewrite elem_of_singleton in Hz. subst z.
        unfold lvars_of_atoms. apply elem_of_map.
        exists x. split; [reflexivity|set_solver].
    + intros τ Hτ.
    destruct Hτ as [σx [Hσx ->]].
    apply (proj1 (resA_extend_by_store_iff m F mx σx Hext)) in Hσx.
    destruct Hσx as [σm [we [σe [Hσm [HF [Hσe ->]]]]]].
    unfold expr_result_at_store.
    split.
    * intros Hxin.
      apply Hx_fresh.
      rewrite <- tm_lvars_fv.
      apply lvars_fv_elem. exact Hxin.
    * destruct (Htotal_eval (lstore_lift_free σm)) as [v Heval_m].
      { exists σm. split; [exact Hσm|reflexivity]. }
      assert (Hclosed_restrict :
        closed_env (store_restrict σm (fv_tm e))).
      { exact (proj1 (Hclosed σm Hσm)). }
      assert (Heval_restrict :
        tm_eval_in_store (store_restrict σm (fv_tm e)) e v).
      {
        apply (proj2 (tm_eval_in_store_restrict_fv_closed_on
          σm e v Hclosed_restrict)).
        exact Heval_m.
      }
      assert (Hproj_dom :
        dom (store_restrict σm (fv_tm e) : gmap atom value) = fv_tm e).
      {
        rewrite storeA_restrict_dom.
        pose proof (res_extend_by_input_dom m F mx Hext) as Hin_sub.
        unfold ext_in in Hin_sub.
        pose proof (wfworldA_store_dom m σm Hσm) as Hσm_dom.
        change (dom (σm : gmap atom value) = world_dom (m : WorldT)) in Hσm_dom.
        rewrite Hσm_dom, <- Hin. set_solver.
      }
      pose proof (expr_result_extension_apply_total_iff
        e x F (store_restrict σm (fv_tm e)) we
        {| expr_result_extension_witness_fresh := Hx_fresh;
           expr_result_extension_witness_shape := conj Hin Hout;
           expr_result_extension_witness_rel := Hrel |}
        Hproj_dom
        ltac:(unfold ext_rel; rewrite <- Hin; exact HF)
        (ex_intro _ v Heval_restrict) σe) as Hwe.
      apply Hwe in Hσe as [u [Heval_u ->]].
      exists u. split.
      -- change (((lstore_lift_free (σm ∪ ({[x := u]} : StoreT)) : LStoreT)
          : gmap logic_var value) !! LVFree x = Some u).
        rewrite lstore_lift_free_lookup_free.
        change (((σm : gmap atom value) ∪ ({[x := u]} : gmap atom value)) !! x =
          Some u).
        assert (Hσm_x_none : σm !! x = None).
        {
          apply eq_None_not_Some. intros [w Hlook].
          pose proof (res_extend_by_output_fresh m F mx Hext) as Hfresh_out.
          change (ext_out F ## world_dom (m : WorldT)) in Hfresh_out.
          unfold ext_out in Hfresh_out.
          pose proof (wfworldA_store_dom m σm Hσm) as Hσm_dom.
          change (dom (σm : gmap atom value) = world_dom (m : WorldT)) in Hσm_dom.
          change (((σm : gmap atom value) !! x) = Some w) in Hlook.
          apply elem_of_dom_2 in Hlook.
          rewrite Hσm_dom in Hlook.
          rewrite Hout in Hfresh_out.
          set_solver.
        }
        apply map_lookup_union_Some_raw. right.
        split; [exact Hσm_x_none|].
        change ((<[x := u]> (∅ : StoreT)) !! x = Some u).
        apply map_lookup_insert.
      -- assert (Hrestrict_union :
          store_restrict (σm ∪ ({[x := u]} : StoreT)) (fv_tm e) =
          store_restrict σm (fv_tm e)).
        {
          apply storeA_restrict_union_ignore_r.
          pose proof (dom_singleton_L (M:=gmap atom) x u) as Hdom_single.
          change (dom (({[x := u]} : StoreT) : gmap atom value) = {[x]})
            in Hdom_single.
          rewrite Hdom_single. set_solver.
        }
        assert (Hclosed_union :
          closed_env (store_restrict (σm ∪ ({[x := u]} : StoreT)) (fv_tm e))).
        { rewrite Hrestrict_union. exact Hclosed_restrict. }
        apply (proj1 (tm_eval_in_store_restrict_fv_closed_on
          (σm ∪ ({[x := u]} : StoreT)) e u Hclosed_union)).
        rewrite Hrestrict_union. exact Heval_u.
Qed.

Lemma expr_result_extension_world_models
    (Σ : lty_env) e x F (m mx : WfWorldT) :
  lvars_of_atoms (fv_tm e) ⊆ dom Σ ->
  res_models m (basic_world_formula Σ) ->
  expr_result_extension_witness e x F ->
  res_extend_by m F mx ->
  expr_total_on_atom_world e m ->
  expr_result_at_world e (LVFree x) (res_lift_free mx : LWorldT).
Proof.
  intros Hfv Hbasic HF Hext Htotal.
  eapply expr_result_extension_world_models_closed; eauto.
  eapply basic_world_formula_wfworld_closed_on_atoms; eauto.
Qed.

Lemma expr_result_formula_of_result_extends (Σ : lty_env) e x m F mx :
  lvars_of_atoms (fv_tm e) ⊆ dom Σ ->
  res_models m (basic_world_formula Σ) ->
  expr_result_extension_witness e x F ->
  res_extend_by m F mx ->
  expr_total_on_atom_world e m ->
  res_models mx (expr_result_formula e (LVFree x)).
Proof.
  intros Hfv Hbasic HF Hext Htotal.
  pose proof (expr_result_extension_world_models
    Σ e x F m mx Hfv Hbasic HF Hext Htotal) as Hres.
  apply expr_result_formula_models_iff.
  unfold expr_result_lqual, logic_qualifier_denote.
  destruct Hres as [Hx [Hdom Hstores]].
  assert (Hlc : lc_lvars (tm_lvars e ∪ {[LVFree x]})).
  {
    unfold lc_lvars. intros v Hv.
    destruct v as [k|y]; [|exact I].
    exfalso.
    specialize (Hdom (LVBound k) Hv).
    rewrite res_lift_free_dom in Hdom.
    unfold lvars_of_atoms in Hdom.
    apply elem_of_map in Hdom as [a [Hbad _]]. discriminate.
  }
  assert (Hsub :
      lvars_fv (tm_lvars e ∪ {[LVFree x]}) ⊆ world_dom (mx : WorldT)).
  {
    intros y Hy.
    assert (LVFree y ∈ tm_lvars e ∪ {[LVFree x]}) as HyD.
    { apply lvars_fv_elem. exact Hy. }
    specialize (Hdom (LVFree y) HyD).
    rewrite res_lift_free_dom in Hdom.
    unfold lvars_of_atoms in Hdom.
    apply elem_of_map in Hdom as [a [Heq Ha]].
    inversion Heq. subst a. exact Ha.
  }
  exists Hlc, Hsub.
  apply expr_result_at_world_lworld_on_lift.
  exact (conj Hx (conj Hdom Hstores)).
Qed.

End TermDenotation.
