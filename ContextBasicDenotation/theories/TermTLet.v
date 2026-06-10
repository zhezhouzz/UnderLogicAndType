(** * BasicDenotation.TermTLet

    Split out from [Term.v] to keep individual proof files small. *)

From ContextBasicDenotation Require Import Notation StoreTyping.
From ContextBasicDenotation Require Import TermSyntax TermEval TermOpen TermExtension.
From ContextLogic Require Import FormulaConnectives.
From CoreLang Require Import StrongNormalization.

Section TermDenotation.

Lemma expr_result_residual_singleton e y (σ : StoreT) :
  lc_lvars (tm_lvars e) ->
  LVFree y ∉ tm_lvars e ->
  dom (σ : StoreT) = lvars_fv (tm_lvars e) ->
  (tm_lvars e ∪ {[LVFree y]}) ∖
    dom (atom_store_to_lvar_store σ : LStoreT) =
  ({[LVFree y]} : lvset).
Proof.
  intros Hlc Hy Hdom.
  apply set_eq. intros v.
  rewrite elem_of_difference, elem_of_union, elem_of_singleton.
  rewrite atom_store_to_lvar_store_dom.
  split.
  - intros [[HvD|Hv] Hvnot].
    + exfalso. apply Hvnot.
      unfold lvars_of_atoms.
      pose proof (lvars_bv_empty_subset_of_atoms_fv (tm_lvars e)
        (proj1 (lc_lvars_no_bv _) Hlc) v HvD) as Hvfv.
      unfold lvars_of_atoms in Hvfv.
      apply elem_of_map in Hvfv as [a [-> Ha]].
      apply elem_of_map. exists a. split; [reflexivity|].
      change (a ∈ dom (σ : StoreT)).
      rewrite Hdom. exact Ha.
    + subst v. reflexivity.
  - intros ->. split.
    + right. reflexivity.
    + intros Hbad. apply Hy.
      unfold lvars_of_atoms in Hbad.
      apply elem_of_map in Hbad as [a [Heq Ha]].
      inversion Heq. subst a.
      apply lvars_fv_elem.
      rewrite <- Hdom. exact Ha.
Qed.

Lemma expr_result_msubst_back_lift_store_eq e y
    (σproj σ : StoreT)
    (HlcQ : lc_lvars (tm_lvars e ∪ {[LVFree y]}))
    (HsubQ : lvars_fv (tm_lvars e ∪ {[LVFree y]}) ⊆ dom (σ : StoreT))
    (HlcR :
      lc_lvars ((tm_lvars e ∪ {[LVFree y]}) ∖
        dom (atom_store_to_lvar_store σproj : LStoreT)))
    (HsubR :
      lvars_fv ((tm_lvars e ∪ {[LVFree y]}) ∖
        dom (atom_store_to_lvar_store σproj : LStoreT)) ⊆ dom (σ : StoreT)) :
  dom (σproj : StoreT) = lvars_fv (tm_lvars e) ->
  store_restrict σ (lvars_fv (tm_lvars e)) = σproj ->
  lstore_on_mlsubst_back (tm_lvars e ∪ {[LVFree y]})
    (atom_store_to_lvar_store σproj)
    (lstore_on_lift_store
      ((tm_lvars e ∪ {[LVFree y]}) ∖
        dom (atom_store_to_lvar_store σproj : LStoreT))
      σ HlcR HsubR) =
  lstore_on_lift_store (tm_lvars e ∪ {[LVFree y]}) σ HlcQ HsubQ.
Proof.
  intros Hproj_dom Hproj_eq.
  apply lstore_on_mlsubst_back_lift_store.
  apply storeA_map_eq. intros v.
  destruct (decide (v ∈ tm_lvars e ∪ {[LVFree y]})) as [HvQ|HvQ].
  2:{
    transitivity (@None value).
    - apply storeA_restrict_lookup_none_r. exact HvQ.
    - symmetry. apply storeA_restrict_lookup_none_r.
      intros Hvbad. apply elem_of_intersection in Hvbad as [Hvbad _].
      exact (HvQ Hvbad).
  }
  destruct (decide (v ∈ dom (atom_store_to_lvar_store σproj : LStoreT)))
    as [Hvρ|Hvρ].
  2:{
    transitivity (@None value).
    - apply storeA_restrict_lookup_none_l.
      apply not_elem_of_dom. exact Hvρ.
    - symmetry. apply storeA_restrict_lookup_none_r.
      intros Hvbad. apply elem_of_intersection in Hvbad as [_ Hvbad].
      exact (Hvρ Hvbad).
  }
  rewrite !storeA_restrict_lookup.
  destruct (decide (v ∈ tm_lvars e ∪ {[LVFree y]})) as [_|Hbad];
    [|contradiction].
  destruct (decide (v ∈ (tm_lvars e ∪ {[LVFree y]}) ∩
      dom (atom_store_to_lvar_store σproj : LStoreT))) as [_|Hbad].
  2:{ exfalso. apply Hbad. apply elem_of_intersection. split; assumption. }
  rewrite atom_store_to_lvar_store_dom in Hvρ.
  unfold lvars_of_atoms in Hvρ.
  apply elem_of_map in Hvρ as [a [-> Ha]].
  rewrite atom_store_to_lvar_store_lookup_free.
  rewrite lstore_lift_free_lookup_free.
  pose proof (f_equal (fun m => (m : gmap atom value) !! a) Hproj_eq)
    as Hlook.
  cbn in Hlook.
  case_decide as Hin_case.
  2:{
    exfalso. apply Hin_case. apply elem_of_intersection. split.
    - exact HvQ.
    - rewrite atom_store_to_lvar_store_dom.
      unfold lvars_of_atoms. apply elem_of_map.
      exists a. split; [reflexivity|exact Ha].
  }
  symmetry.
  change (((σ : gmap atom value) !! a) =
    ((σproj : gmap atom value) !! a)).
  rewrite <- Hlook.
  assert (HaD : a ∈ lvars_fv (tm_lvars e)).
  { rewrite <- Hproj_dom. exact Ha. }
  destruct ((σ : gmap atom value) !! a) as [va|] eqn:Hσa.
  - symmetry. apply storeA_restrict_lookup_some_2; [exact Hσa|exact HaD].
  - symmetry. apply storeA_restrict_lookup_none_l. exact Hσa.
Qed.

Lemma expr_result_msubst_back_input_restrict e y
    (σproj σ : StoreT)
    (s : LStoreOn (V := value)
      ((tm_lvars e ∪ {[LVFree y]}) ∖
        dom (atom_store_to_lvar_store σproj : LStoreT))) :
  lc_lvars (tm_lvars e) ->
  lvars_fv (tm_lvars e) ⊆ dom (σ : StoreT) ->
  store_restrict σ (lvars_fv (tm_lvars e)) = σproj ->
  storeA_restrict
    (lso_store (lstore_on_mlsubst_back
      (tm_lvars e ∪ {[LVFree y]})
      (atom_store_to_lvar_store σproj) s))
    (tm_lvars e) =
  storeA_restrict (lstore_lift_free σ : LStoreT) (tm_lvars e).
Proof.
  intros Hlc Hsubσ Hproj.
  apply storeA_map_eq. intros z.
  destruct (decide (z ∈ tm_lvars e)) as [Hz|Hz].
  2:{
    transitivity (@None value).
    - apply storeA_restrict_lookup_none_r. exact Hz.
    - symmetry. apply storeA_restrict_lookup_none_r. exact Hz.
  }
  rewrite !storeA_restrict_lookup.
  destruct (decide (z ∈ tm_lvars e)) as [_|Hbad]; [|contradiction].
  destruct z as [k|a].
  - exfalso. exact (Hlc (LVBound k) Hz).
  - unfold lstore_on_mlsubst_back. cbn [lso_store storeAO_store].
    assert (Ha_fv : a ∈ lvars_fv (tm_lvars e)).
    { apply lvars_fv_elem. exact Hz. }
    rewrite lookup_union_r.
    2:{
      apply not_elem_of_dom.
      change (LVFree a ∉ dom (lso_store s : LStoreT)).
      rewrite (lso_dom s).
      intros Hrem.
      apply elem_of_difference in Hrem as [_ Hnot].
      apply Hnot.
      rewrite atom_store_to_lvar_store_dom.
      unfold lvars_of_atoms.
      apply elem_of_map. exists a. split; [reflexivity|].
      change (a ∈ dom (σproj : StoreT)).
      rewrite <- Hproj.
      change (a ∈ dom (store_restrict σ (lvars_fv (tm_lvars e)) :
        gmap atom value)).
      rewrite storeA_restrict_dom.
      apply elem_of_intersection. split; [apply Hsubσ|]; exact Ha_fv.
    }
    rewrite atom_store_to_lvar_store_lookup_free.
    rewrite storeA_restrict_lookup.
    destruct (decide (LVFree a ∈ tm_lvars e)) as [_|Hnot_in];
      [|contradiction].
    rewrite lstore_lift_free_lookup_free.
    destruct (decide (LVFree a ∈ tm_lvars e ∪ {[LVFree y]})) as [_|HbadQ].
    2:{ exfalso. apply HbadQ. apply elem_of_union_l. exact Hz. }
    pose proof (Hsubσ a Ha_fv) as Ha_dom.
    change (a ∈ dom (σ : gmap atom value)) in Ha_dom.
    apply elem_of_dom in Ha_dom as [va Hσa].
    replace ((σ : StoreT) !! a) with (Some va) by (symmetry; exact Hσa).
    rewrite <- Hproj.
    change (((storeA_restrict σ (lvars_fv (tm_lvars e)) : gmap atom value)
      !! a) = Some va).
    apply storeA_restrict_lookup_some_2; [exact Hσa|exact Ha_fv].
Qed.

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
  formula_scoped_in_world m (expr_total_formula e) /\
  lc_lvars (tm_lvars e) /\
  forall σ, (m : WorldT) σ ->
    must_terminating (lstore_instantiate_tm (lstore_lift_free σ) e).
Proof.
  unfold expr_total_formula.
  rewrite res_models_FFiberAtom_store_iff.
  split.
  - intros [Hscope Hstores]. split; [exact Hscope|].
    split.
    {
      unfold qualifier_holds_store, expr_total_qual in Hstores.
      cbn [qual_lvars qual_prop] in Hstores.
      destruct (wfA_ne _ (worldA_wf m)) as [σ Hσ].
      destruct (Hstores σ Hσ) as [Hlc _].
      exact Hlc.
    }
    intros σ Hσ.
    specialize (Hstores σ Hσ).
    unfold qualifier_holds_store, expr_total_qual in Hstores.
    cbn [qual_lvars qual_prop] in Hstores.
    destruct Hstores as [Hlc [Hsub Hsn]].
    apply (proj1 (expr_strong_total_restrict_lvars e
      (lstore_lift_free σ : LStoreT) (tm_lvars e) ltac:(set_solver))).
    exact Hsn.
  - intros [Hscope [Hlc Hstores]]. split; [exact Hscope|].
    intros σ Hσ.
    unfold qualifier_holds_store, expr_total_qual.
    cbn [qual_lvars qual_prop].
    assert (Hsub : lvars_fv (tm_lvars e) ⊆ dom (σ : StoreT)).
    {
      intros a Ha.
      change (a ∈ dom (σ : StoreT)).
      replace (dom (σ : StoreT)) with (world_dom (m : WorldT))
        by (symmetry; apply (wfworld_store_dom m σ Hσ)).
      unfold formula_scoped_in_world in Hscope.
      rewrite formula_fv_fiber_atom in Hscope.
      exact (Hscope a Ha).
    }
    exists Hlc, Hsub.
    pose proof (Hstores σ Hσ) as Hsn.
    apply (proj2 (expr_strong_total_restrict_lvars e
      (lstore_lift_free σ : LStoreT) (tm_lvars e) ltac:(set_solver))).
    exact Hsn.
Qed.

Lemma expr_total_formula_to_atom_world e (m : WfWorldT) :
  res_models m (expr_total_formula e) ->
  expr_total_on_atom_world e m.
Proof.
  intros Hmodels.
  apply expr_total_formula_models_iff in Hmodels.
  destruct Hmodels as [Hscope [Hlc Hstores]].
  unfold expr_total_on_atom_world, expr_total_on in *.
  split.
  - rewrite res_lift_free_dom.
    intros v Hv.
    destruct v as [k|a].
    + exfalso. exact (Hlc _ Hv).
    + unfold lvars_of_atoms. apply elem_of_map.
      exists a. split; [reflexivity|].
      unfold formula_scoped_in_world in Hscope.
      rewrite formula_fv_expr_total_formula in Hscope.
      apply Hscope. apply lvars_fv_elem. exact Hv.
  - intros τ Hτ.
    destruct Hτ as [σ [Hσ ->]].
    exact (Hstores σ Hσ).
Qed.

Lemma expr_total_atom_world_to_formula e (m : WfWorldT) :
  expr_total_on_atom_world e m ->
  res_models m (expr_total_formula e).
Proof.
  intros Htotal.
  apply expr_total_formula_models_iff.
  destruct Htotal as [Hdom Hstores].
  split.
  - unfold formula_scoped_in_world.
    rewrite formula_fv_expr_total_formula.
    intros a Ha.
    assert (LVFree a ∈ tm_lvars e) as HaD.
    { apply lvars_fv_elem. exact Ha. }
    specialize (Hdom _ HaD).
    rewrite res_lift_free_dom in Hdom.
    unfold lvars_of_atoms in Hdom.
    apply elem_of_map in Hdom as [b [Heq Hb]].
    inversion Heq. subst b. exact Hb.
  - split.
    + unfold lc_lvars. intros v Hv.
      specialize (Hdom _ Hv).
      rewrite res_lift_free_dom in Hdom.
      unfold lvars_of_atoms in Hdom.
      apply elem_of_map in Hdom as [a [Hbad _]].
      destruct v as [k|b]; [discriminate|exact I].
    + intros σ Hσ.
      apply Hstores.
      exists σ. split; [exact Hσ|reflexivity].
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
  pose proof (proj1 (lc_lete_iff_body e1 e2) Hlc_let)
    as [Hlc_e1 Hbody_e2].
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
    destruct HFx as [Hx_fv [Hin Hout] Hrel].
    set (σT := store_restrict σ (fv_tm (tlete e1 e2))).
    assert (HσT_agree :
      store_restrict σ (fv_tm (tlete e1 e2)) =
      store_restrict σT (fv_tm (tlete e1 e2))).
    {
      subst σT. symmetry. apply storeA_restrict_twice_same.
    }
    apply (proj2 (tm_must_terminating_agree_on_fv
      σ σT (tlete e1 e2) Hlc_let HσT_agree)).
    assert (HclosedT : store_closed σT).
    {
      assert (Hsub_atoms :
        lvars_of_atoms (fv_tm (tlete e1 e2)) ⊆ dom Σ).
      {
        unfold lvars_of_atoms. intros lv Hlv.
        apply elem_of_map in Hlv as [a [-> Ha]].
        apply lvars_fv_elem. apply Hfv_let. exact Ha.
      }
      subst σT.
      exact ((basic_world_formula_wfworld_closed_on_atoms
        Σ (fv_tm (tlete e1 e2)) m Hsub_atoms Hbasic) σ Hσ).
    }
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
    assert (Hx_domT : x ∉ dom (σT : gmap atom value)).
    {
      subst σT. rewrite storeA_restrict_dom. set_solver.
    }
    assert (HbodyT :
      body_tm (lstore_instantiate_tm_at 1 (lstore_lift_free σT : LStoreT) e2)).
    {
      apply lc_lete_iff_body in Hlc_let as [_ Hbody].
      rewrite lstore_instantiate_tm_at_lc_lstore.
      - rewrite lstore_free_part_lift_free.
        eapply body_tm_msubst.
        + exact (proj1 HclosedT).
        + exact (proj2 HclosedT).
        + exact Hbody.
      - apply lc_lstore_lift_free.
      - rewrite lstore_free_part_lift_free. exact (proj1 HclosedT).
    }
    change (must_terminating
      (tlete
        (lstore_instantiate_tm (lstore_lift_free σT : LStoreT) e1)
        (lstore_instantiate_tm_at 1 (lstore_lift_free σT : LStoreT) e2))).
    eapply must_terminating_tlete_intro.
    + exact HbodyT.
    + pose proof (Htotal1_stores (lstore_lift_free σ)
        ltac:(exists σ; split; [exact Hσ|reflexivity])) as Hsn1.
      assert (Hagree_e1 :
        store_restrict σ (fv_tm e1) =
        store_restrict σT (fv_tm e1)).
      {
        subst σT. symmetry.
        apply storeA_restrict_twice_subset.
        cbn [fv_tm]. set_solver.
      }
      apply (proj1 (tm_must_terminating_agree_on_fv
        σ σT e1 Hlc_e1 Hagree_e1)).
      exact Hsn1.
    + intros vx He1.
      pose proof (steps_regular2 _ _ He1) as Hret.
      apply lc_ret_iff_value in Hret as Hvx_lc.
      change (tm_eval_in_store σT e1 vx) in He1.
      set (σX := store_restrict σT (fv_tm e1)).
    assert (HσX_dom : dom (σX : gmap atom value) = fv_tm e1).
    {
      subst σX. rewrite storeA_restrict_dom.
      pose proof (res_extend_by_input_dom m Fx mx Hext) as Hin_sub.
      unfold ext_in in Hin_sub. rewrite <- Hin.
      subst σT.
      rewrite storeA_restrict_dom.
      pose proof (wfworldA_store_dom m σ Hσ) as Hσdom.
      change (dom (σ : gmap atom value) = world_dom (m : WorldT)) in Hσdom.
      rewrite Hσdom. set_solver.
    }
    assert (HFrel : ext_rel Fx σX (expr_result_output_world e1 x σX)).
    { subst σX. apply Hrel. exact HσX_dom. }
    assert (He1X : tm_eval_in_store σX e1 vx).
    {
      subst σX.
      apply (proj2 (tm_eval_in_store_restrict_fv_exact σT e1 vx)).
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
        + subst σX σT. unfold ext_in in Hin. rewrite Hin.
          rewrite storeA_restrict_twice_subset; [reflexivity|cbn; set_solver].
      - split; [exact Hσe|reflexivity].
    }
    pose proof (Htotal2_stores
      (lstore_lift_free (σ ∪ ({[x := vx]} : StoreT)))
      ltac:(exists (σ ∪ ({[x := vx]} : StoreT));
        split; [exact Hmx_store|reflexivity])) as Hsn2_union.
    assert (Hsn2_insert :
      must_terminating
        (lstore_instantiate_tm
          (lstore_lift_free (<[x := vx]> σT) : LStoreT)
          (e2 ^^ x))).
    {
      assert (Hagree :
        store_restrict (σ ∪ ({[x := vx]} : StoreT)) (fv_tm (e2 ^^ x)) =
        store_restrict (<[x := vx]> σT) (fv_tm (e2 ^^ x))).
      {
        subst σT.
        apply store_insert_restrict_agree_on_open_fv.
        - cbn [fv_tm] in Hfv_let. set_solver.
        - exact Hx_let.
        - exact Hx_dom.
      }
      assert (Hlc_e2x : lc_tm (e2 ^^ x)).
      { apply body_open_tm; [exact Hbody_e2|constructor]. }
      apply (proj1 (tm_must_terminating_agree_on_fv
        (σ ∪ ({[x := vx]} : StoreT))
        (<[x := vx]> σT)
        (e2 ^^ x) Hlc_e2x Hagree)).
      exact Hsn2_union.
    }
    rewrite lstore_lift_free_insert in Hsn2_insert.
    change (e2 ^^ x) with (open_tm 0 (vfvar x) e2) in Hsn2_insert.
    rewrite lstore_instantiate_tm_insert_open in Hsn2_insert.
    * exact Hsn2_insert.
    * exact HclosedT.
    * exact Hvx_lc.
    * intros Hbad. apply elem_of_union in Hbad as [Hbad|Hbad].
      -- exact (Hx_domT Hbad).
      -- exact (Hx_e2 Hbad).
Qed.

Lemma expr_result_formula_models_elim e x (m : WfWorldT) :
  res_models m (expr_result_formula e x) ->
  formula_scoped_in_world m (expr_result_formula e x) /\
  lc_lvars (tm_lvars e ∪ {[x]}) /\
  forall σ, (m : WorldT) σ ->
    expr_result_at_store e x (lstore_lift_free σ).
Proof.
  intros Hmodels.
  unfold expr_result_formula.
  apply res_models_FFibVars_iff in Hmodels.
  destruct Hmodels as [Hscope [HlcD Hfib]].
  assert (HDm : lvars_fv (tm_lvars e) ⊆ world_dom (m : WorldT)).
  {
    apply (proj1 (formula_scoped_fibvars_iff m (tm_lvars e)
      (FAtom (expr_result_qual e x)))) in Hscope as [HDm _].
    exact HDm.
  }
  assert (Hstores : forall σ, (m : WorldT) σ ->
    expr_result_at_store e x (lstore_lift_free σ)).
  {
    intros σ Hσ.
    destruct (res_fiber_from_projection_of_store m
      (lvars_fv (tm_lvars e)) σ HDm Hσ)
      as [mfib [Hproj Hσfib]].
    pose proof (Hfib (store_restrict σ (lvars_fv (tm_lvars e)))
      mfib Hproj) as Hatom.
    pose proof (res_models_FAtom_store_holds _ _ Hatom σ Hσfib)
      as Hhold.
    unfold qualifier_holds_store, expr_result_qual,
      qual_msubst_store, qual_mlsubst in Hhold.
    cbn [qual_lvars qual_prop] in Hhold.
    destruct Hhold as [HlcR [HsubR Hres]].
    assert (Hproj_dom :
      dom (store_restrict σ (lvars_fv (tm_lvars e)) : StoreT) =
      lvars_fv (tm_lvars e)).
    {
      change (dom (store_restrict σ (lvars_fv (tm_lvars e)) :
        gmap atom value) = lvars_fv (tm_lvars e)).
      rewrite storeA_restrict_dom.
      rewrite (wfworld_store_dom m σ Hσ).
      set_solver.
    }
    assert (HlcQ : lc_lvars (tm_lvars e ∪ {[x]})).
    {
      intros v Hv.
      apply elem_of_union in Hv as [Hv|Hv].
      - exact (HlcD v Hv).
      - apply elem_of_singleton in Hv as ->.
        destruct x as [k|a]; [|exact I].
        apply (HlcR (LVBound k)).
        apply elem_of_difference. split.
        + apply elem_of_union_r. apply elem_of_singleton. reflexivity.
        + rewrite atom_store_to_lvar_store_dom.
          unfold lvars_of_atoms. intros Hbad.
          apply elem_of_map in Hbad as [b [Hbad _]]. discriminate.
    }
    assert (HsubQ :
      lvars_fv (tm_lvars e ∪ {[x]}) ⊆ dom (σ : StoreT)).
    {
      intros a Ha.
      change (a ∈ dom (σ : gmap atom value)).
      rewrite (wfworld_store_dom m σ Hσ).
      unfold formula_scoped_in_world in Hscope.
      apply Hscope.
      rewrite formula_fv_fibvars, formula_fv_atom.
      unfold expr_result_qual, qual_dom, qual_vars.
      set_solver.
    }
    destruct x as [k|y].
    - exfalso.
      specialize (HlcQ (LVBound k)).
      apply HlcQ. apply elem_of_union_r. apply elem_of_singleton. reflexivity.
    - pose proof (expr_result_msubst_back_lift_store_eq e y
        (store_restrict σ (lvars_fv (tm_lvars e))) σ
        HlcQ HsubQ HlcR HsubR Hproj_dom eq_refl) as Heq.
      pose proof (f_equal lso_store Heq) as Heq_store.
      cbn [lstore_on_lift_store storeAO_store] in Heq_store.
      change (expr_result_at_store e (LVFree y)
        (lso_store (lstore_on_mlsubst_back
          (tm_lvars e ∪ {[LVFree y]})
          (atom_store_to_lvar_store
            (store_restrict σ (lvars_fv (tm_lvars e))))
          (lstore_on_lift_store
            ((tm_lvars e ∪ {[LVFree y]}) ∖
              dom (atom_store_to_lvar_store
                (store_restrict σ (lvars_fv (tm_lvars e)) : StoreT)
                : LStoreT))
            σ HlcR HsubR)))) in Hres.
      rewrite Heq_store in Hres.
      destruct Hres as [Hyfresh [v [Hlookup Heval]]].
      split; [exact Hyfresh|].
      exists v. split.
      * apply storeA_restrict_lookup_some in Hlookup as [_ Hlookup].
        exact Hlookup.
      * apply (proj1 (expr_eval_in_store_restrict_lvars e
          (lstore_lift_free σ : LStoreT) (tm_lvars e ∪ {[LVFree y]})
          v ltac:(set_solver))).
        exact Heval.
  }
  split; [exact Hscope|].
  split.
  - destruct (wfA_ne _ (worldA_wf m)) as [σ0 Hσ0].
    destruct (Hstores σ0 Hσ0) as [_ [v [Hlookup _]]].
    intros v0 Hv0.
    apply elem_of_union in Hv0 as [Hv0|Hv0].
    + exact (HlcD v0 Hv0).
    + apply elem_of_singleton in Hv0 as ->.
      destruct x as [k|a]; [|exact I].
      rewrite lstore_lift_free_lookup_bound in Hlookup. discriminate.
  - exact Hstores.
Qed.

Lemma expr_result_formula_to_atom_world e x (m : WfWorldT) :
  res_models m (expr_result_formula e x) ->
  expr_result_at_world e x (res_lift_free m : LWorldT).
Proof.
  intros Hmodels.
  apply expr_result_formula_models_elim in Hmodels.
  destruct Hmodels as [Hscope [Hlc Hstores]].
  destruct (wfA_ne _ (worldA_wf m)) as [σ0 Hσ0].
  destruct (Hstores σ0 Hσ0) as [Hx _].
  split; [exact Hx|]. split.
  - rewrite res_lift_free_dom.
    intros v Hv.
    destruct v as [k|a].
    + exfalso. exact (Hlc _ Hv).
    + unfold lvars_of_atoms. apply elem_of_map.
      exists a. split; [reflexivity|].
      unfold formula_scoped_in_world in Hscope.
      rewrite formula_fv_expr_result_formula in Hscope.
      apply Hscope. apply lvars_fv_elem. exact Hv.
  - intros τ Hτ.
    destruct Hτ as [σ [Hσ ->]].
    exact (Hstores σ Hσ).
Qed.

Lemma expr_result_atom_world_to_formula e x (m : WfWorldT) :
  expr_result_at_world e x (res_lift_free m : LWorldT) ->
  res_models m (expr_result_formula e x).
Proof.
  intros Hres.
  destruct Hres as [Hx [Hdom Hstores]].
  assert (Hscope : formula_scoped_in_world m (expr_result_formula e x)).
  {
    unfold formula_scoped_in_world.
    rewrite formula_fv_expr_result_formula.
    intros y Hy.
    assert (LVFree y ∈ tm_lvars e ∪ {[x]}) as HyD.
    { apply lvars_fv_elem. exact Hy. }
    specialize (Hdom _ HyD).
    rewrite res_lift_free_dom in Hdom.
    unfold lvars_of_atoms in Hdom.
    apply elem_of_map in Hdom as [a [Heq Ha]].
    inversion Heq. subst a. exact Ha.
  }
  assert (HlcQ : lc_lvars (tm_lvars e ∪ {[x]})).
  {
    unfold lc_lvars. intros v Hv.
    specialize (Hdom _ Hv).
    rewrite res_lift_free_dom in Hdom.
    unfold lvars_of_atoms in Hdom.
    apply elem_of_map in Hdom as [a [Hbad _]].
    destruct v as [k|b]; [discriminate|exact I].
  }
  unfold expr_result_formula.
  apply res_models_FFibVars_intro.
  - exact Hscope.
  - intros v Hv. apply HlcQ. apply elem_of_union_l. exact Hv.
  - intros σproj mfib Hproj.
    destruct Hproj as [Hproj_src Hfib_eq].
    destruct x as [k|y].
    + exfalso.
      apply (HlcQ (LVBound k)).
      apply elem_of_union_r. apply elem_of_singleton. reflexivity.
    + unfold formula_msubst_store. cbn [formula_mlsubst].
      unfold res_models. cbn [formula_measure res_models_fuel].
      split.
      * unfold formula_scoped_in_world. rewrite formula_fv_atom.
        unfold expr_result_qual, qual_dom, qual_vars, qual_msubst_store,
          qual_mlsubst.
        cbn [qual_lvars].
        intros a Ha.
        assert (Hdom_fib :
          world_dom (mfib : WorldT) = world_dom (m : WorldT)).
        {
          change ((mfib : WorldT) = rawA_fiber (m : WorldT) σproj)
            in Hfib_eq.
          pose proof (f_equal world_dom Hfib_eq) as Hdom_eq.
          cbn [raw_world raw_worldA world_dom rawA_fiber] in Hdom_eq.
          exact Hdom_eq.
        }
        change (a ∈ world_dom (mfib : WorldT)).
        replace (world_dom (mfib : WorldT)) with (world_dom (m : WorldT))
          by (symmetry; exact Hdom_fib).
        unfold formula_scoped_in_world in Hscope.
        rewrite formula_fv_expr_result_formula in Hscope.
        apply Hscope.
        eapply lvars_fv_mono; [|exact Ha].
        intros v Hv. apply elem_of_difference in Hv as [Hv _]. exact Hv.
      * unfold qualifier_exact_denote, expr_result_qual,
          qual_msubst_store, qual_mlsubst.
        cbn [qual_lvars qual_prop].
        assert (Hdom_fib :
          world_dom (mfib : WorldT) = world_dom (m : WorldT)).
        {
          change ((mfib : WorldT) = rawA_fiber (m : WorldT) σproj)
            in Hfib_eq.
          pose proof (f_equal world_dom Hfib_eq) as Hdom_eq.
          cbn [raw_world raw_worldA world_dom rawA_fiber] in Hdom_eq.
          exact Hdom_eq.
        }
        assert (HlcD : lc_lvars (tm_lvars e)).
        {
          intros v Hv. apply HlcQ. apply elem_of_union_l. exact Hv.
        }
        assert (Hproj_dom :
          dom (σproj : StoreT) = lvars_fv (tm_lvars e)).
        {
          pose proof (wfworld_store_dom
            (res_restrict m (lvars_fv (tm_lvars e))) σproj Hproj_src)
            as Hσproj_dom.
          change (dom (σproj : StoreT) =
            world_dom (res_restrict m (lvars_fv (tm_lvars e)) : WorldT))
            in Hσproj_dom.
          rewrite res_restrict_dom in Hσproj_dom.
          rewrite Hσproj_dom.
          apply set_eq. intros a. rewrite elem_of_intersection.
          split.
          - intros [_ Ha]. exact Ha.
          - intros Ha. split; [|exact Ha].
            unfold formula_scoped_in_world in Hscope.
            rewrite formula_fv_expr_result_formula in Hscope.
            apply Hscope.
            rewrite lvars_fv_union.
            apply elem_of_union_l. exact Ha.
        }
        pose proof (expr_result_residual_singleton e y σproj HlcD Hx
          Hproj_dom) as HR_single.
        assert (HlcR :
          lc_lvars ((tm_lvars e ∪ {[LVFree y]}) ∖
            dom (atom_store_to_lvar_store σproj : LStoreT))).
        {
          intros v Hv. apply elem_of_difference in Hv as [Hv _].
          apply HlcQ. exact Hv.
        }
        assert (HsubR :
          lvars_fv ((tm_lvars e ∪ {[LVFree y]}) ∖
            dom (atom_store_to_lvar_store σproj : LStoreT)) ⊆
          world_dom (mfib : WorldT)).
        {
          rewrite HR_single, lvars_fv_singleton_free.
          intros a Ha.
          apply elem_of_singleton in Ha as ->.
          assert (Hy_scope : y ∈ world_dom (m : WorldT)).
          {
            unfold formula_scoped_in_world in Hscope.
            rewrite formula_fv_expr_result_formula in Hscope.
            apply Hscope.
            rewrite lvars_fv_union, lvars_fv_singleton_free.
            apply elem_of_union_r. apply elem_of_singleton. reflexivity.
          }
          rewrite Hdom_fib. exact Hy_scope.
        }
        exists HlcR, HsubR. intros s.
        assert (Hs_y_some :
          exists vy, (lso_store s : LStoreT) !! LVFree y = Some vy).
        {
          assert (Hy_dom : LVFree y ∈ dom (lso_store s : LStoreT)).
          {
            rewrite (lso_dom s).
            change (LVFree y ∈
              (tm_lvars e ∪ {[LVFree y]}) ∖
                dom (atom_store_to_lvar_store σproj : LStoreT)).
            rewrite HR_single.
            apply elem_of_singleton. reflexivity.
          }
          change (LVFree y ∈ dom (lso_store s : gmap logic_var value)) in Hy_dom.
          apply elem_of_dom in Hy_dom as [vy Hvy].
          exists vy. exact Hvy.
        }
        assert (Hml_y_lookup :
          forall vy,
            (lso_store s : LStoreT) !! LVFree y = Some vy ->
            (lso_store (lstore_on_mlsubst_back
              (tm_lvars e ∪ {[LVFree y]})
              (atom_store_to_lvar_store σproj) s) : LStoreT)
              !! LVFree y = Some vy).
        {
          intros vy Hsy.
          assert (Hρ_y_none :
            (storeA_restrict (atom_store_to_lvar_store σproj)
              (tm_lvars e ∪ {[LVFree y]}) : gmap logic_var value)
              !! LVFree y = None).
          {
            apply storeA_restrict_lookup_none_l.
            rewrite atom_store_to_lvar_store_lookup_free.
            apply not_elem_of_dom.
            change (y ∉ dom (σproj : StoreT)).
            rewrite Hproj_dom.
            intros Hyfv. apply Hx. apply lvars_fv_elem. exact Hyfv.
          }
          unfold lstore_on_mlsubst_back. cbn [lso_store storeAO_store].
          change (((lso_store s : gmap logic_var value) ∪
            (storeA_restrict (atom_store_to_lvar_store σproj)
              (tm_lvars e ∪ {[LVFree y]}) : gmap logic_var value))
            !! LVFree y = Some vy).
          rewrite lookup_union_l; [exact Hsy|].
          exact Hρ_y_none.
        }
        assert (Hml_y_lookup_inv :
          forall vy,
            (lso_store (lstore_on_mlsubst_back
              (tm_lvars e ∪ {[LVFree y]})
              (atom_store_to_lvar_store σproj) s) : LStoreT)
              !! LVFree y = Some vy ->
            (lso_store s : LStoreT) !! LVFree y = Some vy).
        {
          intros vy Hml.
          destruct Hs_y_some as [wy Hsy].
          assert (Hρ_y_none :
            (storeA_restrict (atom_store_to_lvar_store σproj)
              (tm_lvars e ∪ {[LVFree y]}) : gmap logic_var value)
              !! LVFree y = None).
          {
            apply storeA_restrict_lookup_none_l.
            rewrite atom_store_to_lvar_store_lookup_free.
            apply not_elem_of_dom.
            change (y ∉ dom (σproj : StoreT)).
            rewrite Hproj_dom.
            intros Hyfv. apply Hx. apply lvars_fv_elem. exact Hyfv.
          }
          unfold lstore_on_mlsubst_back in Hml.
          cbn [lso_store storeAO_store] in Hml.
          change (((lso_store s : gmap logic_var value) ∪
            (storeA_restrict (atom_store_to_lvar_store σproj)
              (tm_lvars e ∪ {[LVFree y]}) : gmap logic_var value))
            !! LVFree y = Some vy) in Hml.
          rewrite lookup_union_l in Hml.
          - exact Hml.
          - exact Hρ_y_none.
        }
        split.
        -- intros Hres_s.
           destruct Hproj_src as [σ0 [Hσ0 Hσ0proj]].
           assert (Hσ0fib : (mfib : WorldT) σ0).
           {
             change ((mfib : WorldT) = rawA_fiber (m : WorldT) σproj)
               in Hfib_eq.
             rewrite Hfib_eq. split; [exact Hσ0|].
             change (store_restrict σ0 (dom (σproj : StoreT)) = σproj).
             rewrite Hproj_dom. exact Hσ0proj.
           }
           pose proof (Hstores (lstore_lift_free σ0)) as Hσ0res.
           assert (Hσ0lift : (res_lift_free m : LWorldT)
             (lstore_lift_free σ0)).
           { exists σ0. split; [exact Hσ0|reflexivity]. }
           specialize (Hσ0res Hσ0lift).
           destruct Hσ0res as [_ [u [Hσ0y Heval_σ0]]].
           destruct Hres_s as [_ [v [Hml_y Heval_ml]]].
           assert (Hsubσ0 : lvars_fv (tm_lvars e) ⊆ dom (σ0 : StoreT)).
           {
             intros a Ha.
             change (a ∈ dom (σ0 : gmap atom value)).
             rewrite (wfworld_store_dom m σ0 Hσ0).
             unfold formula_scoped_in_world in Hscope.
             rewrite formula_fv_expr_result_formula in Hscope.
             apply Hscope.
             rewrite lvars_fv_union.
             apply elem_of_union_l. exact Ha.
           }
           pose proof (expr_result_msubst_back_input_restrict e y
             σproj σ0 s HlcD Hsubσ0 Hσ0proj) as Hinput_eq.
           assert (Heval_ml_σ0 :
             expr_eval_in_store (lstore_lift_free σ0) e v).
           {
             apply (proj1 (expr_eval_in_store_restrict_lvars e
               (lstore_lift_free σ0 : LStoreT) (tm_lvars e) v
               ltac:(intros z Hz; exact Hz))).
             rewrite <- Hinput_eq.
             apply (proj2 (expr_eval_in_store_restrict_lvars e
               (lso_store (lstore_on_mlsubst_back
                 (tm_lvars e ∪ {[LVFree y]})
                 (atom_store_to_lvar_store σproj) s))
               (tm_lvars e) v ltac:(intros z Hz; exact Hz))).
             exact Heval_ml.
           }
           assert (v = u) as ->.
           {
             unfold expr_eval_in_store in Heval_ml_σ0, Heval_σ0.
             eapply steps_result_unique; eauto.
           }
           pose proof (Hml_y_lookup_inv u Hml_y) as Hsy.
           assert (Hσ0y_store : σ0 !! y = Some u).
           {
             rewrite <- lstore_lift_free_lookup_free.
             exact Hσ0y.
           }
           assert (Hsubσ0R :
             lvars_fv ((tm_lvars e ∪ {[LVFree y]}) ∖
               dom (atom_store_to_lvar_store σproj : LStoreT)) ⊆
             dom (σ0 : StoreT)).
           {
             rewrite HR_single, lvars_fv_singleton_free.
             intros a Ha. apply elem_of_singleton in Ha as ->.
             change (y ∈ dom (σ0 : gmap atom value)).
             apply elem_of_dom. exists u. exact Hσ0y_store.
           }
           assert (Hs_eq :
             lstore_on_lift_store
               ((tm_lvars e ∪ {[LVFree y]}) ∖
                 dom (atom_store_to_lvar_store σproj : LStoreT))
               σ0 HlcR Hsubσ0R = s).
           {
             apply lstore_on_ext.
             cbn [lstore_on_lift_store storeAO_store].
             change (storeA_restrict (lstore_lift_free σ0 : LStoreT)
               ((tm_lvars e ∪ {[LVFree y]}) ∖
                 dom (atom_store_to_lvar_store σproj : LStoreT)) =
               lso_store s).
             rewrite <- (lstore_lift_free_restrict_fv_lvars_eq σ0
               ((tm_lvars e ∪ {[LVFree y]}) ∖
                 dom (atom_store_to_lvar_store σproj : LStoreT)) HlcR).
             eapply lstore_lift_restrict_singleton_free_eq.
             - exact HR_single.
             - exact Hσ0y_store.
             - exact Hsy.
           }
           rewrite <- Hs_eq.
           apply lstore_in_lworld_on_lift_store_of_world.
           exact Hσ0fib.
        -- intros Hmem.
           pose proof (lstore_in_lworld_on_singleton_free_lookup y
             ((tm_lvars e ∪ {[LVFree y]}) ∖
               dom (atom_store_to_lvar_store σproj : LStoreT))
             mfib HlcR HsubR s HR_single Hmem)
             as [σ [Hσfib Hs_y_eq]].
           change ((mfib : WorldT) = rawA_fiber (m : WorldT) σproj)
             in Hfib_eq.
           rewrite Hfib_eq in Hσfib.
           destruct Hσfib as [Hσ Hσproj].
           pose proof (Hstores (lstore_lift_free σ)) as Hσres.
           assert (Hσlift : (res_lift_free m : LWorldT)
             (lstore_lift_free σ)).
           { exists σ. split; [exact Hσ|reflexivity]. }
           specialize (Hσres Hσlift).
           destruct Hσres as [Hyfresh [v [Hσy Hevalσ]]].
           split; [exact Hyfresh|].
           exists v. split.
           ++ change ((lso_store (lstore_on_mlsubst_back
                (tm_lvars e ∪ {[LVFree y]})
                (atom_store_to_lvar_store σproj) s) : LStoreT) !!
                LVFree y = Some v).
              apply Hml_y_lookup.
              assert (Hσy_store : σ !! y = Some v).
              {
                rewrite <- lstore_lift_free_lookup_free.
                exact Hσy.
              }
              transitivity (σ !! y); [exact Hs_y_eq|exact Hσy_store].
           ++ assert (Hsubσ : lvars_fv (tm_lvars e) ⊆ dom (σ : StoreT)).
              {
                intros a Ha.
                change (a ∈ dom (σ : gmap atom value)).
                rewrite (wfworld_store_dom m σ Hσ).
                unfold formula_scoped_in_world in Hscope.
                rewrite formula_fv_expr_result_formula in Hscope.
                apply Hscope.
                rewrite lvars_fv_union.
                apply elem_of_union_l. exact Ha.
              }
              assert (Hσproj_fv :
                store_restrict σ (lvars_fv (tm_lvars e)) = σproj).
              { rewrite <- Hproj_dom. exact Hσproj. }
              pose proof (expr_result_msubst_back_input_restrict e y
                σproj σ s HlcD Hsubσ Hσproj_fv) as Hinput_eq.
              apply (proj1 (expr_eval_in_store_restrict_lvars e
                (lso_store (lstore_on_mlsubst_back
                  (tm_lvars e ∪ {[LVFree y]})
                  (atom_store_to_lvar_store σproj) s))
                (tm_lvars e) v ltac:(intros z Hz; exact Hz))).
              rewrite Hinput_eq.
              apply (proj2 (expr_eval_in_store_restrict_lvars e
                (lstore_lift_free σ : LStoreT) (tm_lvars e) v
                ltac:(intros z Hz; exact Hz))).
              exact Hevalσ.
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
	    * pose proof (Htotal_eval (lstore_lift_free σm)
	        ltac:(exists σm; split; [exact Hσm|reflexivity])) as Hsn_m.
	      destruct (must_terminating_reaches_result _ Hsn_m) as [v Heval_m].
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
  apply expr_result_atom_world_to_formula. exact Hres.
Qed.

End TermDenotation.
