(** * BasicDenotation.TermExtension

    Split out from [Term.v] to keep individual proof files small. *)

From ContextBasicDenotation Require Import Notation StoreTyping.
From ContextBasicDenotation Require Export TermOpen.

Section TermDenotation.

Lemma expr_result_extension_shape e x Hfresh :
  ext_in (expr_result_extension e x Hfresh) = fv_tm e /\
  ext_out (expr_result_extension e x Hfresh) = {[x]}.
Proof.
  unfold expr_result_extension, ext_in, ext_out, mk_fiber_extension.
  simpl. split; reflexivity.
Qed.

Record expr_result_extension_witness
    (e : tm) (x : atom) (Fx : FiberExtensionT) : Prop := {
  expr_result_extension_witness_fresh : x ∉ fv_tm e;
  expr_result_extension_witness_shape :
    ext_in Fx = fv_tm e /\ ext_out Fx = {[x]};
  expr_result_extension_witness_rel :
    forall σ,
      dom σ = fv_tm e ->
      ext_rel Fx σ (expr_result_output_world e x σ);
}.

Lemma expr_result_extension_witness_exists e x :
  x ∉ fv_tm e ->
  exists Fx, expr_result_extension_witness e x Fx.
Proof.
  intros Hfresh.
  exists (expr_result_extension e x Hfresh).
  constructor.
  - exact Hfresh.
  - apply expr_result_extension_shape.
  - intros σ Hdom.
    unfold expr_result_extension, ext_rel, mk_fiber_extension,
      mk_fiber_extension_rel.
    simpl. reflexivity.
Qed.

Lemma expr_result_extension_apply_total_store e x F σ w v :
  expr_result_extension_witness e x F ->
  dom σ = fv_tm e ->
  ext_rel F σ w ->
  expr_eval_in_atom_store σ e v ->
  (w : WorldT) ({[x := v]} : StoreT).
Proof.
  intros Hwitness Hdom Hrel Heval.
  destruct Hwitness as [Hfresh [Hin Hout] Hwrel].
  pose proof (Hwrel σ Hdom) as Hcanonical.
  assert (HdomF : dom σ = extA_in F).
  { unfold ext_in in Hin. rewrite Hin. exact Hdom. }
  pose proof (proj2 (extA_rel_extensional F σ w
    (expr_result_output_world e x σ) ({[x := v]} : StoreT)
    HdomF Hrel Hcanonical)) as Hto.
  apply Hto.
  unfold expr_result_output_world.
  destruct (excluded_middle_informative (exists v0, expr_eval_in_atom_store σ e v0))
    as [Hex | Hnone].
  - destruct (constructive_indefinite_description _ Hex) as [v0 Heval0].
    assert (v0 = v).
    {
      unfold expr_eval_in_atom_store, expr_eval_in_store in *.
      eapply steps_result_unique; eauto.
    }
    subst v0. simpl. reflexivity.
  - exfalso. apply Hnone. exists v. exact Heval.
Qed.

Lemma expr_result_extension_apply_total_iff e x F σ w :
  expr_result_extension_witness e x F ->
  dom σ = fv_tm e ->
  ext_rel F σ w ->
  (exists v, expr_eval_in_atom_store σ e v) ->
  forall σout,
    (w : WorldT) σout <->
    exists v, expr_eval_in_atom_store σ e v /\ σout = ({[x := v]} : StoreT).
Proof.
  intros Hwitness Hdom Hrel Htotal σout.
  destruct Hwitness as [Hfresh [Hin Hout] Hwrel].
  pose proof (Hwrel σ Hdom) as Hcanonical.
  assert (HdomF : dom σ = extA_in F).
  { unfold ext_in in Hin. rewrite Hin. exact Hdom. }
  pose proof (extA_rel_extensional F σ w
    (expr_result_output_world e x σ) σout HdomF Hrel Hcanonical) as Hext.
  split.
  - intros Hw.
    apply Hext in Hw.
    unfold expr_result_output_world in Hw.
    destruct (excluded_middle_informative (exists v, expr_eval_in_atom_store σ e v))
      as [Hex | Hnone].
    + destruct (constructive_indefinite_description _ Hex) as [v Hv].
      exists v. split; [exact Hv|].
      simpl in Hw. subst σout. reflexivity.
    + exfalso. apply Hnone. exact Htotal.
  - intros [v [Heval ->]].
    eapply expr_result_extension_apply_total_store; eauto.
	    constructor; [exact Hfresh|split; assumption|exact Hwrel].
Qed.

Lemma expr_result_output_world_functional e x σ σ1 σ2 :
  (expr_result_output_world e x σ : WorldT) σ1 ->
  (expr_result_output_world e x σ : WorldT) σ2 ->
  σ1 = σ2.
Proof.
  unfold expr_result_output_world.
  destruct (excluded_middle_informative (exists v, expr_eval_in_atom_store σ e v))
    as [Hex | Hnone].
  - destruct (constructive_indefinite_description _ Hex) as [v Hv].
    simpl. intros -> ->. reflexivity.
  - simpl. intros -> ->. reflexivity.
Qed.

Lemma expr_result_extension_functional_on e x F (m mx : WfWorldT) :
  expr_result_extension_witness e x F ->
  res_extend_by m F mx ->
  fiber_extension_functional_on m F.
Proof.
  intros Hwitness Hext σ w σe1 σe2 Hσ Hrel Hσe1 Hσe2.
  destruct Hwitness as [Hfresh [Hin Hout] Hwrel].
  assert (Hdomσ : dom σ = world_dom (m : WorldT)).
  { eapply wfworld_store_dom. exact Hσ. }
  assert (Hdom : dom (store_restrict σ (ext_in F)) = fv_tm e).
  {
    pose proof (storeA_restrict_dom σ (ext_in F)) as Hrestrict_dom.
    change (dom (store_restrict σ (ext_in F) : StoreT) =
      dom σ ∩ ext_in F) in Hrestrict_dom.
    rewrite Hrestrict_dom, Hdomσ.
    pose proof (res_extend_by_input_dom m F mx Hext) as Hin_dom.
    rewrite Hin. set_solver.
  }
  pose proof (Hwrel (store_restrict σ (ext_in F)) Hdom) as Hcanonical.
  assert (HdomF : dom (store_restrict σ (ext_in F)) = ext_in F).
  { rewrite Hdom, Hin. reflexivity. }
  pose proof (extA_rel_extensional F
    (store_restrict σ (ext_in F)) w
    (expr_result_output_world e x (store_restrict σ (ext_in F)))
    σe1 HdomF Hrel Hcanonical) as Hext1.
  pose proof (extA_rel_extensional F
    (store_restrict σ (ext_in F)) w
    (expr_result_output_world e x (store_restrict σ (ext_in F)))
    σe2 HdomF Hrel Hcanonical) as Hext2.
  eapply expr_result_output_world_functional.
  - apply Hext1. exact Hσe1.
  - apply Hext2. exact Hσe2.
Qed.

Lemma result_extension_has_ltype_from_basic_world
    (Σ : lty_env) (T : ty) (e1 : tm) (m mx : WfWorldT)
    (Fx : FiberExtensionT) (x : atom) :
  LVFree x ∉ dom Σ ->
  expr_result_extension_witness e1 x Fx ->
  res_extend_by m Fx mx ->
  res_models mx (basic_world_formula (<[LVFree x := T]> Σ)) ->
  extension_has_ltype (<[LVFree x := T]> ∅) (res_restrict m (ext_in Fx)) Fx.
Proof.
  intros HxΣ Hwitness Hext Hmx_basic.
  destruct Hwitness as [Hx_fv [Hin Hout] Hrel].
  apply basic_world_formula_models_iff in Hmx_basic as [_ [_ Hmx_typed]].
  unfold extension_has_ltype.
  split.
  - simpl. pose proof (res_extend_by_input_dom m Fx mx Hext) as Hin_sub.
    unfold ext_in in Hin_sub. set_solver.
  - split.
    + intros [k|y] Hy; cbn [lc_logic_var_key]; [|exact I].
      change (LVBound k ∈ dom ({[LVFree x := T]} : gmap logic_var ty)) in Hy.
      rewrite dom_singleton_L in Hy. set_solver.
    + split.
      * change (lvars_fv (dom ({[LVFree x := T]} : gmap logic_var ty)) = ext_out Fx).
        rewrite dom_singleton_L.
        rewrite lvars_fv_singleton_free.
        rewrite Hout. set_solver.
      * intros σout mout Hσout HF.
        unfold lworld_has_type, worldA_has_type.
        split.
        -- change (dom ({[LVFree x := T]} : gmap logic_var ty) ⊆
             worldA_dom (res_lift_free mout : LWorldT)).
           rewrite dom_singleton_L, res_lift_free_dom.
           pose proof (extA_rel_dom Fx σout mout) as Hdom_mout.
           assert (dom (σout : gmap atom value) = ext_in Fx) as Hσout_dom.
           {
             simpl in Hσout.
             destruct Hσout as [σm [Hσm Hrestrict]].
             rewrite <- Hrestrict.
             change (dom (store_restrict σm (ext_in Fx) : gmap atom value) = ext_in Fx).
             rewrite store_restrict_dom.
             pose proof (res_extend_by_input_dom m Fx mx Hext) as Hin_sub.
             unfold ext_in in Hin_sub.
             pose proof (wfworldA_store_dom m σm Hσm) as Hσm_dom.
             change (dom (σm : gmap atom value) = world_dom (m : WorldT)) in Hσm_dom.
             rewrite Hσm_dom. set_solver.
           }
           specialize (Hdom_mout Hσout_dom HF).
           change (world_dom (mout : WorldT) = ext_out Fx) in Hdom_mout.
           intros v Hv.
           rewrite elem_of_singleton in Hv. subst v.
           unfold lvars_of_atoms. apply elem_of_map.
           exists x. split; [reflexivity|].
           change (x ∈ world_dom (mout : WorldT)).
           rewrite Hdom_mout, Hout. set_solver.
        -- intros τ Hτ.
           destruct Hτ as [σe [Hσe ->]].
           intros v U u HΣout Hu.
           change (((<[LVFree x := T]> (∅ : lty_env) : lty_env)
             : gmap logic_var ty) !! v = Some U) in HΣout.
           destruct v as [k|y].
           ++ change ((<[LVFree x := T]> (∅ : gmap logic_var ty) : gmap logic_var ty) !!
                LVBound k = Some U) in HΣout.
              rewrite lookup_insert_ne in HΣout by discriminate.
              rewrite lookup_empty in HΣout. discriminate.
           ++ change ((<[LVFree x := T]> (∅ : gmap logic_var ty) : gmap logic_var ty) !!
                LVFree y = Some U) in HΣout.
              destruct (decide (y = x)) as [->|Hyx].
              ** rewrite lookup_insert in HΣout.
                 destruct (decide (LVFree x = LVFree x)) as [_|Hneq];
                   [|congruence].
                 injection HΣout as ->.
                 change (((lstore_lift_free σe : LStoreT) : gmap logic_var value) !!
                   LVFree x = Some u) in Hu.
                 rewrite lstore_lift_free_lookup_free in Hu.
                 simpl in Hσout.
                 destruct Hσout as [σm [Hσm Hrestrict]].
                 rewrite <- Hrestrict in HF.
                 assert (Hmx_store :
                   (mx : WorldT) (σm ∪ σe)).
                 {
                   apply (proj2 (resA_extend_by_store_iff m Fx mx
                     (σm ∪ σe) Hext)).
                   exists σm, mout, σe. repeat split; try assumption.
                 }
                 assert (Hx_not_m : σm !! x = None).
                 {
                   change (((σm : gmap atom value) !! x) = None).
	                   apply not_elem_of_dom.
	                   pose proof (res_extend_by_output_fresh m Fx mx Hext) as Hfresh.
	                   change (ext_out Fx ## world_dom (m : WorldT)) in Hfresh.
	                   rewrite Hout in Hfresh.
                   pose proof (wfworldA_store_dom m σm Hσm) as Hσm_dom.
                   change (dom (σm : gmap atom value) = world_dom (m : WorldT)) in Hσm_dom.
                   rewrite Hσm_dom.
                   set_solver.
                 }
                 destruct Hmx_typed as [_ Hstores_typed].
                 specialize (Hstores_typed (lstore_lift_free (σm ∪ σe))).
                 assert (Hlift_mx :
                   worldA_stores (res_lift_free mx : LWorldT)
                     (lstore_lift_free (σm ∪ σe))).
                 { exists (σm ∪ σe). split; [exact Hmx_store|reflexivity]. }
	                 specialize (Hstores_typed Hlift_mx).
	                 eapply (Hstores_typed (LVFree x) U u).
	                 --- change ((<[LVFree x := U]> (Σ : gmap logic_var ty)
	                        : gmap logic_var ty) !! LVFree x = Some U).
	                     rewrite lookup_insert.
	                     destruct (decide (LVFree x = LVFree x)); [reflexivity|congruence].
                 --- change (((lstore_lift_free (σm ∪ σe) : LStoreT)
                        : gmap logic_var value) !! LVFree x = Some u).
                     rewrite lstore_lift_free_lookup_free.
                     change (((σm : gmap atom value) ∪ (σe : gmap atom value)) !! x = Some u).
                     rewrite storeA_lookup_union_Some_raw.
                     right. split; [exact Hx_not_m|exact Hu].
              ** rewrite lookup_insert_ne in HΣout by congruence.
                 rewrite lookup_empty in HΣout. discriminate.
Qed.

End TermDenotation.
