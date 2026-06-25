(** * Denotation.TypeEquivTermTLet

    TLet-specific term fiber/result-extension support. *)

From Denotation Require Import Notation TypeDenote TypeEquivCore DenotationSetMapFacts TypeEquivTermBase TypeEquivTermResult.
From CoreLang Require Import StrongNormalization.

Section TypeDenote.

Local Lemma fv_tm_open_fvar_tlete_body_subset e1 e2 z k :
  fv_tm (open_tm k (vfvar z) e2) ⊆ fv_tm (tlete e1 e2) ∪ {[z]}.
Proof.
  intros a Ha.
  pose proof (open_fv_tm e2 (vfvar z) k a Ha) as Hopen.
  cbn [fv_value] in Hopen.
  apply elem_of_union in Hopen as [Hz|He2].
  - apply elem_of_union_r. exact Hz.
  - apply elem_of_union_l.
    cbn [fv_tm]. apply elem_of_union_r. exact He2.
Qed.

Local Lemma fv_tm_tlete_left_subset e1 e2 :
  fv_tm e1 ⊆ fv_tm (tlete e1 e2).
Proof.
  intros a Ha. cbn [fv_tm]. apply elem_of_union_l. exact Ha.
Qed.

Local Lemma notin_fv_tm_tlete e1 e2 z :
  z ∉ fv_tm e1 ->
  z ∉ fv_tm e2 ->
  z ∉ fv_tm (tlete e1 e2).
Proof.
  intros Hze1 Hze2 Hz.
  cbn [fv_tm] in Hz.
  apply elem_of_union in Hz as [Hz|Hz]; [exact (Hze1 Hz)|exact (Hze2 Hz)].
Qed.

Local Lemma elem_of_fv_tm_open_fvar e z k a :
  a ∈ fv_tm (open_tm k (vfvar z) e) ->
  a ∈ {[z]} ∪ fv_tm e.
Proof.
  intros Ha.
  pose proof (open_fv_tm e (vfvar z) k a Ha) as Hopen.
  cbn [fv_value] in Hopen.
  exact Hopen.
Qed.

Local Lemma tlet_fresh_for_parts
    (σ : StoreT) e1 e2 X x z :
  z ∉ dom (σ : StoreT) ∪ fv_tm e1 ∪ fv_tm e2 ∪ X ∪ {[x]} ->
  z ∉ dom (σ : StoreT) /\
  z ∉ fv_tm e1 /\
  z ∉ fv_tm e2 /\
  z ∉ X /\
  z <> x.
Proof.
  intros Hz.
  repeat split; set_solver.
Qed.

Lemma tm_total_equiv_res_store_subset
    (m0 m : WfWorldT) e1 e2 :
  res_subset m0 m ->
  tm_total_equiv_on m e1 e2 ->
  tm_total_equiv_on m0 e1 e2.
Proof.
  intros [_ Hstores] Htotal σ Hσ.
  apply Htotal. exact (Hstores σ Hσ).
Qed.

Lemma tm_fiber_equiv_tlete_body_extension
    (m mx : WfWorldT) X e1 e2 x Fx :
  x ∉ fv_tm e2 ->
  x ∉ X ->
  lc_tm (tlete e1 e2) ->
  wfworld_closed_on (fv_tm (tlete e1 e2)) mx ->
  fv_tm (e2 ^^ x) ⊆ world_dom (mx : WorldT) ->
  expr_total_on_atom_world (tlete e1 e2) mx ->
  expr_result_extension_witness e1 x Fx ->
  res_extend_by m Fx mx ->
  tm_fiber_equiv_on mx X (e2 ^^ x) (tlete e1 e2).
Proof.
  intros Hxe2 HxX Hlc_tlet Hclosed_tlet Hfv_body_world
    Htotal_tlet HFx Hext σ0 Hσ0 v.
  destruct HFx as [Hx_e1 [Hin Hout] Hrel].
  assert (Hx_tlet : x ∉ fv_tm (tlete e1 e2)).
  { apply notin_fv_tm_tlete; assumption. }
  pose proof Hlc_tlet as Hlc_tlet_parts.
  apply lc_lete_iff_body in Hlc_tlet_parts as [_ Hbody_e2].
  split.
  - intros [σ [Hσmx [HσX He2x]]].
    assert (Hclosedσ : store_closed (store_restrict σ (fv_tm (tlete e1 e2)))).
    { eapply wfworld_closed_on_store_restrict_closed; eauto. }
    assert (Hmust_tlet :
        must_terminating (lstore_instantiate_tm (lstore_lift_free σ)
          (tlete e1 e2))).
    {
      destruct Htotal_tlet as [_ Htotal].
      apply Htotal. exists σ. split; [exact Hσmx|reflexivity].
    }
    pose proof (must_terminating_tlete_elim_e1 _ _ Hmust_tlet) as Hmust_e1.
    destruct (must_terminating_reaches_result _ Hmust_e1) as [vx0 He1_full0].
    assert (He1_total : exists vx, tm_eval_in_store (store_restrict σ (fv_tm e1)) e1 vx).
    {
      exists vx0.
      apply (proj2 (tm_eval_in_store_restrict_fv_exact σ e1 vx0)).
      exact He1_full0.
    }
    destruct (result_extension_store_lookup_output e1 x Fx m mx σ
      ltac:(constructor; [exact Hx_e1|split; [exact Hin|exact Hout]|exact Hrel])
      Hext Hσmx He1_total) as [vx [Hx_lookup He1]].
    set (z := fresh_for (dom (σ : StoreT) ∪ fv_tm e1 ∪ fv_tm e2 ∪ X ∪ {[x]})).
    assert (Hzfresh :
        z ∉ dom (σ : StoreT) ∪ fv_tm e1 ∪ fv_tm e2 ∪ X ∪ {[x]})
      by (subst z; apply fresh_for_not_in).
    destruct (tlet_fresh_for_parts σ e1 e2 X x z Hzfresh)
      as [Hzσ [Hze1 [Hze2 [_ Hz_ne_x]]]].
    assert (Hscope_x :
        tm_lvars (e2 ^^ x) ⊆ lvars_of_atoms (dom (σ : StoreT))).
    {
      intros lv Hlv.
      rewrite (tm_lvars_lc_eq_atoms (e2 ^^ x)) in Hlv.
      2:{ apply body_open_tm; [exact Hbody_e2|constructor]. }
      unfold lvars_of_atoms in Hlv |- *.
      apply elem_of_map in Hlv as [a [-> Ha]].
      apply elem_of_map. exists a. split; [reflexivity|].
      change (a ∈ dom (σ : gmap atom value)).
      rewrite (wfworld_store_dom mx σ Hσmx).
      apply Hfv_body_world. exact Ha.
    }
    assert (He2z_full :
        tm_eval_in_store (<[z := vx]> σ) (e2 ^^ z) v).
    {
      apply (proj1 (tm_eval_in_store_open_alias e2 σ x z vx v
        Hx_lookup Hzσ Hxe2 Hze2 Hscope_x)).
      exact He2x.
    }
    assert (Hagree_z :
        store_restrict (<[z := vx]> σ) (fv_tm (e2 ^^ z)) =
        store_restrict
          (<[z := vx]> (store_restrict σ (fv_tm (tlete e1 e2)) : StoreT))
          (fv_tm (e2 ^^ z))).
    {
      apply store_restrict_insert_agree_on_observed.
      - apply fv_tm_open_fvar_tlete_body_subset.
      - exact Hzσ.
      - apply notin_fv_tm_tlete; assumption.
    }
    assert (He2z_restrict :
        tm_eval_in_store
          (<[z := vx]> (store_restrict σ (fv_tm (tlete e1 e2)) : StoreT))
          (e2 ^^ z) v).
    {
      apply (proj1 (tm_eval_in_store_agree_on_fv _ _ _ _ Hagree_z)).
      exact He2z_full.
    }
    assert (He1_tlet :
        tm_eval_in_store (store_restrict σ (fv_tm (tlete e1 e2))) e1 vx).
    {
      assert (Hagree_e1 :
          store_restrict (store_restrict σ (fv_tm e1)) (fv_tm e1) =
          store_restrict (store_restrict σ (fv_tm (tlete e1 e2))) (fv_tm e1)).
      {
        transitivity (store_restrict σ (fv_tm e1)).
        - apply storeA_restrict_twice_same.
        - symmetry. apply storeA_restrict_twice_subset.
          apply fv_tm_tlete_left_subset.
      }
      apply (proj1 (tm_eval_in_store_agree_on_fv
        (store_restrict σ (fv_tm e1))
        (store_restrict σ (fv_tm (tlete e1 e2))) e1 vx Hagree_e1)).
      exact He1.
    }
    exists σ. split; [exact Hσmx|]. split; [exact HσX|].
    eapply tm_eval_in_store_tlete_intro_closed_on.
    + exact Hclosedσ.
    + exact Hlc_tlet.
    + intros Hz_bad.
      apply elem_of_union in Hz_bad as [Hz_bad|Hz_bad].
      * exact (Hzσ Hz_bad).
      * exact (Hze2 Hz_bad).
    + exact He1_tlet.
    + exact He2z_restrict.
  - intros [σ [Hσmx [HσX Hlet]]].
    assert (Hclosedσ : store_closed (store_restrict σ (fv_tm (tlete e1 e2)))).
    { eapply wfworld_closed_on_store_restrict_closed; eauto. }
    set (z := fresh_for (dom (σ : StoreT) ∪ fv_tm e1 ∪ fv_tm e2 ∪ X ∪ {[x]})).
    assert (Hzfresh :
        z ∉ dom (σ : StoreT) ∪ fv_tm e1 ∪ fv_tm e2 ∪ X ∪ {[x]})
      by (subst z; apply fresh_for_not_in).
    destruct (tlet_fresh_for_parts σ e1 e2 X x z Hzfresh)
      as [_ [Hze1 [Hze2 [_ Hz_ne_x]]]].
    assert (Hztlet : z ∉ fv_tm (tlete e1 e2)).
    { apply notin_fv_tm_tlete; assumption. }
    destruct (tm_eval_in_store_tlete_elim_closed_on e1 e2 z σ v
      Hclosedσ Hztlet Hze2 Hlet) as [vx [He1 He2z]].
    apply (proj1 (resA_extend_by_store_iff m Fx mx σ Hext)) in Hσmx.
    destruct Hσmx as [σm [we [σe [Hσm [HFrel [Hσe ->]]]]]].
    assert (Hσe_dom : dom (σe : StoreT) = {[x]}).
    {
      pose proof (wfworldA_store_dom we σe Hσe) as Hdomσe.
      change (dom (σe : StoreT) = world_dom (we : WorldT)) in Hdomσe.
      rewrite Hdomσe.
      pose proof (extA_rel_dom Fx (store_restrict σm (ext_in Fx)) we) as Hdom_we.
      rewrite <- Hout.
      apply Hdom_we; [|exact HFrel].
      eapply extA_projection_dom.
      - apply resA_extend_by_applicable in Hext. exact Hext.
      - exact Hσm.
    }
    assert (He1_base :
        tm_eval_in_store (store_restrict σm (fv_tm e1)) e1 vx).
    {
      assert (Hagree_e1 :
          store_restrict (store_restrict ((σm : StoreT) ∪ σe) (fv_tm e1))
            (fv_tm e1) =
          store_restrict (store_restrict σm (fv_tm e1)) (fv_tm e1)).
      {
        rewrite !storeA_restrict_twice_same.
        apply storeA_restrict_union_ignore_r.
        change (dom (σe : StoreT) ## fv_tm e1).
        rewrite Hσe_dom.
        apply disjoint_singleton_l. exact Hx_e1.
      }
      apply (proj1 (tm_eval_in_store_agree_on_fv
        (store_restrict ((σm : StoreT) ∪ σe) (fv_tm e1))
        (store_restrict σm (fv_tm e1)) e1 vx Hagree_e1)).
      exact He1.
    }
    assert (Hσm_dom_fv :
        dom (store_restrict σm (fv_tm e1) : StoreT) = fv_tm e1).
    {
      rewrite <- Hin.
      eapply extA_projection_dom.
      - apply resA_extend_by_applicable in Hext. exact Hext.
      - exact Hσm.
    }
    pose proof (expr_result_extension_apply_total_store e1 x Fx
      (store_restrict σm (fv_tm e1)) we vx
      ltac:(constructor; [exact Hx_e1|split; [exact Hin|exact Hout]|exact Hrel])
      Hσm_dom_fv
      ltac:(unfold ext_rel; rewrite <- Hin; exact HFrel)
      He1_base) as Hwe_vx.
    set (σx := (σm : StoreT) ∪ ({[x := vx]} : StoreT)).
    assert (Hσx_mx : (mx : WorldT) σx).
    {
      apply (proj2 (resA_extend_by_store_iff m Fx mx σx Hext)).
      exists σm, we, ({[x := vx]} : StoreT).
      split; [exact Hσm|]. split.
      - exact HFrel.
      - split; [exact Hwe_vx|reflexivity].
    }
    assert (HσxX : store_restrict σx X = σ0).
    {
      rewrite <- HσX.
      unfold σx.
      transitivity (store_restrict σm X).
      - apply storeA_restrict_union_ignore_r.
        change (dom (({[x := vx]} : StoreT) : gmap atom value) ## X).
        pose proof (dom_singleton_L (M:=gmap atom) x vx) as Hdom_single.
        change (dom (({[x := vx]} : StoreT) : gmap atom value) = {[x]})
          in Hdom_single.
        rewrite Hdom_single. apply disjoint_singleton_l. exact HxX.
      - symmetry.
        apply storeA_restrict_union_ignore_r.
        change (dom (σe : StoreT) ## X).
        rewrite Hσe_dom.
        apply disjoint_singleton_l. exact HxX.
    }
    assert (Hx_lookup_σx : σx !! x = Some vx).
    {
      unfold σx.
      apply map_lookup_union_Some_raw. right.
      split.
      - apply eq_None_not_Some. intros [u Hlook].
        pose proof (res_extend_by_output_fresh m Fx mx Hext) as Hfresh_out.
        change (ext_out Fx ## world_dom (m : WorldT)) in Hfresh_out.
        rewrite Hout in Hfresh_out.
        pose proof (wfworldA_store_dom m σm Hσm) as Hσm_dom.
        change (dom (σm : StoreT) = world_dom (m : WorldT)) in Hσm_dom.
        apply elem_of_dom_2 in Hlook.
        apply disjoint_singleton_l in Hfresh_out.
        apply Hfresh_out.
        rewrite <- Hσm_dom. exact Hlook.
      - apply map_lookup_singleton.
    }
    assert (Hscope_x :
        tm_lvars (e2 ^^ x) ⊆ lvars_of_atoms (dom (σx : StoreT))).
    {
      intros lv Hlv.
      rewrite (tm_lvars_lc_eq_atoms (e2 ^^ x)) in Hlv.
      2:{ apply body_open_tm; [exact Hbody_e2|constructor]. }
      unfold lvars_of_atoms in Hlv |- *.
      apply elem_of_map in Hlv as [a [-> Ha]].
      apply elem_of_map. exists a. split; [reflexivity|].
      change (a ∈ dom (σx : gmap atom value)).
      rewrite (wfworld_store_dom mx σx Hσx_mx).
      apply Hfv_body_world. exact Ha.
    }
    assert (He2z_full :
        tm_eval_in_store (<[z := vx]> σx) (e2 ^^ z) v).
    {
      assert (Hagree_z :
          store_restrict
            (<[z := vx]> (store_restrict ((σm : StoreT) ∪ σe)
              (fv_tm (tlete e1 e2)) : StoreT))
            (fv_tm (e2 ^^ z)) =
          store_restrict (<[z := vx]> σx) (fv_tm (e2 ^^ z))).
      {
        subst σx.
        apply storeA_map_eq. intros a.
        rewrite !storeA_restrict_lookup.
        destruct (decide (a ∈ fv_tm (e2 ^^ z))) as [Ha|Ha]; [|reflexivity].
        assert (Ha_open : a ∈ {[z]} ∪ fv_tm e2).
        { apply (elem_of_fv_tm_open_fvar e2 z 0). exact Ha. }
        assert (Hax : a <> x).
        {
          intros ->.
          apply elem_of_union in Ha_open as [Haz|Ha_e2].
          - apply elem_of_singleton in Haz.
            exact (Hz_ne_x (eq_sym Haz)).
          - exact (Hxe2 Ha_e2).
        }
        destruct (decide (a = z)) as [->|Haz].
        - change (((<[z := vx]>
              (store_restrict ((σm : StoreT) ∪ σe) (fv_tm (tlete e1 e2))
                : StoreT)) : gmap atom value) !! z =
            ((<[z := vx]> ((σm : StoreT) ∪ ({[x := vx]} : StoreT))
                : StoreT) : gmap atom value) !! z).
          transitivity (Some vx).
          + apply map_lookup_insert.
          + symmetry. apply map_lookup_insert.
        - change (((<[z := vx]>
              (store_restrict ((σm : StoreT) ∪ σe) (fv_tm (tlete e1 e2))
                : StoreT)) : gmap atom value) !! a =
            ((<[z := vx]> ((σm : StoreT) ∪ ({[x := vx]} : StoreT))
                : StoreT) : gmap atom value) !! a).
	          transitivity
	            ((store_restrict ((σm : StoreT) ∪ σe)
	                (fv_tm (tlete e1 e2)) : StoreT) !! a).
	          + apply map_lookup_insert_ne. exact Haz.
	          + transitivity
	              (((σm : StoreT) ∪ ({[x := vx]} : StoreT)) !! a).
	            2:{ symmetry. apply map_lookup_insert_ne. exact Haz. }
	          change ((storeA_restrict
	              (((σm : StoreT) : gmap atom value) ∪
	                ((σe : StoreT) : gmap atom value))
	              (fv_tm (tlete e1 e2))) !! a =
	            ((((σm : StoreT) : gmap atom value) ∪
	              ({[x := vx]} : gmap atom value)) !! a)).
	          rewrite (storeA_restrict_lookup (V:=value)
	            (((σm : StoreT) : gmap atom value) ∪
	              ((σe : StoreT) : gmap atom value))
	            (fv_tm (tlete e1 e2)) a).
	          destruct (decide (a ∈ fv_tm (tlete e1 e2))) as [Ha_tlet|Ha_tlet].
	          2:{
                    exfalso. apply Ha_tlet.
                    cbn [fv_tm]. apply elem_of_union_r.
                    apply elem_of_union in Ha_open as [Haz_open|Ha_e2].
                    - apply elem_of_singleton in Haz_open.
                      exact (False_rect _ (Haz Haz_open)).
                    - exact Ha_e2.
                  }
	          destruct ((σm : StoreT) !! a) eqn:Haσm.
	          { transitivity (Some v0).
	            - transitivity ((σm : StoreT) !! a).
	              + apply lookup_union_l'. exists v0. exact Haσm.
	              + exact Haσm.
	            - symmetry. transitivity ((σm : StoreT) !! a).
	              + apply lookup_union_l'. exists v0. exact Haσm.
	              + exact Haσm. }
	          { transitivity ((σe : StoreT) !! a).
	            - apply (lookup_union_r (M:=gmap atom) (A:=value)
	                (σm : StoreT) (σe : StoreT) a). exact Haσm.
	            - transitivity (@None value).
		              + change (((σe : StoreT) : gmap atom value) !! a = None).
		                apply not_elem_of_dom_1.
		                change (a ∉ dom (σe : StoreT)).
		                rewrite Hσe_dom.
                                intros Ha_single. apply elem_of_singleton in Ha_single.
                                exact (Hax Ha_single).
	              + symmetry.
	                transitivity (({[x := vx]} : gmap atom value) !! a).
	                * apply (lookup_union_r (M:=gmap atom) (A:=value)
		                    (σm : StoreT) ({[x := vx]} : gmap atom value) a).
		                  exact Haσm.
	                * apply lookup_singleton_ne. congruence. }
      }
      apply (proj1 (tm_eval_in_store_agree_on_fv _ _ _ _ Hagree_z)).
      exact He2z.
    }
	    assert (He2x :
	        tm_eval_in_store σx (e2 ^^ x) v).
	    {
	      assert (Hzσx : z ∉ dom (σx : StoreT)).
	      {
                subst σx.
	                apply notin_store_union_singleton_dom; [|exact Hz_ne_x].
	                intros Hzσm.
	                apply Hzfresh. repeat apply elem_of_union_l.
	                change (z ∈ dom (σm : gmap atom value)) in Hzσm.
	                apply elem_of_dom in Hzσm as [vz Hlook].
	                change (z ∈ dom
                          ((((σm : StoreT) : gmap atom value) ∪
                            ((σe : StoreT) : gmap atom value)) : gmap atom value)).
	                rewrite elem_of_dom. exists vz.
	                apply map_lookup_union_Some_raw. left. exact Hlook.
	      }
	      apply (proj2 (tm_eval_in_store_open_alias e2 σx x z vx v
	        Hx_lookup_σx Hzσx
	        Hxe2 Hze2 Hscope_x)).
	      exact He2z_full.
	    }
    exists σx. split; [exact Hσx_mx|]. split; [exact HσxX|exact He2x].
Qed.


End TypeDenote.
