(** * Denotation.TypeEquivTermBase

    Term, totality, and fiber-result equivalence support for type denotation transport. *)

From Denotation Require Import Notation TypeDenote TypeEquivCore
  DenotationSetMapFacts.
From CoreLang Require Import StrongNormalization.

Section TypeDenote.

Definition tm_equiv_on
    (m : WfWorldT) (e1 e2 : tm) : Prop :=
  forall σ v,
    worldA_stores (m : WorldT) σ ->
    tm_eval_in_store σ e1 v <->
    tm_eval_in_store σ e2 v.

Definition tm_total_equiv_on
    (m : WfWorldT) (e1 e2 : tm) : Prop :=
  forall σ,
    worldA_stores (m : WorldT) σ ->
    must_terminating
      (lstore_instantiate_tm (lstore_lift_free σ) e1) <->
    must_terminating
      (lstore_instantiate_tm (lstore_lift_free σ) e2).

Definition tm_fiber_result_on
    (m : WfWorldT) (X : aset) (e : tm) (σ0 : StoreT) (v : value) : Prop :=
  exists σ,
    worldA_stores (m : WorldT) σ /\
    store_restrict σ X = σ0 /\
    tm_eval_in_store σ e v.

(** [tm_fiber_equiv_on m X e_src e_tgt] compares the result sets of two
    terms inside each [X]-projection fiber of [m].  The comparison is exact:
    both directions are required.  This exactness is essential because type
    denotation contains both over- and under-approximate refinements. *)
Definition tm_fiber_equiv_on
    (m : WfWorldT) (X : aset) (e1 e2 : tm) : Prop :=
  forall σ0,
    worldA_stores (res_restrict m X : WorldT) σ0 ->
    forall v,
      tm_fiber_result_on m X e1 σ0 v <->
      tm_fiber_result_on m X e2 σ0 v.

Definition tm_result_refines_projected_on
    (m : WfWorldT) (D : lvset) (e_src e_tgt : tm) : Prop :=
  forall y (my_src : WfWorldT),
    y ∉ world_dom (m : WorldT) ∪
      fv_tm e_src ∪ fv_tm e_tgt ∪ lvars_fv D ->
    world_dom (my_src : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
    res_restrict my_src (world_dom (m : WorldT)) = m ->
    my_src ⊨ expr_result_formula_at (D ∪ tm_lvars e_src) e_src (LVFree y) ->
    exists my_tgt : WfWorldT,
      world_dom (my_tgt : WorldT) = world_dom (m : WorldT) ∪ {[y]} /\
        res_restrict my_tgt (world_dom (m : WorldT)) = m /\
        my_tgt ⊨ expr_result_formula_at (D ∪ tm_lvars e_tgt) e_tgt (LVFree y) /\
        res_restrict my_tgt
          (lvars_fv D ∪ {[y]}) =
        res_restrict my_src
          (lvars_fv D ∪ {[y]}).

Definition tm_result_equiv_projected_on
    (m : WfWorldT) (D : lvset) (e1 e2 : tm) : Prop :=
  tm_result_refines_projected_on m D e1 e2 /\
  tm_result_refines_projected_on m D e2 e1.

Definition typed_total_equiv_on
    (Σ : lty_env) (τ : context_ty) (m : WfWorldT)
    (e1 e2 : tm) : Prop :=
  tm_equiv_on m e1 e2 /\
  tm_total_equiv_on m e1 e2 /\
  m ⊨ ty_denote_gas 0 Σ τ e1 /\
  m ⊨ ty_denote_gas 0 Σ τ e2.

(** The main type-level transport premise is exact result-set equality inside
    each [FV τ]-fiber.  This is intentionally stronger and simpler than the
    projected witness relation used inside Over/Under/Sum: the latter is a
    derived view of this fiber equality, not the public transport premise.
    The two gas-zero denotations provide the source/target guards, including
    strong totality, so [tm_total_equiv_on] is not part of this record. *)
Definition typed_fiber_equiv_on
    (Σ : lty_env) (τ : context_ty) (m : WfWorldT) (e1 e2 : tm) : Prop :=
  tm_fiber_equiv_on m (lvars_fv (context_ty_lvars τ)) e1 e2 /\
  m ⊨ ty_denote_gas 0 Σ τ e1 /\
  m ⊨ ty_denote_gas 0 Σ τ e2.

Lemma typed_fiber_equiv_intro
    Σ τ m e1 e2 :
  tm_fiber_equiv_on m (lvars_fv (context_ty_lvars τ)) e1 e2 ->
  m ⊨ ty_denote_gas 0 Σ τ e1 ->
  m ⊨ ty_denote_gas 0 Σ τ e2 ->
  typed_fiber_equiv_on Σ τ m e1 e2.
Proof.
  intros Hfib Hzero1 Hzero2.
  unfold typed_fiber_equiv_on.
  split; [exact Hfib|].
  split; assumption.
Qed.

Lemma typed_fiber_equiv_sym
    Σ τ m e1 e2 :
  typed_fiber_equiv_on Σ τ m e1 e2 ->
  typed_fiber_equiv_on Σ τ m e2 e1.
Proof.
  intros [Hfib [Hzero1 Hzero2]].
  split.
  - intros σ0 Hσ0 v. symmetry. apply Hfib. exact Hσ0.
  - split; assumption.
Qed.

Lemma tm_fiber_equiv_on_refl m X e :
  tm_fiber_equiv_on m X e e.
Proof.
  intros σ0 Hσ0 v. reflexivity.
Qed.

Lemma tm_fiber_equiv_on_sym m X e1 e2 :
  tm_fiber_equiv_on m X e1 e2 ->
  tm_fiber_equiv_on m X e2 e1.
Proof.
  intros Heq σ0 Hσ0 v. symmetry. apply Heq. exact Hσ0.
Qed.

Lemma tm_fiber_equiv_on_trans m X e1 e2 e3 :
  tm_fiber_equiv_on m X e1 e2 ->
  tm_fiber_equiv_on m X e2 e3 ->
  tm_fiber_equiv_on m X e1 e3.
Proof.
  intros H12 H23 σ0 Hσ0 v.
  rewrite (H12 σ0 Hσ0 v). apply H23. exact Hσ0.
Qed.

Lemma tm_fiber_equiv_on_mono m Xsmall Xbig e1 e2 :
  Xsmall ⊆ Xbig ->
  tm_fiber_equiv_on m Xbig e1 e2 ->
  tm_fiber_equiv_on m Xsmall e1 e2.
Proof.
  intros Hsub Heq σ0 Hσ0 v.
  split; intros [σ [Hσ [Hproj Heval]]].
  - pose proof (Heq (store_restrict σ Xbig)
      ltac:(exists σ; split; [exact Hσ|reflexivity]) v) as [H12 _].
    destruct (H12 ltac:(exists σ; split; [exact Hσ|split; [reflexivity|exact Heval]]))
      as [σ2 [Hσ2 [Hproj_big Heval2]]].
    exists σ2. split; [exact Hσ2|]. split; [|exact Heval2].
    rewrite <- Hproj.
    eapply storeA_restrict_eq_mono; [exact Hsub|exact Hproj_big].
  - pose proof (Heq (store_restrict σ Xbig)
      ltac:(exists σ; split; [exact Hσ|reflexivity]) v) as [_ H21].
    destruct (H21 ltac:(exists σ; split; [exact Hσ|split; [reflexivity|exact Heval]]))
      as [σ2 [Hσ2 [Hproj_big Heval1]]].
    exists σ2. split; [exact Hσ2|]. split; [|exact Heval1].
    rewrite <- Hproj.
    eapply storeA_restrict_eq_mono; [exact Hsub|exact Hproj_big].
Qed.

Lemma tm_equiv_on_to_fiber_equiv m X e1 e2 :
  tm_equiv_on m e1 e2 ->
  tm_fiber_equiv_on m X e1 e2.
Proof.
  intros Heq σ0 Hσ0 v.
  split; intros [σ [Hσ [Hproj Heval]]].
  - exists σ. split; [exact Hσ|]. split; [exact Hproj|].
    apply (proj1 (Heq σ v Hσ)). exact Heval.
  - exists σ. split; [exact Hσ|]. split; [exact Hproj|].
    apply (proj2 (Heq σ v Hσ)). exact Heval.
Qed.

Lemma tm_fiber_equiv_result_pullback
    (m : WfWorldT) X e_src e_tgt σ_t v :
  tm_fiber_equiv_on m X e_src e_tgt ->
  (m : WorldT) σ_t ->
  tm_eval_in_store σ_t e_tgt v ->
  exists σ_s,
    (m : WorldT) σ_s /\
    store_restrict σ_s X = store_restrict σ_t X /\
    tm_eval_in_store σ_s e_src v.
Proof.
  intros Heq Hσt Heval_t.
  assert (HσX :
      worldA_stores (res_restrict m X : WorldT)
        (store_restrict σ_t X)).
  { exists σ_t. split; [exact Hσt|reflexivity]. }
  assert (Htgt :
      tm_fiber_result_on m X e_tgt (store_restrict σ_t X) v).
  {
    exists σ_t. split; [exact Hσt|].
    split; [reflexivity|exact Heval_t].
  }
  pose proof (Heq (store_restrict σ_t X)
    HσX v) as [_ Hback].
  destruct (Hback Htgt)
    as [σ_s [Hσs [Hproj Heval_s]]].
  exists σ_s. repeat split; assumption.
Qed.

Lemma tm_fiber_equiv_eval_forward
    (m : WfWorldT) X e_src e_tgt σ v :
  fv_tm e_tgt ⊆ X ->
  tm_fiber_equiv_on m X e_src e_tgt ->
  (m : WorldT) σ ->
  tm_eval_in_store σ e_src v ->
  tm_eval_in_store σ e_tgt v.
Proof.
  intros Hfv Heq Hσ Heval_src.
  pose proof (Heq (store_restrict σ X)
    ltac:(exists σ; split; [exact Hσ|reflexivity]) v) as [H12 _].
  destruct (H12 ltac:(exists σ; split; [exact Hσ|split; [reflexivity|exact Heval_src]]))
    as [σ_t [Hσt [Hproj_t Heval_t]]].
  apply (proj2 (tm_eval_in_store_restrict_fv_subset
    σ_t e_tgt v X Hfv)) in Heval_t as Heval_restricted.
  apply (proj1 (tm_eval_in_store_restrict_fv_subset
    σ e_tgt v X Hfv)).
  rewrite <- Hproj_t.
  exact Heval_restricted.
Qed.

Lemma tm_fiber_equiv_result_ext_on
    e x F (m mx : WfWorldT) X :
  fv_tm e ⊆ X ->
  X ⊆ world_dom (m : WorldT) ->
  x ∉ X ->
  expr_result_extension_witness_on X e x F ->
  res_extend_by m F mx ->
  expr_total_on_atom_world e m ->
  wfworld_closed_on ({[x]} : aset) mx ->
  tm_fiber_equiv_on mx X e (tret (vfvar x)).
Proof.
  intros HfvX HXdom HxX HFx Hext Htotal Hclosed_x σ0 Hσ0 v.
  destruct HFx as [HfvX' Hxfresh [Hin Hout] Hrel].
  split.
  - intros [σ [Hσmx [HσX Heval]]].
    apply (proj1 (resA_extend_by_store_iff m F mx σ Hext)) in Hσmx.
    destruct Hσmx as [σm [we [σe [Hσm [HFrel [Hσe ->]]]]]].
    assert (Hσe_dom : dom (σe : StoreT) = {[x]}).
    {
      pose proof (wfworldA_store_dom we σe Hσe) as Hdomσe.
      change (dom (σe : StoreT) = world_dom (we : WorldT)) in Hdomσe.
      rewrite Hdomσe.
      pose proof (extA_rel_dom F (store_restrict σm (ext_in F)) we) as Hdom_we.
      rewrite <- Hout.
      apply Hdom_we; [|exact HFrel].
      rewrite storeA_restrict_dom.
      pose proof (wfworldA_store_dom m σm Hσm) as Hdomσm.
      change (dom (σm : StoreT) = world_dom (m : WorldT)) in Hdomσm.
      denotation_regular_res_extend_input.
      set_solver.
    }
    assert (Heval_base :
        tm_eval_in_store (store_restrict σm (fv_tm e)) e v).
    {
      assert (Hrestrict_e :
          store_restrict ((σm : StoreT) ∪ σe) (fv_tm e) =
          store_restrict σm (fv_tm e)).
      {
        apply storeA_restrict_union_ignore_r.
        change (dom (σe : StoreT) ## fv_tm e).
        rewrite Hσe_dom. set_solver.
      }
      rewrite <- Hrestrict_e.
      exact ((proj2 (tm_eval_in_store_restrict_fv_exact
        ((σm : StoreT) ∪ σe) e v)) Heval).
    }
    assert (Hσm_dom : dom (store_restrict σm (ext_in F) : StoreT) = ext_in F).
    {
      eapply extA_projection_dom.
      - apply resA_extend_by_applicable in Hext. exact Hext.
      - exact Hσm.
    }
    assert (Hout_v : (we : WorldT) ({[x := v]} : StoreT)).
    {
      eapply expr_result_extension_apply_total_store_on.
      - exact {| expr_result_extension_witness_on_fv := HfvX';
                 expr_result_extension_witness_on_fresh := Hxfresh;
                 expr_result_extension_witness_on_shape := conj Hin Hout;
                 expr_result_extension_witness_on_rel := Hrel |}.
      - rewrite <- Hin. exact Hσm_dom.
      - exact HFrel.
      - rewrite Hin.
        apply (proj1 (tm_eval_in_store_restrict_fv_subset
          (store_restrict σm X) e v (fv_tm e) ltac:(set_solver))).
        rewrite (storeA_restrict_twice_subset σm X (fv_tm e) HfvX).
        exact Heval_base.
    }
    set (σv := (σm : StoreT) ∪ ({[x := v]} : StoreT)).
    assert (Hσv_mx : (mx : WorldT) σv).
    {
      apply (proj2 (resA_extend_by_store_iff m F mx σv Hext)).
      exists σm, we, ({[x := v]} : StoreT).
      repeat split; eauto.
    }
    assert (HσvX : store_restrict σv X = σ0).
    {
      transitivity (store_restrict σm X).
      - subst σv. apply store_restrict_union_singleton_ignore_r.
        exact HxX.
      - rewrite <- HσX.
        rewrite storeA_restrict_union_ignore_r; [reflexivity|].
        change (dom (σe : StoreT) ## X).
        rewrite Hσe_dom. set_solver.
    }
    exists σv. split; [exact Hσv_mx|]. split; [exact HσvX|].
    apply (proj1 (tm_eval_in_store_restrict_fv_subset
      σv (tret (vfvar x)) v ({[x]} : aset) ltac:(cbn [fv_tm fv_value]; set_solver))).
    apply tm_eval_in_store_ret_fvar_lookup.
    + exact (Hclosed_x σv Hσv_mx).
    + change ((store_restrict σv ({[x]} : aset) : StoreT) !! x = Some v).
      apply storeA_restrict_lookup_some_2.
      * subst σv.
        transitivity (({[x := v]} : StoreT) !! x).
        -- apply lookup_union_r.
           apply not_elem_of_dom.
           exact (res_extend_by_singleton_output_notin_base_store
             m mx F x σm Hext Hout Hσm).
        -- apply map_lookup_singleton.
      * set_solver.
  - intros [σ [Hσmx [HσX Heval_ret]]].
    pose proof (Hclosed_x σ Hσmx) as Hσx_closed.
    assert (Hret_restrict :
        tm_eval_in_store (store_restrict σ ({[x]} : aset))
          (tret (vfvar x)) v).
    {
      apply (proj2 (tm_eval_in_store_restrict_fv_subset
        σ (tret (vfvar x)) v ({[x]} : aset)
        ltac:(cbn [fv_tm fv_value]; set_solver))).
      exact Heval_ret.
    }
    assert (Hxdomσ : x ∈ dom (σ : StoreT)).
    {
      replace (dom (σ : StoreT)) with (world_dom (mx : WorldT)).
      exact (res_extend_by_singleton_output_in_world m mx F x Hext Hout).
      symmetry. exact (wfworldA_store_dom mx σ Hσmx).
    }
    change (x ∈ dom (σ : gmap atom value)) in Hxdomσ.
    apply elem_of_dom in Hxdomσ as [vx Hxσ].
    assert (Hxlook : store_restrict σ ({[x]} : aset) !! x = Some vx).
    { apply (storeA_restrict_lookup_some_2 _ _ _ _ Hxσ). set_solver. }
    pose proof (tm_eval_in_store_ret_value_inv
      (store_restrict σ ({[x]} : aset)) (vfvar x) v
      Hσx_closed ltac:(constructor) Hret_restrict) as Hv_eq.
    rewrite (msubst_fvar_lookup_closed
      (store_restrict σ ({[x]} : aset)) x vx) in Hv_eq
      by (exact (proj1 Hσx_closed) || exact Hxlook).
    subst vx.
    apply storeA_restrict_lookup_some in Hxlook as [_ Hxlook].
    apply (proj1 (resA_extend_by_store_iff m F mx σ Hext)) in Hσmx.
    destruct Hσmx as [σm [we [σe [Hσm [HFrel [Hσe ->]]]]]].
    assert (Hσe_dom : dom (σe : StoreT) = {[x]}).
    {
      pose proof (wfworldA_store_dom we σe Hσe) as Hdomσe.
      change (dom (σe : StoreT) = world_dom (we : WorldT)) in Hdomσe.
      rewrite Hdomσe.
      pose proof (extA_rel_dom F (store_restrict σm (ext_in F)) we) as Hdom_we.
      rewrite <- Hout.
      apply Hdom_we; [|exact HFrel].
      rewrite storeA_restrict_dom.
      pose proof (wfworldA_store_dom m σm Hσm) as Hdomσm.
      change (dom (σm : StoreT) = world_dom (m : WorldT)) in Hdomσm.
      denotation_regular_res_extend_input.
      set_solver.
    }
    assert (Hσm_dom : dom (store_restrict σm (ext_in F) : StoreT) = ext_in F).
    {
      eapply extA_projection_dom.
      - apply resA_extend_by_applicable in Hext. exact Hext.
      - exact Hσm.
    }
    assert (Htotal_base :
        exists u, tm_eval_in_store (store_restrict σm X) e u).
    {
      destruct Htotal as [_ Htotal_stores].
      assert (Hlift :
          worldA_stores (res_lift_free m : LWorldT)
            (lstore_lift_free σm)).
      { exists σm. split; [exact Hσm|reflexivity]. }
      specialize (Htotal_stores (lstore_lift_free σm) Hlift)
        as Hmust.
      apply must_terminating_reaches_result in Hmust as [u Hu].
      exists u.
      apply (proj2 (tm_eval_in_store_restrict_fv_subset
        σm e u X HfvX)).
      exact Hu.
    }
    assert (Hσm_dom_fv :
        dom (store_restrict σm (ext_in F) : StoreT) = X).
    { rewrite Hσm_dom. exact Hin. }
    pose proof (expr_result_extension_apply_total_iff_on
      X e x F (store_restrict σm (ext_in F)) we
      {| expr_result_extension_witness_on_fv := HfvX';
         expr_result_extension_witness_on_fresh := Hxfresh;
         expr_result_extension_witness_on_shape := conj Hin Hout;
         expr_result_extension_witness_on_rel := Hrel |}
      Hσm_dom_fv HFrel ltac:(rewrite Hin; exact Htotal_base) σe)
      as Hσe_iff.
    apply Hσe_iff in Hσe as [u [Heval_u ->]].
    assert (u = v).
    {
      change ((((σm : StoreT) ∪ ({[x := u]} : StoreT)) : gmap atom value)
        !! x = Some v) in Hxlook.
      assert (Hxσm : x ∉ dom (σm : StoreT)).
      { exact (res_extend_by_singleton_output_notin_base_store
          m mx F x σm Hext Hout Hσm). }
      eapply lookup_union_singleton_r_eq.
      - apply not_elem_of_dom. exact Hxσm.
      - exact Hxlook.
    }
    subst u.
    exists ((σm : StoreT) ∪ ({[x := v]} : StoreT)).
    split.
	    + apply (proj2 (resA_extend_by_store_iff m F mx
	        ((σm : StoreT) ∪ ({[x := v]} : StoreT)) Hext)).
	      exists σm, we, ({[x := v]} : StoreT).
	      split; [exact Hσm|].
	      split; [exact HFrel|].
	      split.
      * eapply expr_result_extension_apply_total_store_on.
        -- exact {| expr_result_extension_witness_on_fv := HfvX';
                    expr_result_extension_witness_on_fresh := Hxfresh;
                    expr_result_extension_witness_on_shape := conj Hin Hout;
                    expr_result_extension_witness_on_rel := Hrel |}.
        -- exact Hσm_dom_fv.
        -- exact HFrel.
        -- exact Heval_u.
	      * reflexivity.
    + split.
      * rewrite <- HσX.
        rewrite !store_restrict_union_singleton_ignore_r by exact HxX.
        reflexivity.
      * change (tm_eval_in_store
          ((σm : StoreT) ∪ ({[x := v]} : StoreT)) e v).
        apply (proj1 (tm_eval_in_store_restrict_fv_subset
          ((σm : StoreT) ∪ ({[x := v]} : StoreT)) e v
          (fv_tm e) ltac:(set_solver))).
        rewrite store_restrict_union_singleton_ignore_r by set_solver.
        rewrite <- (storeA_restrict_twice_subset σm X (fv_tm e) HfvX).
        apply (proj2 (tm_eval_in_store_restrict_fv_subset
          (store_restrict σm X) e v (fv_tm e) ltac:(set_solver))).
        rewrite <- Hin.
        exact Heval_u.
Qed.

Lemma expr_result_formula_msubst_store_to_atom
    (mfib : WfWorldT) D e x σ :
  lc_lvars D ->
  lc_tm e ->
  x ∉ dom (σ : StoreT) ->
  dom (σ : StoreT) = lvars_fv (D ∪ tm_lvars e) ->
  mfib ⊨ formula_msubst_store (store_restrict σ (fv_tm e))
    (expr_result_formula e (LVFree x)) ->
  mfib ⊨ formula_msubst_store σ
    (FAtom (expr_result_qual e (LVFree x))).
Proof.
  intros HlcD Hlc_e Hxσ Hdomσ Hplain.
  rewrite <- (formula_msubst_store_expr_result_formula_restrict σ e x)
    in Hplain by exact Hxσ.
  unfold expr_result_formula, expr_result_formula_at in Hplain.
  rewrite formula_msubst_store_fibvars in Hplain.
  assert (Hempty :
      tm_lvars e ∖ lvars_of_atoms (dom (σ : StoreT)) = ∅).
  {
    rewrite Hdomσ.
    rewrite (tm_lvars_lc_eq_atoms e Hlc_e).
    rewrite lc_lvars_of_atoms_fv_eq.
    - set_solver.
    - intros v Hv.
      apply elem_of_union in Hv as [Hv|Hv].
      + exact (HlcD v Hv).
      + unfold lvars_of_atoms in Hv.
        apply elem_of_map in Hv as [a [-> _]]. exact I.
  }
  rewrite Hempty in Hplain.
  apply res_models_fibvars_empty_elim in Hplain.
  exact Hplain.
Qed.

Lemma typed_fiber_equiv_total_equiv
    Σ τ m e1 e2 :
  typed_fiber_equiv_on Σ τ m e1 e2 ->
  tm_total_equiv_on m e1 e2.
Proof.
  intros Hequiv.
  destruct Hequiv as [_ [Hzero1 Hzero2]].
  pose proof (ty_denote_gas_total_guard_of_zero Σ τ e1 m Hzero1)
    as Htotal1.
  pose proof (ty_denote_gas_total_guard_of_zero Σ τ e2 m Hzero2)
    as Htotal2.
  intros σ Hσ.
  apply expr_total_formula_to_atom_world in Htotal1.
  apply expr_total_formula_to_atom_world in Htotal2.
  destruct Htotal1 as [_ Hstores1].
  destruct Htotal2 as [_ Hstores2].
  assert (Hlift :
      worldA_stores (res_lift_free m : LWorldT) (lstore_lift_free σ)).
  { exists σ. split; [exact Hσ | reflexivity]. }
  split; intros _.
  - exact (Hstores2 (lstore_lift_free σ) Hlift).
  - exact (Hstores1 (lstore_lift_free σ) Hlift).
Qed.

Lemma typed_fiber_equiv_fiber
    Σ τ m e1 e2 :
  typed_fiber_equiv_on Σ τ m e1 e2 ->
  tm_fiber_equiv_on m (lvars_fv (context_ty_lvars τ)) e1 e2.
Proof. intros [Hfib _]. exact Hfib. Qed.

Lemma typed_fiber_equiv_zero_src
    Σ τ m e1 e2 :
  typed_fiber_equiv_on Σ τ m e1 e2 ->
  m ⊨ ty_denote_gas 0 Σ τ e1.
Proof. intros [_ [Hzero _]]. exact Hzero. Qed.

Lemma typed_fiber_equiv_zero_tgt
    Σ τ m e1 e2 :
  typed_fiber_equiv_on Σ τ m e1 e2 ->
  m ⊨ ty_denote_gas 0 Σ τ e2.
Proof. intros [_ [_ Hzero]]. exact Hzero. Qed.

Lemma typed_fiber_equiv_term_lc
    Σ τ m e1 e2 :
  typed_fiber_equiv_on Σ τ m e1 e2 ->
  lc_tm e1 /\ lc_tm e2.
Proof.
  intros Hequiv.
  pose proof (typed_fiber_equiv_zero_src _ _ _ _ _ Hequiv) as Hzero1.
  pose proof (typed_fiber_equiv_zero_tgt _ _ _ _ _ Hequiv) as Hzero2.
  pose proof (ty_denote_gas_guard_of_zero Σ τ e1 m Hzero1) as Hguard1.
  pose proof (ty_denote_gas_guard_of_zero Σ τ e2 m Hzero2) as Hguard2.
  repeat rewrite res_models_and_iff in Hguard1.
  repeat rewrite res_models_and_iff in Hguard2.
  destruct Hguard1 as [_ [_ [Hbasic1 _]]].
  destruct Hguard2 as [_ [_ [Hbasic2 _]]].
  apply expr_basic_typing_formula_models_iff in Hbasic1
    as [HlcΣ1 [_ Hty1]].
  apply expr_basic_typing_formula_models_iff in Hbasic2
    as [HlcΣ2 [_ Hty2]].
  split.
  - eapply basic_tm_has_ltype_lc; [exact HlcΣ1|exact Hty1].
  - eapply basic_tm_has_ltype_lc; [exact HlcΣ2|exact Hty2].
Qed.

Lemma typed_fiber_equiv_term_scope_env
    Σ τ m e1 e2 :
  typed_fiber_equiv_on Σ τ m e1 e2 ->
  fv_tm e1 ∪ fv_tm e2 ⊆ lvars_fv (dom Σ).
Proof.
  intros Hequiv.
  pose proof (typed_fiber_equiv_zero_src _ _ _ _ _ Hequiv) as Hzero1.
  pose proof (typed_fiber_equiv_zero_tgt _ _ _ _ _ Hequiv) as Hzero2.
  pose proof (ty_denote_gas_guard_of_zero Σ τ e1 m Hzero1) as Hguard1.
  pose proof (ty_denote_gas_guard_of_zero Σ τ e2 m Hzero2) as Hguard2.
  repeat rewrite res_models_and_iff in Hguard1.
  repeat rewrite res_models_and_iff in Hguard2.
  destruct Hguard1 as [_ [_ [Hbasic1 _]]].
  destruct Hguard2 as [_ [_ [Hbasic2 _]]].
  apply expr_basic_typing_formula_models_iff in Hbasic1
    as [_ [_ Hty1]].
  apply expr_basic_typing_formula_models_iff in Hbasic2
    as [_ [_ Hty2]].
  pose proof (basic_tm_has_ltype_lvars _ _ _ Hty1) as Hfv1.
  pose proof (basic_tm_has_ltype_lvars _ _ _ Hty2) as Hfv2.
  pose proof (relevant_env_dom_subset_direct Σ τ e1) as Hrel1.
  pose proof (relevant_env_dom_subset_direct Σ τ e2) as Hrel2.
  intros x Hx.
  apply elem_of_union in Hx as [Hx|Hx].
  - apply lvars_fv_elem.
    apply Hrel1.
    apply Hfv1.
    unfold lvars_of_atoms. apply elem_of_map.
    exists x. split; [reflexivity|exact Hx].
  - apply lvars_fv_elem.
    apply Hrel2.
    apply Hfv2.
    unfold lvars_of_atoms. apply elem_of_map.
    exists x. split; [reflexivity|exact Hx].
Qed.

Lemma typed_fiber_equiv_term_lvars_env
    Σ τ m e1 e2 :
  typed_fiber_equiv_on Σ τ m e1 e2 ->
  tm_lvars e1 ∪ tm_lvars e2 ⊆ dom Σ.
Proof.
  intros Hequiv.
  pose proof (typed_fiber_equiv_term_lc _ _ _ _ _ Hequiv)
    as [Hlc1 Hlc2].
  pose proof (typed_fiber_equiv_term_scope_env _ _ _ _ _ Hequiv)
    as Hfv.
  rewrite (tm_lvars_lc_eq_atoms e1 Hlc1).
  rewrite (tm_lvars_lc_eq_atoms e2 Hlc2).
  intros v Hv.
  apply elem_of_union in Hv as [Hv|Hv].
  - unfold lvars_of_atoms in Hv.
    apply elem_of_map in Hv as [x [-> Hx]].
    apply lvars_fv_elem.
    apply Hfv. apply elem_of_union_l. exact Hx.
  - unfold lvars_of_atoms in Hv.
    apply elem_of_map in Hv as [x [-> Hx]].
    apply lvars_fv_elem.
    apply Hfv. apply elem_of_union_r. exact Hx.
Qed.

Lemma tm_total_equiv_of_total_formulas
    (m : WfWorldT) e1 e2 :
  m ⊨ expr_total_formula e1 ->
  m ⊨ expr_total_formula e2 ->
  tm_total_equiv_on m e1 e2.
Proof.
  intros Htotal1 Htotal2 σ Hσ.
  apply expr_total_formula_to_atom_world in Htotal1.
  apply expr_total_formula_to_atom_world in Htotal2.
  destruct Htotal1 as [_ Hstores1].
  destruct Htotal2 as [_ Hstores2].
  assert (Hlift :
      worldA_stores (res_lift_free m : LWorldT) (lstore_lift_free σ)).
  { exists σ. split; [exact Hσ | reflexivity]. }
  split; intros _.
  - exact (Hstores2 (lstore_lift_free σ) Hlift).
  - exact (Hstores1 (lstore_lift_free σ) Hlift).
Qed.

Lemma tm_equiv_lam_app_body
    T e y (m : WfWorldT) :
  wfworld_closed_on
    (fv_tm (tapp_tm (tret (vlam T e)) (vfvar y)) ∪ fv_tm (e ^^ y)) m ->
  body_tm e ->
  y ∉ fv_tm e ->
  y ∈ world_dom (m : WorldT) ->
  tm_equiv_on m
    (tapp_tm (tret (vlam T e)) (vfvar y))
    (e ^^ y).
Proof.
  intros Hclosed Hbody Hy_fresh Hy_dom σ v Hσ.
  set (X := fv_tm (tapp_tm (tret (vlam T e)) (vfvar y)) ∪ fv_tm (e ^^ y)).
  assert (HσX_closed : store_closed (store_restrict σ X)).
  { subst X. eapply wfworld_closed_on_store_restrict_closed; eauto. }
  assert (Hfv_app : fv_tm (tapp_tm (tret (vlam T e)) (vfvar y)) ⊆ X)
    by (subst X; set_solver).
  assert (Hfv_body : fv_tm (e ^^ y) ⊆ X)
    by (subst X; set_solver).
  pose proof (wfworld_store_dom m σ Hσ) as Hσdom.
  assert (Hyσ : y ∈ dom (σ : StoreT)).
  { rewrite <- Hσdom in Hy_dom. exact Hy_dom. }
  destruct (σ !! y) as [vy|] eqn:Hσy.
  2:{ apply not_elem_of_dom in Hσy. set_solver. }
  assert (HyX : y ∈ X).
  {
    subst X. unfold tapp_tm. cbn [fv_tm fv_value].
    set_solver.
  }
  assert (HσXy : store_restrict σ X !! y = Some vy).
  { apply (storeA_restrict_lookup_some_2 _ _ _ _ Hσy HyX). }
  split.
  - intros Happ.
    apply (proj1 (tm_eval_in_store_restrict_fv_subset σ (e ^^ y) v X Hfv_body)).
    apply (proj1 (tm_eval_in_store_tapp_tm_lam_body
      (store_restrict σ X) T e y vy v HσX_closed Hbody Hy_fresh HσXy)).
    apply (proj2 (tm_eval_in_store_restrict_fv_subset
      σ (tapp_tm (tret (vlam T e)) (vfvar y)) v X Hfv_app)).
    exact Happ.
  - intros Hbody_eval.
    apply (proj1 (tm_eval_in_store_restrict_fv_subset
      σ (tapp_tm (tret (vlam T e)) (vfvar y)) v X Hfv_app)).
    apply (proj2 (tm_eval_in_store_tapp_tm_lam_body
      (store_restrict σ X) T e y vy v HσX_closed Hbody Hy_fresh HσXy)).
    apply (proj2 (tm_eval_in_store_restrict_fv_subset
      σ (e ^^ y) v X Hfv_body)).
    exact Hbody_eval.
Qed.

Lemma tm_total_equiv_lam_app_body
    T e y (m : WfWorldT) :
  wfworld_closed_on
    (fv_tm (tapp_tm (tret (vlam T e)) (vfvar y)) ∪ fv_tm (e ^^ y)) m ->
  body_tm e ->
  y ∉ fv_tm e ->
  y ∈ world_dom (m : WorldT) ->
  tm_total_equiv_on m
    (e ^^ y)
    (tapp_tm (tret (vlam T e)) (vfvar y)).
Proof.
  intros Hclosed Hbody Hy_fresh Hy_dom σ Hσ.
  set (X := fv_tm (tapp_tm (tret (vlam T e)) (vfvar y)) ∪ fv_tm (e ^^ y)).
  assert (HσX_closed : store_closed (store_restrict σ X)).
  { subst X. eapply wfworld_closed_on_store_restrict_closed; eauto. }
  assert (Hfv_app : fv_tm (tapp_tm (tret (vlam T e)) (vfvar y)) ⊆ X)
    by (subst X; set_solver).
  assert (Hfv_body : fv_tm (e ^^ y) ⊆ X)
    by (subst X; set_solver).
  pose proof (wfworld_store_dom m σ Hσ) as Hσdom.
  assert (Hyσ : y ∈ dom (σ : StoreT)).
  { rewrite <- Hσdom in Hy_dom. exact Hy_dom. }
  destruct (σ !! y) as [vy|] eqn:Hσy.
  2:{ apply not_elem_of_dom in Hσy. set_solver. }
  assert (HyX : y ∈ X).
  {
    subst X. unfold tapp_tm. cbn [fv_tm fv_value].
    set_solver.
  }
  assert (HσXy : store_restrict σ X !! y = Some vy).
  { apply (storeA_restrict_lookup_some_2 _ _ _ _ Hσy HyX). }
  pose proof (tm_must_terminating_tapp_tm_lam_body
    (store_restrict σ X) T e y vy HσX_closed Hbody Hy_fresh HσXy)
    as HequivX.
  assert (Hlc_body : lc_tm (e ^^ y)).
  { apply body_open_tm; [exact Hbody|constructor]. }
  assert (Hlc_app : lc_tm (tapp_tm (tret (vlam T e)) (vfvar y))).
  {
    apply lc_tapp_tm; [|constructor].
    constructor.
    apply LC_lam with (L := fv_tm e ∪ {[y]}).
    intros z Hz. apply body_open_tm; [exact Hbody|constructor].
  }
  assert (Hbody_agree :
      store_restrict σ (fv_tm (e ^^ y)) =
      store_restrict (store_restrict σ X) (fv_tm (e ^^ y))).
  {
    rewrite storeA_restrict_twice_subset; [reflexivity|exact Hfv_body].
  }
  assert (Happ_agree :
      store_restrict σ (fv_tm (tapp_tm (tret (vlam T e)) (vfvar y))) =
      store_restrict (store_restrict σ X)
        (fv_tm (tapp_tm (tret (vlam T e)) (vfvar y)))).
  {
    rewrite storeA_restrict_twice_subset; [reflexivity|exact Hfv_app].
  }
  pose proof (tm_must_terminating_agree_on_fv σ (store_restrict σ X)
    (e ^^ y) Hlc_body Hbody_agree) as Hbody_restrict.
  pose proof (tm_must_terminating_agree_on_fv σ (store_restrict σ X)
    (tapp_tm (tret (vlam T e)) (vfvar y)) Hlc_app Happ_agree)
    as Happ_restrict.
  split; intros Htotal.
  - apply (proj2 Happ_restrict).
    apply (proj2 HequivX).
    apply (proj1 Hbody_restrict). exact Htotal.
  - apply (proj2 Hbody_restrict).
    apply (proj1 HequivX).
    apply (proj1 Happ_restrict). exact Htotal.
Qed.

Lemma tm_equiv_fix_unfold
    Tf vf y (m : WfWorldT) :
  wfworld_closed_on
    (fv_tm (tapp_tm (tret (vfix Tf vf)) (vfvar y)) ∪
     fv_tm (tapp_tm (tret (open_value 0 (vfvar y) vf)) (vfix Tf vf))) m ->
  body_val vf ->
  y ∈ world_dom (m : WorldT) ->
  tm_equiv_on m
    (tapp_tm (tret (vfix Tf vf)) (vfvar y))
    (tapp_tm (tret (open_value 0 (vfvar y) vf)) (vfix Tf vf)).
Proof.
  intros Hclosed Hbody Hy_dom σ v Hσ.
  set (X := fv_tm (tapp_tm (tret (vfix Tf vf)) (vfvar y)) ∪
            fv_tm (tapp_tm (tret (open_value 0 (vfvar y) vf))
              (vfix Tf vf))).
  assert (HσX_closed : store_closed (store_restrict σ X)).
  { subst X. eapply wfworld_closed_on_store_restrict_closed; eauto. }
  assert (Hfv_src :
      fv_tm (tapp_tm (tret (vfix Tf vf)) (vfvar y)) ⊆ X)
    by (subst X; better_set_solver).
  assert (Hfv_tgt :
      fv_tm (tapp_tm (tret (open_value 0 (vfvar y) vf))
        (vfix Tf vf)) ⊆ X)
    by (subst X; better_set_solver).
  pose proof (wfworld_store_dom m σ Hσ) as Hσdom.
  assert (Hyσ : y ∈ dom (σ : StoreT)).
  { rewrite <- Hσdom in Hy_dom. exact Hy_dom. }
  destruct (σ !! y) as [vy|] eqn:Hσy.
  2:{ apply not_elem_of_dom in Hσy. set_solver. }
  assert (HyX : y ∈ X).
  {
    subst X. unfold tapp_tm. cbn [fv_tm fv_value].
    better_set_solver.
  }
  assert (HσXy : store_restrict σ X !! y = Some vy).
  { apply (storeA_restrict_lookup_some_2 _ _ _ _ Hσy HyX). }
  split.
  - intros Hsrc.
    apply (proj1 (tm_eval_in_store_restrict_fv_subset
      σ (tapp_tm (tret (open_value 0 (vfvar y) vf)) (vfix Tf vf))
      v X Hfv_tgt)).
    apply (proj1 (tm_eval_in_store_tapp_tm_fix_unfold
      (store_restrict σ X) Tf vf y vy v HσX_closed Hbody HσXy)).
    apply (proj2 (tm_eval_in_store_restrict_fv_subset
      σ (tapp_tm (tret (vfix Tf vf)) (vfvar y)) v X Hfv_src)).
    exact Hsrc.
  - intros Htgt.
    apply (proj1 (tm_eval_in_store_restrict_fv_subset
      σ (tapp_tm (tret (vfix Tf vf)) (vfvar y)) v X Hfv_src)).
    apply (proj2 (tm_eval_in_store_tapp_tm_fix_unfold
      (store_restrict σ X) Tf vf y vy v HσX_closed Hbody HσXy)).
    apply (proj2 (tm_eval_in_store_restrict_fv_subset
      σ (tapp_tm (tret (open_value 0 (vfvar y) vf)) (vfix Tf vf))
      v X Hfv_tgt)).
    exact Htgt.
Qed.

Lemma tm_total_equiv_fix_unfold
    Tf vf y (m : WfWorldT) :
  wfworld_closed_on
    (fv_tm (tapp_tm (tret (vfix Tf vf)) (vfvar y)) ∪
     fv_tm (tapp_tm (tret (open_value 0 (vfvar y) vf)) (vfix Tf vf))) m ->
  body_val vf ->
  y ∈ world_dom (m : WorldT) ->
  tm_total_equiv_on m
    (tapp_tm (tret (vfix Tf vf)) (vfvar y))
    (tapp_tm (tret (open_value 0 (vfvar y) vf)) (vfix Tf vf)).
Proof.
  intros Hclosed Hbody Hy_dom σ Hσ.
  set (X := fv_tm (tapp_tm (tret (vfix Tf vf)) (vfvar y)) ∪
            fv_tm (tapp_tm (tret (open_value 0 (vfvar y) vf))
              (vfix Tf vf))).
  assert (HσX_closed : store_closed (store_restrict σ X)).
  { subst X. eapply wfworld_closed_on_store_restrict_closed; eauto. }
  assert (Hfv_src :
      fv_tm (tapp_tm (tret (vfix Tf vf)) (vfvar y)) ⊆ X)
    by (subst X; better_set_solver).
  assert (Hfv_tgt :
      fv_tm (tapp_tm (tret (open_value 0 (vfvar y) vf))
        (vfix Tf vf)) ⊆ X)
    by (subst X; better_set_solver).
  pose proof (wfworld_store_dom m σ Hσ) as Hσdom.
  assert (Hyσ : y ∈ dom (σ : StoreT)).
  { rewrite <- Hσdom in Hy_dom. exact Hy_dom. }
  destruct (σ !! y) as [vy|] eqn:Hσy.
  2:{ apply not_elem_of_dom in Hσy. set_solver. }
  assert (HyX : y ∈ X).
  {
    subst X. unfold tapp_tm. cbn [fv_tm fv_value].
    better_set_solver.
  }
  assert (HσXy : store_restrict σ X !! y = Some vy).
  { apply (storeA_restrict_lookup_some_2 _ _ _ _ Hσy HyX). }
  pose proof (tm_must_terminating_tapp_tm_fix_unfold
    (store_restrict σ X) Tf vf y vy HσX_closed Hbody HσXy)
    as HequivX.
  assert (Hlc_src : lc_tm (tapp_tm (tret (vfix Tf vf)) (vfvar y))).
  {
    apply lc_tapp_tm; [|constructor].
    constructor. apply lc_fix_iff_body. exact Hbody.
  }
  assert (Hlc_tgt :
      lc_tm (tapp_tm (tret (open_value 0 (vfvar y) vf)) (vfix Tf vf))).
  {
    apply lc_tapp_tm.
    - constructor. apply body_open_value; [exact Hbody|constructor].
    - apply lc_fix_iff_body. exact Hbody.
  }
  assert (Hsrc_agree :
      store_restrict σ (fv_tm (tapp_tm (tret (vfix Tf vf)) (vfvar y))) =
      store_restrict (store_restrict σ X)
        (fv_tm (tapp_tm (tret (vfix Tf vf)) (vfvar y)))).
  {
    rewrite storeA_restrict_twice_subset; [reflexivity|exact Hfv_src].
  }
  assert (Htgt_agree :
      store_restrict σ
        (fv_tm (tapp_tm (tret (open_value 0 (vfvar y) vf)) (vfix Tf vf))) =
      store_restrict (store_restrict σ X)
        (fv_tm (tapp_tm (tret (open_value 0 (vfvar y) vf)) (vfix Tf vf)))).
  {
    rewrite storeA_restrict_twice_subset; [reflexivity|exact Hfv_tgt].
  }
  pose proof (tm_must_terminating_agree_on_fv σ (store_restrict σ X)
    (tapp_tm (tret (vfix Tf vf)) (vfvar y)) Hlc_src Hsrc_agree)
    as Hsrc_restrict.
  pose proof (tm_must_terminating_agree_on_fv σ (store_restrict σ X)
    (tapp_tm (tret (open_value 0 (vfvar y) vf)) (vfix Tf vf))
    Hlc_tgt Htgt_agree) as Htgt_restrict.
  split; intros Htotal.
  - apply (proj2 Htgt_restrict).
    apply (proj1 HequivX).
    apply (proj1 Hsrc_restrict). exact Htotal.
  - apply (proj2 Hsrc_restrict).
    apply (proj2 HequivX).
    apply (proj1 Htgt_restrict). exact Htotal.
Qed.

Lemma typed_total_equiv_source_zero
    Σ τ m e1 e2 :
  typed_total_equiv_on Σ τ m e1 e2 ->
  m ⊨ ty_denote_gas 0 Σ τ e1.
Proof. intros [_ [_ [Hzero _]]]. exact Hzero. Qed.

Lemma typed_total_equiv_target_zero
    Σ τ m e1 e2 :
  typed_total_equiv_on Σ τ m e1 e2 ->
  m ⊨ ty_denote_gas 0 Σ τ e2.
Proof. intros [_ [_ [_ Hzero]]]. exact Hzero. Qed.

Lemma typed_total_equiv_tm_equiv
    Σ τ m e1 e2 :
  typed_total_equiv_on Σ τ m e1 e2 ->
  tm_equiv_on m e1 e2.
Proof. intros [Heq _]. exact Heq. Qed.

Lemma typed_total_equiv_total_equiv
    Σ τ m e1 e2 :
  typed_total_equiv_on Σ τ m e1 e2 ->
  tm_total_equiv_on m e1 e2.
Proof. intros [_ [Htotal _]]. exact Htotal. Qed.

Lemma typed_total_equiv_term_lc
    Σ τ m e1 e2 :
  typed_total_equiv_on Σ τ m e1 e2 ->
  lc_tm e1 /\ lc_tm e2.
Proof.
  intros Hequiv.
  pose proof (typed_total_equiv_source_zero _ _ _ _ _ Hequiv) as Hzero1.
  pose proof (typed_total_equiv_target_zero _ _ _ _ _ Hequiv) as Hzero2.
  pose proof (ty_denote_gas_guard_of_zero Σ τ e1 m Hzero1) as Hguard1.
  pose proof (ty_denote_gas_guard_of_zero Σ τ e2 m Hzero2) as Hguard2.
  repeat rewrite res_models_and_iff in Hguard1.
  repeat rewrite res_models_and_iff in Hguard2.
  destruct Hguard1 as [_ [_ [Hbasic1 _]]].
  destruct Hguard2 as [_ [_ [Hbasic2 _]]].
  apply expr_basic_typing_formula_models_iff in Hbasic1
    as [HlcΣ1 [_ Hty1]].
  apply expr_basic_typing_formula_models_iff in Hbasic2
    as [HlcΣ2 [_ Hty2]].
  split.
  - eapply basic_tm_has_ltype_lc; [exact HlcΣ1|exact Hty1].
  - eapply basic_tm_has_ltype_lc; [exact HlcΣ2|exact Hty2].
Qed.

Lemma typed_total_equiv_term_scope
    Σ τ m e1 e2 :
  typed_total_equiv_on Σ τ m e1 e2 ->
  fv_tm e1 ∪ fv_tm e2 ⊆ world_dom (m : WorldT).
Proof.
  intros Hequiv.
  pose proof (typed_total_equiv_source_zero _ _ _ _ _ Hequiv) as Hzero1.
  pose proof (typed_total_equiv_target_zero _ _ _ _ _ Hequiv) as Hzero2.
  pose proof (ty_denote_gas_guard_of_zero Σ τ e1 m Hzero1) as Hguard1.
  pose proof (ty_denote_gas_guard_of_zero Σ τ e2 m Hzero2) as Hguard2.
  repeat rewrite res_models_and_iff in Hguard1.
  repeat rewrite res_models_and_iff in Hguard2.
  destruct Hguard1 as [_ [Hworld1 [Hbasic1 _]]].
  destruct Hguard2 as [_ [Hworld2 [Hbasic2 _]]].
  apply expr_basic_typing_formula_models_iff in Hbasic1
    as [_ [_ Hty1]].
  apply expr_basic_typing_formula_models_iff in Hbasic2
    as [_ [_ Hty2]].
  pose proof (basic_tm_has_ltype_lvars _ _ _ Hty1) as Hfv1.
  pose proof (basic_tm_has_ltype_lvars _ _ _ Hty2) as Hfv2.
  apply basic_world_formula_models_iff in Hworld1 as [_ [Hdom1 _]].
  apply basic_world_formula_models_iff in Hworld2 as [_ [Hdom2 _]].
  intros x Hx.
  apply elem_of_union in Hx as [Hx|Hx].
  - apply Hdom1. apply lvars_fv_elem.
    apply Hfv1. unfold lvars_of_atoms.
    apply elem_of_map. exists x. split; [reflexivity|exact Hx].
  - apply Hdom2. apply lvars_fv_elem.
    apply Hfv2. unfold lvars_of_atoms.
    apply elem_of_map. exists x. split; [reflexivity|exact Hx].
Qed.

Lemma typed_total_equiv_term_lc_lvars
    Σ τ m e1 e2 :
  typed_total_equiv_on Σ τ m e1 e2 ->
  lc_tm e1 /\ lc_tm e2.
Proof.
  apply typed_total_equiv_term_lc.
Qed.

Lemma typed_fiber_equiv_of_tm_equiv
    Σ τ m e1 e2 :
  tm_equiv_on m e1 e2 ->
  m ⊨ ty_denote_gas 0 Σ τ e1 ->
  m ⊨ ty_denote_gas 0 Σ τ e2 ->
  typed_fiber_equiv_on Σ τ m e1 e2.
Proof.
  intros Heq Hzero1 Hzero2.
  apply typed_fiber_equiv_intro.
  - apply tm_equiv_on_to_fiber_equiv. exact Heq.
  - exact Hzero1.
  - exact Hzero2.
Qed.

Lemma tm_equiv_res_store_subset
    (m0 m : WfWorldT) e1 e2 :
  res_subset m0 m ->
  tm_equiv_on m e1 e2 ->
  tm_equiv_on m0 e1 e2.
Proof.
  intros [_ Hstores] Heq σ v Hσ.
  apply Heq. exact (Hstores σ Hσ).
Qed.

Lemma tm_equiv_on_to_fiber_equiv_on
    (m : WfWorldT) (X : aset) e1 e2 :
  tm_equiv_on m e1 e2 ->
  tm_fiber_equiv_on m X e1 e2.
Proof.
  apply tm_equiv_on_to_fiber_equiv.
Qed.

Lemma res_subset_trans_local (m0 m1 m2 : WfWorldT) :
  res_subset m0 m1 ->
  res_subset m1 m2 ->
  res_subset m0 m2.
Proof.
  intros [Hdom01 Hstores01] [Hdom12 Hstores12].
  split; [rewrite Hdom01; exact Hdom12|].
  intros σ Hσ. apply Hstores12. apply Hstores01. exact Hσ.
Qed.


End TypeDenote.

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
