(** * Denotation.TypeEquivTerm

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

Local Lemma store_restrict_union_singleton_ignore_r
    (σ : StoreT) x (v : value) X :
  x ∉ X ->
  store_restrict ((σ : StoreT) ∪ ({[x := v]} : StoreT)) X =
  store_restrict σ X.
Proof.
  intros Hx.
  change ((storeA_restrict
    (@union (gmap atom value) _ (σ : gmap atom value)
      ({[x := v]} : gmap atom value)) X : gmap atom value) =
    storeA_restrict (σ : gmap atom value) X).
  apply storeA_restrict_union_singleton_ignore_r. exact Hx.
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
      pose proof (res_extend_by_input_dom m F mx Hext) as Hin_sub.
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
           pose proof (res_extend_by_output_fresh m F mx Hext) as Hfresh.
	           change (ext_out F ## world_dom (m : WorldT)) in Hfresh.
	           rewrite Hout in Hfresh.
	           pose proof (wfworldA_store_dom m σm Hσm) as Hdomσm.
	           change (dom (σm : StoreT) = world_dom (m : WorldT)) in Hdomσm.
	           change (x ∉ dom (σm : StoreT)).
	           rewrite Hdomσm. set_solver.
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
      pose proof (res_extend_by_dom m F mx Hext) as Hdom_mx.
      change (world_dom (mx : WorldT) =
        world_dom (m : WorldT) ∪ ext_out F) in Hdom_mx.
      rewrite Hdom_mx, Hout. set_solver.
      symmetry. exact (wfworldA_store_dom mx σ Hσmx).
    }
    change (x ∈ dom (σ : gmap atom value)) in Hxdomσ.
    apply elem_of_dom in Hxdomσ as [vx Hxσ].
    assert (Hxlook : store_restrict σ ({[x]} : aset) !! x = Some vx).
    { apply storeA_restrict_lookup_some_2; [exact Hxσ|set_solver]. }
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
      pose proof (res_extend_by_input_dom m F mx Hext) as Hin_sub.
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
      {
        pose proof (res_extend_by_output_fresh m F mx Hext) as Hfresh.
	change (ext_out F ## world_dom (m : WorldT)) in Hfresh.
	rewrite Hout in Hfresh.
	pose proof (wfworldA_store_dom m σm Hσm) as Hdomσm.
	change (dom (σm : StoreT) = world_dom (m : WorldT)) in Hdomσm.
	rewrite Hdomσm. set_solver.
      }
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
  { subst X. apply Hclosed. exact Hσ. }
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
  { apply storeA_restrict_lookup_some_2; [exact Hσy|exact HyX]. }
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
  { subst X. apply Hclosed. exact Hσ. }
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
  { apply storeA_restrict_lookup_some_2; [exact Hσy|exact HyX]. }
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
  { subst X. apply Hclosed. exact Hσ. }
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
  { apply storeA_restrict_lookup_some_2; [exact Hσy|exact HyX]. }
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
  { subst X. apply Hclosed. exact Hσ. }
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
  { apply storeA_restrict_lookup_some_2; [exact Hσy|exact HyX]. }
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
  intros Heq σ0 Hσ0 v.
  split.
  - intros [σ [Hσ [Hproj Heval]]].
    exists σ. split; [exact Hσ|].
    split; [exact Hproj|].
    apply (proj1 (Heq σ v Hσ)). exact Heval.
  - intros [σ [Hσ [Hproj Heval]]].
    exists σ. split; [exact Hσ|].
    split; [exact Hproj|].
    apply (proj2 (Heq σ v Hσ)). exact Heval.
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

Lemma expr_result_formula_transport_fv_subset
    (m : WfWorldT) e1 e2 y :
  lc_tm e1 ->
  tm_equiv_on m e1 e2 ->
  fv_tm e1 ⊆ fv_tm e2 ->
  m ⊨ expr_result_formula e2 (LVFree y) ->
  m ⊨ expr_result_formula e1 (LVFree y).
Proof.
  intros Hlc1 Heq Hfv Hres2.
  pose proof (expr_result_formula_to_atom_world e2 (LVFree y) m Hres2)
    as Hworld2.
  destruct Hworld2 as [Hy2 [Hdom2 Hstores2]].
  apply expr_result_atom_world_to_formula.
  - split.
    + intros Hy1. apply Hy2.
      apply lvars_fv_elem. rewrite tm_lvars_fv.
      apply Hfv. rewrite <- tm_lvars_fv. apply lvars_fv_elem. exact Hy1.
    + split.
      * intros z Hz.
        apply elem_of_union in Hz as [Hz|Hz].
        -- pose proof (tm_lvars_lc_subset_atoms_fv e1
             (tm_lvars_lc e1 Hlc1) _ Hz) as Hzfv.
           unfold lvars_of_atoms in Hzfv.
           apply elem_of_map in Hzfv as [a [-> Ha]].
           apply Hdom2. apply elem_of_union_l.
           apply lvars_fv_elem. rewrite tm_lvars_fv. apply Hfv. exact Ha.
        -- apply Hdom2. apply elem_of_union_r. exact Hz.
      * intros σL HσL.
        destruct HσL as [σ [Hσ ->]].
        specialize (Hstores2 (lstore_lift_free σ)
          ltac:(exists σ; split; [exact Hσ|reflexivity])).
        destruct Hstores2 as [_ [v [Hy_lookup Heval2]]].
        split.
        -- intros Hy1. apply Hy2.
           apply lvars_fv_elem. rewrite tm_lvars_fv.
           apply Hfv. rewrite <- tm_lvars_fv. apply lvars_fv_elem. exact Hy1.
        -- exists v. split; [exact Hy_lookup|].
           change (tm_eval_in_store σ e1 v).
           apply (proj2 (Heq σ v Hσ)).
           change (tm_eval_in_store σ e2 v). exact Heval2.
  - intros z σ v Heq_x Hσ Heval1.
    inversion Heq_x. subst z.
    assert (Heval1_full : tm_eval_in_store σ e1 v).
    {
      apply (proj1 (tm_eval_in_store_restrict_fv_exact σ e1 v)).
      exact Heval1.
    }
    assert (Heval2_full : tm_eval_in_store σ e2 v).
    { apply (proj1 (Heq σ v Hσ)). exact Heval1_full. }
    pose proof (expr_result_formula_fiber_witness e2 y m
      Hres2 σ v Hσ
      ltac:(apply (proj2 (tm_eval_in_store_restrict_fv_exact σ e2 v));
        exact Heval2_full))
      as [σv [Hσv [Hproj2 Hy_lookup]]].
    exists σv. split; [exact Hσv|]. split; [|exact Hy_lookup].
    eapply storeA_restrict_eq_mono.
    + rewrite !tm_lvars_fv. exact Hfv.
		    + rewrite tm_lvars_fv in Hproj2. exact Hproj2.
Qed.

Lemma expr_result_formula_alias_ret_fvar
    (m my : WfWorldT) e x y :
  y ∉ fv_tm e ∪ {[x]} ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_restrict my (world_dom (m : WorldT)) = m ->
  wfworld_closed_on ({[x]} : aset) my ->
  m ⊨ expr_result_formula e (LVFree x) ->
  my ⊨ expr_result_formula (tret (vfvar x)) (LVFree y) ->
  my ⊨ expr_result_formula e (LVFree y).
Proof.
  intros Hyfresh Hdom Hrestrict Hclosed_x Hresx Hretxy.
  pose proof (expr_result_formula_to_atom_world e (LVFree x) m Hresx)
    as Hworld_x.
  pose proof (expr_result_formula_to_atom_world
    (tret (vfvar x)) (LVFree y) my Hretxy) as Hworld_y.
  pose proof (expr_result_formula_models_elim e (LVFree x) m Hresx)
    as [_ [_ Hstore_x]].
  pose proof (expr_result_formula_models_elim
    (tret (vfvar x)) (LVFree y) my Hretxy) as [_ [_ Hstore_y]].
  apply expr_result_atom_world_to_formula.
  - destruct Hworld_x as [Hx_fresh [Hdom_x _]].
    split.
    + intros Hy_lvar.
      apply Hyfresh. apply elem_of_union_l.
      rewrite <- tm_lvars_fv. apply lvars_fv_elem. exact Hy_lvar.
    + split.
      * intros z Hz.
        apply elem_of_union in Hz as [Hz|Hz].
        -- pose proof (Hdom_x z (elem_of_union_l _ _ _ Hz)) as Hz_m.
           rewrite res_lift_free_dom in Hz_m |- *.
           unfold lvars_of_atoms in Hz_m |- *.
	           apply elem_of_map in Hz_m as [a [-> Ha]].
	           apply elem_of_map. exists a. split; [reflexivity|].
	           change (a ∈ world_dom (my : WorldT)).
	           rewrite Hdom. set_solver.
        -- apply elem_of_singleton in Hz as ->.
           rewrite res_lift_free_dom.
	           unfold lvars_of_atoms. apply elem_of_map.
	           exists y. split; [reflexivity|].
	           change (y ∈ world_dom (my : WorldT)).
	           rewrite Hdom. set_solver.
      * intros σL HσL.
        destruct HσL as [σ [Hσ ->]].
        pose proof (Hstore_y σ Hσ) as [_ [vy [Hy_lookup Heval_ret]]].
	        assert (Hx_dom_my : x ∈ world_dom (my : WorldT)).
	        {
	          pose proof (Hdom_x (LVFree x)
	            ltac:(apply elem_of_union_r; set_solver)) as Hx_lift_m.
	          rewrite res_lift_free_dom in Hx_lift_m.
	          unfold lvars_of_atoms in Hx_lift_m.
	          apply elem_of_map in Hx_lift_m as [a [Heq Ha]].
	          inversion Heq. subst a.
	          rewrite Hdom. set_solver.
	        }
	        pose proof (wfworldA_store_dom my σ Hσ) as Hσdom.
	        assert (Hx_dom_σ : x ∈ dom (σ : gmap atom value)).
	        {
	          change (x ∈ dom (σ : gmap atom value)).
	          rewrite Hσdom. exact Hx_dom_my.
	        }
        assert (Hret_restrict :
            tm_eval_in_store (store_restrict (σ : gmap atom value) ({[x]} : aset))
              (tret (vfvar x)) vy).
        {
          apply (proj2 (tm_eval_in_store_restrict_fv_subset
            σ (tret (vfvar x)) vy ({[x]} : aset)
            ltac:(cbn [fv_tm fv_value]; set_solver))).
          change (tm_eval_in_store σ (tret (vfvar x)) vy).
          exact Heval_ret.
        }
	        assert (Hx_dom_restrict :
            x ∈ dom (store_restrict (σ : gmap atom value) ({[x]} : aset) : gmap atom value)).
	        {
	          destruct (σ !! x) as [vx|] eqn:Hx_lookup0.
	          - eapply elem_of_dom_2.
	            eapply storeA_restrict_lookup_some_2;
	              [exact Hx_lookup0|set_solver].
	          - apply not_elem_of_dom in Hx_lookup0. contradiction.
	        }
        pose proof (tm_eval_in_store_ret_fvar_inv
          (store_restrict (σ : gmap atom value) ({[x]} : aset)) x vy
          (Hclosed_x σ Hσ) Hx_dom_restrict Hret_restrict) as Hx_lookup_r.
        apply storeA_restrict_lookup_some in Hx_lookup_r as [_ Hx_lookup].
        assert (Hσm :
            (m : WorldT) (store_restrict (σ : gmap atom value) (world_dom (m : WorldT)))).
        {
          assert (Hr :
              (res_restrict my (world_dom (m : WorldT)) : WorldT)
                (store_restrict (σ : gmap atom value) (world_dom (m : WorldT)))).
          { exists σ. split; [exact Hσ|reflexivity]. }
          rewrite Hrestrict in Hr. exact Hr.
        }
        pose proof (Hstore_x _ Hσm) as [_ [vx [Hx_lookup_m Heval_e_m]]].
	        assert (Hx_in_m : x ∈ world_dom (m : WorldT)).
	        {
	          pose proof (Hdom_x (LVFree x)
	            ltac:(apply elem_of_union_r; set_solver)) as Hx_lift_m.
	          rewrite res_lift_free_dom in Hx_lift_m.
	          unfold lvars_of_atoms in Hx_lift_m.
	          apply elem_of_map in Hx_lift_m as [a [Heq Ha]].
	          inversion Heq. subst a. exact Ha.
	        }
	        assert (Hx_lookup_restrict :
            store_restrict (σ : gmap atom value) (world_dom (m : WorldT)) !! x = Some vy).
	        {
	          apply storeA_restrict_lookup_some_2;
	            [exact Hx_lookup|exact Hx_in_m].
	        }
	        rewrite lstore_lift_free_lookup_free in Hx_lookup_m.
	        rewrite Hx_lookup_m in Hx_lookup_restrict.
        inversion Hx_lookup_restrict. subst vx.
        split.
        -- intros Hy_bad.
           apply Hyfresh. apply elem_of_union_l.
           rewrite <- tm_lvars_fv. apply lvars_fv_elem. exact Hy_bad.
	        -- exists vy. split; [exact Hy_lookup|].
	           assert (Hfv_m : fv_tm e ⊆ world_dom (m : WorldT)).
	           {
	             intros a Ha.
	             assert (Ha_lvar : LVFree a ∈ tm_lvars e).
	             {
	               apply lvars_fv_elem.
	               rewrite tm_lvars_fv. exact Ha.
	             }
	             pose proof (Hdom_x (LVFree a)
	               (elem_of_union_l _ _ _ Ha_lvar)) as Ha_lift_m.
	             rewrite res_lift_free_dom in Ha_lift_m.
	             unfold lvars_of_atoms in Ha_lift_m.
	             apply elem_of_map in Ha_lift_m as [b [Heq Hb]].
	             inversion Heq. subst b. exact Hb.
	           }
	           change (tm_eval_in_store σ e vy).
	           apply (proj1 (tm_eval_in_store_restrict_fv_subset
	             σ e vy (world_dom (m : WorldT)) Hfv_m)).
	           exact Heval_e_m.
  - intros z σ v Heq_z Hσ Heval_e.
    inversion Heq_z. subst z.
    pose proof (expr_result_formula_fiber_witness e x m Hresx
      (store_restrict (σ : gmap atom value) (world_dom (m : WorldT))) v) as Hwit.
    assert (Hσm :
        (m : WorldT) (store_restrict (σ : gmap atom value) (world_dom (m : WorldT)))).
    {
      assert (Hr :
          (res_restrict my (world_dom (m : WorldT)) : WorldT)
            (store_restrict (σ : gmap atom value) (world_dom (m : WorldT)))).
      { exists σ. split; [exact Hσ|reflexivity]. }
      rewrite Hrestrict in Hr. exact Hr.
    }
    assert (Heval_m :
        tm_eval_in_store
          (store_restrict
            (store_restrict (σ : gmap atom value) (world_dom (m : WorldT))) (fv_tm e)) e v).
    {
      rewrite storeA_restrict_twice_subset.
      - exact Heval_e.
      - intros a Ha.
        destruct Hworld_x as [_ [Hdom_x _]].
        pose proof (Hdom_x (LVFree a)
          ltac:(apply elem_of_union_l; apply lvars_fv_elem;
            rewrite tm_lvars_fv; exact Ha)) as Ha_lift_m.
        rewrite res_lift_free_dom in Ha_lift_m.
        unfold lvars_of_atoms in Ha_lift_m.
        apply elem_of_map in Ha_lift_m as [b [Heq Hb]].
        inversion Heq. subst b. exact Hb.
    }
    specialize (Hwit Hσm Heval_m) as [σx [Hσx [Hproj_x Hx_lookup]]].
    assert (Hσx_my :
        (res_restrict my (world_dom (m : WorldT)) : WorldT) σx).
    { rewrite Hrestrict. exact Hσx. }
    destruct Hσx_my as [σxy [Hσxy Hσxy_restrict]].
    pose proof (Hstore_y σxy Hσxy) as [_ [vy [Hy_lookup Heval_ret]]].
	    assert (Hx_dom_my : x ∈ world_dom (my : WorldT)).
	    {
	      pose proof Hworld_x as [_ [Hdom_x _]].
	      pose proof (Hdom_x (LVFree x)
	        ltac:(apply elem_of_union_r; set_solver)) as Hx_lift_m.
	      rewrite res_lift_free_dom in Hx_lift_m.
	      unfold lvars_of_atoms in Hx_lift_m.
	      apply elem_of_map in Hx_lift_m as [a [Heq Ha]].
	      inversion Heq. subst a.
	      rewrite Hdom. set_solver.
	    }
	    pose proof (wfworldA_store_dom my σxy Hσxy) as Hσxy_dom.
	    assert (Hx_dom_σxy : x ∈ dom (σxy : gmap atom value)).
	    {
	      change (x ∈ dom (σxy : gmap atom value)).
	      rewrite Hσxy_dom. exact Hx_dom_my.
	    }
    assert (Hret_restrict :
        tm_eval_in_store (store_restrict (σxy : gmap atom value) ({[x]} : aset))
          (tret (vfvar x)) vy).
    {
      apply (proj2 (tm_eval_in_store_restrict_fv_subset
        σxy (tret (vfvar x)) vy ({[x]} : aset)
        ltac:(cbn [fv_tm fv_value]; set_solver))).
      change (tm_eval_in_store σxy (tret (vfvar x)) vy).
      exact Heval_ret.
    }
    assert (Hx_dom_restrict :
        x ∈ dom (store_restrict (σxy : gmap atom value) ({[x]} : aset) : gmap atom value)).
    {
      destruct (σxy !! x) as [vx|] eqn:Hx_lookup0.
      - eapply elem_of_dom_2.
        eapply storeA_restrict_lookup_some_2;
          [exact Hx_lookup0|set_solver].
      - apply not_elem_of_dom in Hx_lookup0. contradiction.
    }
    pose proof (tm_eval_in_store_ret_fvar_inv
      (store_restrict (σxy : gmap atom value) ({[x]} : aset)) x vy
      (Hclosed_x σxy Hσxy) Hx_dom_restrict Hret_restrict) as Hx_lookup_xy_r.
    apply storeA_restrict_lookup_some in Hx_lookup_xy_r as [_ Hx_lookup_xy].
	    assert (Hx_in_m : x ∈ world_dom (m : WorldT)).
	    {
	      pose proof Hworld_x as [_ [Hdom_x _]].
	      pose proof (Hdom_x (LVFree x)
	        ltac:(apply elem_of_union_r; set_solver)) as Hx_lift_m.
	      rewrite res_lift_free_dom in Hx_lift_m.
	      unfold lvars_of_atoms in Hx_lift_m.
	      apply elem_of_map in Hx_lift_m as [a [Heq Ha]].
	      inversion Heq. subst a. exact Ha.
	    }
    assert (Hx_lookup_xy_restrict :
        store_restrict (σxy : gmap atom value) (world_dom (m : WorldT)) !! x = Some vy).
    {
      apply storeA_restrict_lookup_some_2;
        [exact Hx_lookup_xy|exact Hx_in_m].
    }
    rewrite Hσxy_restrict in Hx_lookup_xy_restrict.
	    rewrite Hx_lookup in Hx_lookup_xy_restrict.
	    inversion Hx_lookup_xy_restrict. subst vy.
	    exists σxy. split; [exact Hσxy|]. split.
		    + transitivity (store_restrict (σx : gmap atom value) (lvars_fv (tm_lvars e))).
	      * symmetry.
	        rewrite <- Hσxy_restrict.
	        apply storeA_restrict_twice_subset.
	        intros a Ha.
	        pose proof Hworld_x as [_ [Hdom_x _]].
	        pose proof (Hdom_x (LVFree a)
	          ltac:(apply elem_of_union_l; apply lvars_fv_elem; exact Ha))
	          as Ha_lift_m.
	        rewrite res_lift_free_dom in Ha_lift_m.
	        unfold lvars_of_atoms in Ha_lift_m.
	        apply elem_of_map in Ha_lift_m as [b [Heq Hb]].
	        inversion Heq. subst b. exact Hb.
	      * transitivity
		          (store_restrict (store_restrict (σ : gmap atom value) (world_dom (m : WorldT)))
	            (lvars_fv (tm_lvars e))).
	        -- exact Hproj_x.
	        -- apply storeA_restrict_twice_subset.
	           intros a Ha.
	           pose proof Hworld_x as [_ [Hdom_x _]].
	           pose proof (Hdom_x (LVFree a)
	             ltac:(apply elem_of_union_l; apply lvars_fv_elem; exact Ha))
	             as Ha_lift_m.
	           rewrite res_lift_free_dom in Ha_lift_m.
	           unfold lvars_of_atoms in Ha_lift_m.
	           apply elem_of_map in Ha_lift_m as [b [Heq Hb]].
	           inversion Heq. subst b. exact Hb.
	    + rewrite lstore_lift_free_lookup_free in Hy_lookup.
		      exact Hy_lookup.
Qed.

Lemma expr_result_extension_fiber_models_result_slot
    e x F (m mx my mfib : WfWorldT) X σ :
  expr_result_extension_witness e x F ->
  res_extend_by m F mx ->
  lc_tm e ->
  expr_total_on_atom_world e m ->
  wfworld_closed_on (fv_tm e) m ->
  x ∉ X ->
  X ∩ world_dom (my : WorldT) ⊆ world_dom (mx : WorldT) ->
  res_restrict my (world_dom (mx : WorldT)) = mx ->
  res_fiber_from_projection my X σ mfib ->
  mfib ⊨ formula_msubst_store (store_restrict σ (fv_tm e))
    (expr_result_formula e (LVFree x)).
Proof.
  intros HF Hext Hlc_e Htotal Hclosed_e HxX HXmy Hrestrict_my Hproj.
  set (σe := store_restrict σ (fv_tm e)).
  assert (HσeD : dom (σe : StoreT) ⊆ lvars_fv (tm_lvars e)).
  {
    subst σe. rewrite tm_lvars_fv.
    apply storeA_restrict_dom_subset.
  }
  assert (Hfixed :
      forall τ, (mfib : WorldT) τ ->
        store_restrict τ (dom (σe : StoreT)) = σe).
  {
    subst σe. intros τ Hτ.
    eapply res_fiber_from_projection_store_restrict_substore; eauto.
  }
  apply (proj1 (res_models_fibvars_msubst_store_fixed
    mfib (tm_lvars e) (FAtom (expr_result_qual e (LVFree x)))
    σe HσeD Hfixed)).
  assert (Hplain : mfib ⊨ expr_result_formula e (LVFree x)).
  2:{ exact Hplain. }
  pose proof (expr_result_extension_world_models_closed
    e x F m mx Hclosed_e HF Hext Htotal) as Hworld_mx.
  apply expr_result_atom_world_to_formula.
  - destruct Hworld_mx as [Hxfresh [Hdom_mx Hstores_mx]].
    split.
    + exact Hxfresh.
    + split.
	      * intros lv Hlv.
	        destruct lv as [k|a].
	        -- exfalso.
	           apply elem_of_union in Hlv as [Hlv|Hlv].
	           ++ rewrite (tm_lvars_lc_eq_atoms e Hlc_e) in Hlv.
	              unfold lvars_of_atoms in Hlv.
	              apply elem_of_map in Hlv as [? [Hbad _]]. discriminate.
	           ++ apply elem_of_singleton in Hlv. discriminate.
	        -- assert (Ha_mx : a ∈ world_dom (mx : WorldT)).
	           {
	             assert (HLV : LVFree a ∈ worldA_dom (res_lift_free mx)).
	             {
	               apply Hdom_mx.
	               apply elem_of_union in Hlv as [Hlv|Hlv].
	               - apply elem_of_union_l. exact Hlv.
	               - apply elem_of_singleton in Hlv as ->.
	                 apply elem_of_union_r. apply elem_of_singleton. reflexivity.
	             }
	             rewrite res_lift_free_dom in HLV.
	             unfold lvars_of_atoms in HLV.
	             apply elem_of_map in HLV as [b [Heq Hb]].
	             inversion Heq. subst b. exact Hb.
	           }
           destruct Hproj as [_ Hfib_eq].
	           change ((mfib : WorldT) = rawA_fiber (my : WorldT) σ) in Hfib_eq.
	           pose proof (f_equal world_dom Hfib_eq) as Hdom_fib.
	           change (world_dom (mfib : WorldT) = world_dom (my : WorldT)) in Hdom_fib.
           rewrite res_lift_free_dom.
           unfold lvars_of_atoms.
           apply elem_of_map. exists a. split; [reflexivity|].
           change (a ∈ world_dom (mfib : WorldT)).
           rewrite Hdom_fib.
           assert (Ha_my : a ∈ world_dom (my : WorldT)).
           {
             assert (Ha_restrict :
                 a ∈ world_dom
                   (res_restrict my (world_dom (mx : WorldT)) : WfWorldT)).
             { rewrite Hrestrict_my. exact Ha_mx. }
             change (a ∈ world_dom
               (res_restrict my (world_dom (mx : WorldT)) : WorldT))
               in Ha_restrict.
             rewrite res_restrict_dom in Ha_restrict.
             set_solver.
           }
           exact Ha_my.
      * intros τL HτL.
        destruct HτL as [τ [Hτ ->]].
        destruct Hproj as [Hproj_src Hfib_eq].
        pose proof (res_fiber_from_projection_store_source
          my mfib X σ τ (conj Hproj_src Hfib_eq) Hτ) as Hτ_my.
        set (τmx := store_restrict τ (world_dom (mx : WorldT))).
        assert (Hτmx_mx : (mx : WorldT) τmx).
        {
          rewrite <- Hrestrict_my.
          subst τmx.
          exists τ. split; [exact Hτ_my|reflexivity].
        }
        specialize (Hstores_mx (lstore_lift_free τmx)
          ltac:(exists τmx; split; [exact Hτmx_mx|reflexivity])).
        destruct Hstores_mx as [Hx_fresh [v [Hxlook Heval]]].
        split; [exact Hx_fresh|].
        exists v. split.
        -- rewrite lstore_lift_free_lookup_free in Hxlook |- *.
           subst τmx.
           change ((store_restrict τ (world_dom (mx : WorldT)) : StoreT) !! x =
             Some v) in Hxlook.
           apply storeA_restrict_lookup_some in Hxlook as [_ Hxlook].
           exact Hxlook.
	        -- eapply tm_eval_in_store_agree_on_fv; [|exact Heval].
	           apply storeA_map_eq. intros a.
	           rewrite !storeA_restrict_lookup.
	           destruct (decide (a ∈ fv_tm e)) as [Ha|Ha]; [|reflexivity].
	           subst τmx.
	           rewrite storeA_restrict_lookup.
	           destruct (decide (a ∈ world_dom (mx : WorldT))) as [_|Hbad];
	             [reflexivity|].
	           exfalso. apply Hbad.
	           assert (HLV : LVFree a ∈ worldA_dom (res_lift_free mx)).
		   {
		     apply Hdom_mx. apply elem_of_union_l.
	             apply lvars_fv_elem. rewrite tm_lvars_fv. exact Ha.
		   }
	           rewrite res_lift_free_dom in HLV.
	           unfold lvars_of_atoms in HLV.
	           apply elem_of_map in HLV as [b [Heq Hb]].
	           inversion Heq. subst b. exact Hb.
  - intros y τ v Heq Hτ Heval.
    inversion Heq. subst y.
    destruct HF as [Hx_fresh [Hin Hout] Hrel].
    destruct Hproj as [Hproj_src Hfib_eq].
    pose proof (res_fiber_from_projection_store_source
      my mfib X σ τ (conj Hproj_src Hfib_eq) Hτ) as Hτ_my.
    set (τmx := store_restrict τ (world_dom (mx : WorldT))).
    assert (Hτmx_mx : (mx : WorldT) τmx).
    {
      rewrite <- Hrestrict_my.
      subst τmx. exists τ. split; [exact Hτ_my|reflexivity].
    }
    apply (proj1 (resA_extend_by_store_iff m F mx τmx Hext)) in Hτmx_mx.
    destruct Hτmx_mx as [τm [we [τe [Hτm [HFrel [Hτe Hτmx_eq]]]]]].
    assert (Hτe_dom : dom (τe : StoreT) = {[x]}).
    {
      pose proof (wfworldA_store_dom we τe Hτe) as Hdomτe.
      change (dom (τe : StoreT) = world_dom (we : WorldT)) in Hdomτe.
      rewrite Hdomτe.
      pose proof (extA_rel_dom F (store_restrict τm (ext_in F)) we) as Hdom_we.
      rewrite <- Hout.
      apply Hdom_we; [|exact HFrel].
      rewrite storeA_restrict_dom.
      pose proof (wfworldA_store_dom m τm Hτm) as Hdomτm.
      change (dom (τm : StoreT) = world_dom (m : WorldT)) in Hdomτm.
      pose proof (res_extend_by_input_dom m F mx Hext) as Hin_sub.
      set_solver.
    }
    assert (Heval_m :
        tm_eval_in_store (store_restrict τm (fv_tm e)) e v).
    {
      assert (Hτ_agree :
          store_restrict τ (fv_tm e) =
          store_restrict τm (fv_tm e)).
	      {
	        subst τmx.
	        rewrite <- (storeA_restrict_twice_subset τ
	          (world_dom (mx : WorldT)) (fv_tm e)).
	        2:{
	          pose proof (res_extend_by_input_dom m F mx Hext) as Hin_sub.
	          pose proof (res_extend_by_dom m F mx Hext) as Hdom_mx_ext.
	          rewrite <- Hin, Hdom_mx_ext.
	          set_solver.
	        }
		        rewrite Hτmx_eq.
	        apply storeA_map_eq. intros a.
	        rewrite !storeA_restrict_lookup.
	        destruct (decide (a ∈ fv_tm e)) as [Ha|Ha]; [|reflexivity].
	        change ((((τm : StoreT) ∪ τe) : gmap atom value) !! a =
	          (τm : StoreT) !! a).
	        destruct ((τm : StoreT) !! a) eqn:Hτma.
	        - change ((((τm : StoreT) : gmap atom value) ∪
	              ((τe : StoreT) : gmap atom value)) !! a = Some v0).
	          transitivity (((τm : StoreT) : gmap atom value) !! a).
	          + apply lookup_union_l'. exists v0. exact Hτma.
	          + exact Hτma.
	        - apply (proj2 (map_lookup_union_None
	            (τm : StoreT) τe a)).
	          split; [exact Hτma|].
	          apply not_elem_of_dom_1.
	          change (a ∉ dom (τe : StoreT)).
	          rewrite Hτe_dom. set_solver.
	      }
      rewrite <- Hτ_agree.
      exact Heval.
    }
    assert (Hτm_dom_fv :
        dom (store_restrict τm (ext_in F) : StoreT) = ext_in F).
    {
      eapply extA_projection_dom.
      - apply resA_extend_by_applicable in Hext. exact Hext.
      - exact Hτm.
    }
    assert (Hwe_v : (we : WorldT) ({[x := v]} : StoreT)).
    {
      eapply expr_result_extension_apply_total_store.
	      - exact {| expr_result_extension_witness_fresh := Hx_fresh;
	                 expr_result_extension_witness_shape := conj Hin Hout;
	                 expr_result_extension_witness_rel := Hrel |}.
	      - rewrite <- Hin. exact Hτm_dom_fv.
      - exact HFrel.
      - rewrite Hin. exact Heval_m.
    }
    set (τmxv := (τm : StoreT) ∪ ({[x := v]} : StoreT)).
    assert (Hτmxv_mx : (mx : WorldT) τmxv).
    {
      apply (proj2 (resA_extend_by_store_iff m F mx τmxv Hext)).
      exists τm, we, ({[x := v]} : StoreT).
      split; [exact Hτm|]. split; [exact HFrel|].
      split; [exact Hwe_v|reflexivity].
    }
    assert (Hτmxv_X :
        store_restrict τmxv (X ∩ world_dom (mx : WorldT)) =
        store_restrict τ (X ∩ world_dom (mx : WorldT))).
	    {
	      subst τmxv.
	      apply storeA_map_eq. intros a.
	      rewrite !storeA_restrict_lookup.
	      destruct (decide (a ∈ X ∩ world_dom (mx : WorldT))) as [Ha|Ha];
	        [|reflexivity].
	      apply elem_of_intersection in Ha as [HaX Hamx].
	      assert (Hτ_lookup :
	          τ !! a = (((τm : StoreT) ∪ τe) : StoreT) !! a).
	      {
	        pose proof (f_equal (fun s : StoreT => s !! a) Hτmx_eq)
	          as Htmp.
	        subst τmx.
	        change ((store_restrict τ (world_dom (mx : WorldT)) : StoreT) !! a =
	          (((τm : StoreT) ∪ τe) : StoreT) !! a) in Htmp.
	        transitivity ((store_restrict τ (world_dom (mx : WorldT)) : StoreT) !! a).
	        - destruct (τ !! a) eqn:Hτa.
	          + symmetry. apply storeA_restrict_lookup_some_2; [exact Hτa|exact Hamx].
	          + exfalso.
	            assert (Ha_my : a ∈ world_dom (my : WorldT)).
	            {
	              assert (Ha_restrict :
	                  a ∈ world_dom
	                    (res_restrict my (world_dom (mx : WorldT)) : WfWorldT)).
	              { rewrite Hrestrict_my. exact Hamx. }
	              change (a ∈ world_dom
	                (res_restrict my (world_dom (mx : WorldT)) : WorldT))
	                in Ha_restrict.
	              rewrite res_restrict_dom in Ha_restrict.
	              set_solver.
	            }
		            pose proof (wfworld_store_dom my τ Hτ_my) as Hdomτ.
		            change (dom (τ : StoreT) = world_dom (my : WorldT)) in Hdomτ.
		            assert (a ∈ dom (τ : StoreT)) by (rewrite Hdomτ; exact Ha_my).
		            change (a ∈ dom (τ : gmap atom value)) in H.
		            apply elem_of_dom in H as [? Hlook].
		            rewrite Hτa in Hlook. discriminate.
	        - exact Htmp.
	      }
	      assert (Hax : a <> x) by set_solver.
      change ((((τm : StoreT) ∪ ({[x := v]} : StoreT)) : gmap atom value) !! a =
        ((τ : StoreT) : gmap atom value) !! a).
      rewrite Hτ_lookup.
      change ((((τm : StoreT) ∪ ({[x := v]} : StoreT)) : gmap atom value) !! a =
        (((τm : StoreT) ∪ τe) : gmap atom value) !! a).
	      destruct ((τm : StoreT) !! a) eqn:Hτma.
	      - transitivity ((τm : StoreT) !! a).
	        + apply lookup_union_l'. exists v0. exact Hτma.
	        + symmetry. apply lookup_union_l'. exists v0. exact Hτma.
	      - transitivity (@None value).
	        + apply (proj2 (map_lookup_union_None
	            (τm : StoreT) ({[x := v]} : StoreT) a)).
	          split.
	          * exact Hτma.
	          * change ((({[x := v]} : gmap atom value) !! a) = None).
	            apply lookup_singleton_ne. congruence.
	        + symmetry. apply (proj2 (map_lookup_union_None
	            (τm : StoreT) τe a)). split.
	          * exact Hτma.
	          * apply not_elem_of_dom_1.
            change (a ∉ dom (τe : StoreT)).
            rewrite Hτe_dom. set_solver.
    }
	    assert (Hτmxv_in_restrict :
	        (res_restrict my (world_dom (mx : WorldT)) : WorldT) τmxv).
	    { rewrite Hrestrict_my. exact Hτmxv_mx. }
	    change ((rawA_restrict (my : WorldT) (world_dom (mx : WorldT))) τmxv)
	      in Hτmxv_in_restrict.
	    cbn [rawA_restrict worldA_stores] in Hτmxv_in_restrict.
	    destruct Hτmxv_in_restrict as [τv [Hτv_my Hτv_restrict]].
	    exists τv.
	    split.
	    + subst τmxv.
	        assert (Hτv_X : store_restrict τv X = σ).
        {
	          apply storeA_map_eq. intros a.
	          rewrite !storeA_restrict_lookup.
	          destruct (decide (a ∈ X)) as [HaX|HaX]; [|].
	          2:{
	            destruct (σ !! a) eqn:Hσa; [|reflexivity].
	            exfalso. apply HaX.
	            pose proof (wfworld_store_dom (res_restrict my X) σ Hproj_src)
	              as Hdomσ.
	            change (dom (σ : StoreT) =
	              world_dom (res_restrict my X : WorldT)) in Hdomσ.
	            rewrite res_restrict_dom in Hdomσ.
	            assert (a ∈ dom (σ : StoreT)).
	            {
	              change (a ∈ dom (σ : gmap atom value)).
	              rewrite elem_of_dom. eauto.
	            }
	            rewrite Hdomσ in H. set_solver.
	          }
	          destruct (decide (a ∈ world_dom (my : WorldT))) as [Ha_my|Ha_not_my].
		          2:{
		            assert (Hτv_none : τv !! a = None).
		            {
		              destruct (τv !! a) eqn:Hτva; [|reflexivity].
		              exfalso. apply Ha_not_my.
		              pose proof (wfworld_store_dom my τv Hτv_my) as Hdomτv.
		              change (dom (τv : StoreT) = world_dom (my : WorldT))
		                in Hdomτv.
		              rewrite <- Hdomτv.
		              change (a ∈ dom (τv : gmap atom value)).
		              rewrite elem_of_dom. eauto.
		            }
	            assert (Hσ_none : σ !! a = None).
	            {
	              apply not_elem_of_dom_1.
	              change (a ∉ dom (σ : StoreT)).
	              pose proof (wfworld_store_dom (res_restrict my X) σ Hproj_src)
	                as Hdomσ.
	              change (dom (σ : StoreT) =
	                world_dom (res_restrict my X : WorldT)) in Hdomσ.
		              rewrite Hdomσ, res_restrict_dom.
		              set_solver.
		            }
		            change ((τv : StoreT) !! a = (σ : StoreT) !! a).
		            transitivity (@None value); [exact Hτv_none|].
		            symmetry. exact Hσ_none.
		          }
	          assert (Ha_mx : a ∈ world_dom (mx : WorldT)).
	          { apply HXmy. apply elem_of_intersection. split; [exact HaX|exact Ha_my]. }
	          assert (Hv_lookup :
	              τv !! a =
	              (((τm : StoreT) ∪ ({[x := v]} : StoreT)) : StoreT) !! a).
	          {
	            pose proof (f_equal (fun s : StoreT => s !! a) Hτv_restrict)
	              as Hv_restrict.
	            change ((store_restrict τv (world_dom (mx : WorldT)) : StoreT) !! a =
	              (((τm : StoreT) ∪ ({[x := v]} : StoreT)) : StoreT) !! a)
	              in Hv_restrict.
	            transitivity ((store_restrict τv (world_dom (mx : WorldT)) : StoreT) !! a).
	            - destruct (τv !! a) eqn:Hτva.
	              + symmetry. apply storeA_restrict_lookup_some_2;
	                  [exact Hτva|exact Ha_mx].
	              + exfalso.
	                pose proof (wfworld_store_dom my τv Hτv_my) as Hdomτv.
	                change (dom (τv : StoreT) = world_dom (my : WorldT))
	                  in Hdomτv.
	                assert (a ∈ dom (τv : StoreT)) by
	                  (rewrite Hdomτv; exact Ha_my).
	                change (a ∈ dom (τv : gmap atom value)) in H.
	                apply elem_of_dom in H as [? Hlook].
	                rewrite Hτva in Hlook. discriminate.
		            - exact Hv_restrict.
		          }
	          change ((τv : StoreT) !! a = (σ : StoreT) !! a).
	          transitivity
	            ((((τm : StoreT) ∪ ({[x := v]} : StoreT)) : StoreT) !! a).
	          { exact Hv_lookup. }
	          assert (Hmxv_lookup :
	              (((τm : StoreT) ∪ ({[x := v]} : StoreT)) : StoreT) !! a =
	              τ !! a).
	          {
	            pose proof (f_equal (fun s : StoreT => s !! a) Hτmxv_X)
	              as Hmxv.
	            change ((store_restrict
	              (((τm : StoreT) ∪ ({[x := v]} : StoreT)) : StoreT)
	              (X ∩ world_dom (mx : WorldT)) : StoreT) !! a =
	              (store_restrict τ (X ∩ world_dom (mx : WorldT)) : StoreT) !! a)
	              in Hmxv.
		            transitivity ((store_restrict
		              (((τm : StoreT) ∪ ({[x := v]} : StoreT)) : StoreT)
		              (X ∩ world_dom (mx : WorldT)) : StoreT) !! a).
		            - destruct ((((τm : StoreT) ∪ ({[x := v]} : StoreT)) : StoreT) !! a)
		                eqn:Hlook.
		              + symmetry. apply storeA_restrict_lookup_some_2.
		                * exact Hlook.
		                * apply elem_of_intersection. split; [exact HaX|exact Ha_mx].
		              + exfalso.
		                pose proof (wfworld_store_dom mx
		                  (((τm : StoreT) ∪ ({[x := v]} : StoreT)) : StoreT)
		                  Hτmxv_mx) as Hdommxv.
		                change (dom ((((τm : StoreT) ∪ ({[x := v]} : StoreT)) : StoreT)) =
		                  world_dom (mx : WorldT)) in Hdommxv.
			                assert (a ∈ dom (((τm : StoreT) ∪ ({[x := v]} : StoreT)) : StoreT))
		                  by (rewrite Hdommxv; exact Ha_mx).
			                change (a ∈ dom (((τm : StoreT) : gmap atom value) ∪
			                  (({[x := v]} : StoreT) : gmap atom value))) in H.
			                apply elem_of_dom in H as [? Hbad].
			                change ((((τm : StoreT) : gmap atom value) ∪
			                  (({[x := v]} : StoreT) : gmap atom value)) !! a = None)
			                  in Hlook.
			                rewrite Hlook in Hbad. discriminate.
	            - transitivity ((store_restrict τ
	                (X ∩ world_dom (mx : WorldT)) : StoreT) !! a).
	              + exact Hmxv.
	              + destruct (τ !! a) eqn:Hτa.
	                * apply storeA_restrict_lookup_some_2.
	                  -- exact Hτa.
	                  -- apply elem_of_intersection. split; [exact HaX|exact Ha_mx].
	                * exfalso.
	                  pose proof (wfworld_store_dom my τ Hτ_my) as Hdomτ.
	                  change (dom (τ : StoreT) = world_dom (my : WorldT)) in Hdomτ.
	                  assert (a ∈ dom (τ : StoreT)) by
	                    (rewrite Hdomτ; exact Ha_my).
	                  change (a ∈ dom (τ : gmap atom value)) in H.
	                  apply elem_of_dom in H as [? Hbad].
	                  rewrite Hτa in Hbad. discriminate.
	          }
		          rewrite Hmxv_lookup.
		          pose proof (res_fiber_from_projection_store_restrict
		            my mfib X σ τ (conj Hproj_src Hfib_eq) Hτ) as Hτfix.
	          assert (Haσ : a ∈ dom (σ : StoreT)).
	          {
	            pose proof (wfworld_store_dom (res_restrict my X) σ Hproj_src)
	              as Hdomσ.
	            change (dom (σ : StoreT) =
	              world_dom (res_restrict my X : WorldT)) in Hdomσ.
	            rewrite Hdomσ, res_restrict_dom.
	            set_solver.
	          }
	          pose proof (f_equal (fun s : StoreT => s !! a) Hτfix) as Hfixa.
	          change ((store_restrict τ (dom (σ : StoreT)) : StoreT) !! a =
	            σ !! a) in Hfixa.
	          transitivity ((store_restrict τ (dom (σ : StoreT)) : StoreT) !! a).
	          -- destruct (τ !! a) eqn:Hτa.
	             ++ symmetry. apply storeA_restrict_lookup_some_2;
	                  [exact Hτa|exact Haσ].
	             ++ exfalso.
	                pose proof (wfworld_store_dom my τ Hτ_my) as Hdomτ.
	                change (dom (τ : StoreT) = world_dom (my : WorldT)) in Hdomτ.
	                assert (a ∈ dom (τ : StoreT)) by
	                  (rewrite Hdomτ; exact Ha_my).
	                change (a ∈ dom (τ : gmap atom value)) in H.
	                apply elem_of_dom in H as [? Hbad].
	                rewrite Hτa in Hbad. discriminate.
	          -- exact Hfixa.
	        }
	        change ((mfib : WorldT) = rawA_fiber (my : WorldT) σ) in Hfib_eq.
	        rewrite Hfib_eq.
	        split; [exact Hτv_my|].
	        eapply storeA_restrict_projection_dom.
	        exact Hτv_X.
	    + split.
	      * apply storeA_map_eq. intros a.
	        rewrite !storeA_restrict_lookup.
	        destruct (decide (a ∈ lvars_fv (tm_lvars e))) as [Ha|Ha];
	          [|reflexivity].
	        assert (Ha_fv : a ∈ fv_tm e) by (rewrite <- tm_lvars_fv; exact Ha).
	        assert (Ha_mx : a ∈ world_dom (mx : WorldT)).
	        {
		          pose proof (res_extend_by_input_dom m F mx Hext) as Hin_sub.
		          pose proof (res_extend_by_dom m F mx Hext) as Hdom_mx_ext.
		          rewrite Hdom_mx_ext.
		          set_solver.
	        }
	        assert (Hv_lookup :
	            τv !! a =
	            (((τm : StoreT) ∪ ({[x := v]} : StoreT)) : StoreT) !! a).
	        {
	          pose proof (f_equal (fun s : StoreT => s !! a) Hτv_restrict)
	            as Htmp.
	          change ((store_restrict τv (world_dom (mx : WorldT)) : StoreT) !! a =
	            (((τm : StoreT) ∪ ({[x := v]} : StoreT)) : StoreT) !! a)
	            in Htmp.
	          transitivity ((store_restrict τv (world_dom (mx : WorldT)) : StoreT) !! a).
	          - destruct (τv !! a) eqn:Hτva.
	            + symmetry. apply storeA_restrict_lookup_some_2;
	                [exact Hτva|exact Ha_mx].
	            + exfalso.
	              pose proof (wfworld_store_dom my τv Hτv_my) as Hdomτv.
	              change (dom (τv : StoreT) = world_dom (my : WorldT)) in Hdomτv.
	              assert (a ∈ world_dom (my : WorldT)).
	              {
	                assert (Ha_restrict :
	                    a ∈ world_dom
	                      (res_restrict my (world_dom (mx : WorldT)) : WfWorldT)).
	                { rewrite Hrestrict_my. exact Ha_mx. }
	                change (a ∈ world_dom
	                  (res_restrict my (world_dom (mx : WorldT)) : WorldT))
	                  in Ha_restrict.
	                rewrite res_restrict_dom in Ha_restrict.
	                set_solver.
	              }
	              assert (a ∈ dom (τv : StoreT)) by (rewrite Hdomτv; exact H).
	              change (a ∈ dom (τv : gmap atom value)) in H0.
	              apply elem_of_dom in H0 as [? Hbad].
	              rewrite Hτva in Hbad. discriminate.
	          - exact Htmp.
	        }
	        assert (Hτ_lookup :
	            τ !! a = (((τm : StoreT) ∪ τe) : StoreT) !! a).
	        {
	          pose proof (f_equal (fun s : StoreT => s !! a) Hτmx_eq) as Htmp.
	          subst τmx.
	          change ((store_restrict τ (world_dom (mx : WorldT)) : StoreT) !! a =
	            (((τm : StoreT) ∪ τe) : StoreT) !! a) in Htmp.
	          transitivity ((store_restrict τ (world_dom (mx : WorldT)) : StoreT) !! a).
	          - destruct (τ !! a) eqn:Hτa.
	            + symmetry. apply storeA_restrict_lookup_some_2;
	                [exact Hτa|exact Ha_mx].
	            + exfalso.
	              pose proof (wfworld_store_dom my τ Hτ_my) as Hdomτ.
	              change (dom (τ : StoreT) = world_dom (my : WorldT)) in Hdomτ.
	              assert (a ∈ world_dom (my : WorldT)).
	              {
	                assert (Ha_restrict :
	                    a ∈ world_dom
	                      (res_restrict my (world_dom (mx : WorldT)) : WfWorldT)).
	                { rewrite Hrestrict_my. exact Ha_mx. }
	                change (a ∈ world_dom
	                  (res_restrict my (world_dom (mx : WorldT)) : WorldT))
	                  in Ha_restrict.
	                rewrite res_restrict_dom in Ha_restrict.
	                set_solver.
	              }
	              assert (a ∈ dom (τ : StoreT)) by (rewrite Hdomτ; exact H).
	              change (a ∈ dom (τ : gmap atom value)) in H0.
	              apply elem_of_dom in H0 as [? Hbad].
	              rewrite Hτa in Hbad. discriminate.
	          - exact Htmp.
	        }
		        change ((τv : StoreT) !! a = (τ : StoreT) !! a).
		        transitivity
		          ((((τm : StoreT) ∪ ({[x := v]} : StoreT)) : StoreT) !! a).
		        { exact Hv_lookup. }
		        transitivity ((((τm : StoreT) ∪ τe) : StoreT) !! a).
		        2:{ symmetry. exact Hτ_lookup. }
		        assert (Hax_fv : a <> x) by set_solver.
	        change ((((τm : StoreT) ∪ ({[x := v]} : StoreT)) : gmap atom value) !! a =
	          (((τm : StoreT) ∪ τe) : gmap atom value) !! a).
	        destruct ((τm : StoreT) !! a) eqn:Hτma.
	        -- transitivity ((τm : StoreT) !! a).
	           ++ apply lookup_union_l'. exists v0. exact Hτma.
	           ++ symmetry. apply lookup_union_l'. exists v0. exact Hτma.
	        -- transitivity (@None value).
	           ++ apply (proj2 (map_lookup_union_None
	                (τm : StoreT) ({[x := v]} : StoreT) a)).
	              split; [exact Hτma|].
	              change ((({[x := v]} : gmap atom value) !! a) = None).
	              apply lookup_singleton_ne. congruence.
	           ++ symmetry. apply (proj2 (map_lookup_union_None
	                (τm : StoreT) τe a)). split; [exact Hτma|].
	              apply not_elem_of_dom_1.
	              change (a ∉ dom (τe : StoreT)).
	              rewrite Hτe_dom. set_solver.
	      * subst τmxv.
	        pose proof (f_equal (fun s : StoreT => s !! x) Hτv_restrict) as Hxlook.
	        assert (Hx_mx : x ∈ world_dom (mx : WorldT)).
	        {
	          pose proof (res_extend_by_dom m F mx Hext) as Hdom_mx.
	          rewrite Hdom_mx. set_solver.
	        }
	        change ((store_restrict τv (world_dom (mx : WorldT)) : StoreT) !! x =
	          (((τm : StoreT) ∪ ({[x := v]} : StoreT)) : StoreT) !! x)
	          in Hxlook.
	        transitivity
	          ((((τm : StoreT) ∪ ({[x := v]} : StoreT)) : StoreT) !! x).
	        2:{
	        change ((((τm : StoreT) ∪ ({[x := v]} : StoreT)) : gmap atom value)
	          !! x = Some v).
	        apply map_lookup_union_Some_raw. right.
	        split.
	        - apply not_elem_of_dom_1.
	           pose proof (res_extend_by_output_fresh m F mx Hext) as Hfresh.
	           change (ext_out F ## world_dom (m : WorldT)) in Hfresh.
	           rewrite Hout in Hfresh.
	           pose proof (wfworldA_store_dom m τm Hτm) as Hdomτm.
	           change (dom (τm : StoreT) = world_dom (m : WorldT)) in Hdomτm.
	           change (x ∉ dom (τm : StoreT)). rewrite Hdomτm. set_solver.
	        - change ((({[x := v]} : gmap atom value) !! x) = Some v).
		           apply map_lookup_singleton.
		        }
		        destruct (τv !! x) eqn:Hτvx.
		        { transitivity
		            ((store_restrict τv (world_dom (mx : WorldT)) : StoreT) !! x).
		          - symmetry. apply storeA_restrict_lookup_some_2;
		              [exact Hτvx|exact Hx_mx].
		          - exact Hxlook.
		        }
		        { exfalso.
		          pose proof (wfworld_store_dom my τv Hτv_my) as Hdomτv.
		          change (dom (τv : StoreT) = world_dom (my : WorldT)) in Hdomτv.
		          assert (x ∈ world_dom (my : WorldT)).
	          {
	            assert (Hx_restrict :
	                x ∈ world_dom
	                  (res_restrict my (world_dom (mx : WorldT)) : WfWorldT)).
	            { rewrite Hrestrict_my. exact Hx_mx. }
	            change (x ∈ world_dom
	              (res_restrict my (world_dom (mx : WorldT)) : WorldT))
	              in Hx_restrict.
	            rewrite res_restrict_dom in Hx_restrict.
	            set_solver.
	          }
	          assert (x ∈ dom (τv : StoreT)) by (rewrite Hdomτv; exact H).
		          change (x ∈ dom (τv : gmap atom value)) in H0.
		          apply elem_of_dom in H0 as [? Hbad].
		          rewrite Hτvx in Hbad. discriminate.
		        }
Qed.

Lemma expr_result_formula_at_of_result_extends
    D e x F (m mx : WfWorldT) :
  lc_lvars D ->
  lc_tm e ->
  lvars_fv D ⊆ world_dom (m : WorldT) ->
  fv_tm e ⊆ world_dom (m : WorldT) ->
  x ∉ lvars_fv D ∪ fv_tm e ->
  expr_result_extension_witness e x F ->
  res_extend_by m F mx ->
  expr_total_on_atom_world e m ->
  wfworld_closed_on (fv_tm e) m ->
  mx ⊨ expr_result_formula_at (D ∪ tm_lvars e) e (LVFree x).
Proof.
  intros HlcD Hlc_e HDm Hfv_m HxD HF Hext Htotal Hclosed.
  apply res_models_FFibVars_intro.
  - unfold formula_scoped_in_world.
    change (formula_fv (expr_result_formula_at (D ∪ tm_lvars e) e (LVFree x)) ⊆
      world_dom (mx : WorldT)).
    rewrite formula_fv_expr_result_formula_at.
    intros a Ha.
    pose proof (res_extend_by_dom m F mx Hext) as Hdom_mx.
    destruct HF as [_ [Hin Hout] _].
    rewrite Hdom_mx.
    change (extA_out F) with (ext_out F).
    rewrite Hout.
    rewrite lvars_fv_union in Ha.
    apply elem_of_union in Ha as [HaD|HaQ].
    + apply elem_of_union in HaD as [HaD|HaE].
      * apply elem_of_union_l. exact (HDm a HaD).
      * apply elem_of_union_l. apply Hfv_m.
        rewrite <- tm_lvars_fv. exact HaE.
    + rewrite lvars_fv_union in HaQ.
      apply elem_of_union in HaQ as [HaE|Hax].
      * apply elem_of_union_l. apply Hfv_m.
        rewrite <- tm_lvars_fv. exact HaE.
      * apply elem_of_union_r.
        rewrite <- lvars_fv_singleton_free. exact Hax.
  - intros v Hv.
    apply elem_of_union in Hv as [Hv|Hv].
    + exact (HlcD v Hv).
    + exact (tm_lvars_lc e Hlc_e v Hv).
  - intros σ mfib Hproj.
    assert (HlcDe : lc_lvars (D ∪ tm_lvars e)).
    {
      intros v Hv.
      apply elem_of_union in Hv as [Hv|Hv].
      - exact (HlcD v Hv).
      - exact (tm_lvars_lc e Hlc_e v Hv).
    }
    assert (HXmx :
        lvars_fv (D ∪ tm_lvars e) ⊆ world_dom (mx : WorldT)).
    {
      intros a Ha.
      pose proof (res_extend_by_dom m F mx Hext) as Hdom_mx.
      rewrite Hdom_mx.
      apply elem_of_union_l.
      rewrite lvars_fv_union in Ha.
      apply elem_of_union in Ha as [Ha|Ha].
      - exact (HDm a Ha).
      - apply Hfv_m. rewrite <- tm_lvars_fv. exact Ha.
    }
    destruct Hproj as [Hproj_store Hfib_eq].
    pose proof (wfworld_store_dom
      (res_restrict mx (lvars_fv (D ∪ tm_lvars e))) σ Hproj_store)
      as Hdomσ.
    change (dom (σ : StoreT) =
      world_dom (res_restrict mx (lvars_fv (D ∪ tm_lvars e)) : WorldT))
      in Hdomσ.
    rewrite res_restrict_dom in Hdomσ.
    assert (Hdomσ_eq : dom (σ : StoreT) = lvars_fv (D ∪ tm_lvars e)).
    {
      rewrite Hdomσ.
      apply set_eq. intros a. split.
      - intros Ha. apply elem_of_intersection in Ha as [_ Ha]. exact Ha.
      - intros Ha. apply elem_of_intersection. split; [exact (HXmx a Ha)|exact Ha].
    }
    assert (Hxσ : x ∉ dom (σ : StoreT)).
    {
      rewrite Hdomσ_eq. intros Hx.
      apply HxD.
      rewrite lvars_fv_union in Hx.
      apply elem_of_union in Hx as [Hx|Hx].
      - apply elem_of_union_l. exact Hx.
      - apply elem_of_union_r. rewrite <- tm_lvars_fv. exact Hx.
    }
    pose proof (expr_result_extension_fiber_models_result_slot
      e x F m mx mx mfib
      (lvars_fv (D ∪ tm_lvars e)) σ
      HF Hext Hlc_e Htotal Hclosed
      ltac:(rewrite ?lvars_fv_union;
        rewrite (tm_lvars_lc_eq_atoms e Hlc_e);
        rewrite ?lvars_fv_of_atoms; set_solver)
      ltac:(set_solver)
      ltac:(apply res_restrict_eq_of_le; apply raw_le_refl)
      (conj Hproj_store Hfib_eq)) as Hplain.
    eapply (expr_result_formula_msubst_store_to_atom
      mfib D e x σ).
    + exact HlcD.
    + exact Hlc_e.
    + exact Hxσ.
    + exact Hdomσ_eq.
    + exact Hplain.
Qed.

Lemma expr_result_formula_msubst_alias_ret_fvar
    (m : WfWorldT) e x y σ :
  y ∉ fv_tm e ∪ {[x]} ->
  x ∉ dom (σ : StoreT) ->
  y ∉ dom (σ : StoreT) ->
  wfworld_closed_on ({[x]} : aset) m ->
  (forall τ, (m : WorldT) τ ->
    store_restrict τ (dom (store_restrict σ (fv_tm e) : StoreT)) =
      store_restrict σ (fv_tm e)) ->
  m ⊨ formula_msubst_store σ (expr_result_formula e (LVFree x)) ->
  m ⊨ expr_result_formula (tret (vfvar x)) (LVFree y) ->
  m ⊨ formula_msubst_store σ (expr_result_formula e (LVFree y)).
Proof.
  intros Hyfresh Hxσ Hyσ Hclosed_x Hfixed Hresx Hret.
  rewrite formula_msubst_store_expr_result_formula_restrict in Hresx
    by exact Hxσ.
  rewrite formula_msubst_store_expr_result_formula_restrict
    by exact Hyσ.
  set (σe := store_restrict σ (fv_tm e)).
  assert (HσeD : dom (σe : StoreT) ⊆ lvars_fv (tm_lvars e)).
  {
    subst σe. rewrite tm_lvars_fv.
    apply storeA_restrict_dom_subset.
  }
  pose proof (res_models_fibvars_msubst_store_fixed
    m (tm_lvars e) (FAtom (expr_result_qual e (LVFree x))) σe
    HσeD Hfixed) as Hiffx.
  pose proof (res_models_fibvars_msubst_store_fixed
    m (tm_lvars e) (FAtom (expr_result_qual e (LVFree y))) σe
    HσeD Hfixed) as Hiffy.
  change (expr_result_formula e (LVFree x))
    with (FFibVars (tm_lvars e) (FAtom (expr_result_qual e (LVFree x))))
    in Hresx.
  change (expr_result_formula e (LVFree y))
    with (FFibVars (tm_lvars e) (FAtom (expr_result_qual e (LVFree y)))).
  apply Hiffy.
  assert (Hplainx : m ⊨ expr_result_formula e (LVFree x)).
  { apply Hiffx. exact Hresx. }
  pose proof (expr_result_formula_to_atom_world e (LVFree x) m Hplainx)
    as Hworld_x.
  pose proof (expr_result_formula_to_atom_world
    (tret (vfvar x)) (LVFree y) m Hret) as Hworld_y.
  pose proof (expr_result_formula_models_elim e (LVFree x) m Hplainx)
    as [_ [_ Hstore_x]].
  pose proof (expr_result_formula_models_elim
    (tret (vfvar x)) (LVFree y) m Hret) as [_ [_ Hstore_y]].
  apply expr_result_atom_world_to_formula.
  - destruct Hworld_x as [Hx_fresh [Hdom_x _]].
    destruct Hworld_y as [Hy_fresh [Hdom_y _]].
    split.
    + intros Hy_lvar.
      apply Hyfresh. apply elem_of_union_l.
      rewrite <- tm_lvars_fv. apply lvars_fv_elem. exact Hy_lvar.
    + split.
      * intros z Hz.
        apply elem_of_union in Hz as [Hz|Hz].
        -- apply Hdom_x. apply elem_of_union_l. exact Hz.
        -- apply elem_of_singleton in Hz as ->.
           apply Hdom_y. apply elem_of_union_r. apply elem_of_singleton. reflexivity.
      * intros τL HτL.
        destruct HτL as [τ [Hτ ->]].
        specialize (Hstore_x τ Hτ) as [Hx_fresh_store [v [Hxlook Heval]]].
	        specialize (Hstore_y τ Hτ) as [_ [vy [Hylook Heval_ret]]].
	        split.
	        -- intros Hbad. apply Hyfresh.
	           apply elem_of_union_l.
	           rewrite <- tm_lvars_fv. apply lvars_fv_elem. exact Hbad.
        -- exists v. split.
	           ++ transitivity (Some vy).
              ** exact Hylook.
	              ** assert (Heval_ret_full :
	                    tm_eval_in_store τ (tret (vfvar x)) vy).
	                 {
	                   change (tm_eval_in_store τ (tret (vfvar x)) vy).
	                   exact Heval_ret.
	                 }
	                 assert (Heval_ret_restrict :
	                     tm_eval_in_store (store_restrict τ ({[x]} : aset))
	                       (tret (vfvar x)) vy).
	                 {
	                   apply (proj2 (tm_eval_in_store_restrict_fv_subset
	                     τ (tret (vfvar x)) vy ({[x]} : aset)
	                     ltac:(cbn [fv_tm fv_value]; set_solver))).
	                   exact Heval_ret_full.
	                 }
	                 pose proof (tm_eval_in_store_ret_fvar_inv
	                   (store_restrict τ ({[x]} : aset)) x vy
	                   (Hclosed_x τ Hτ)
	                   ltac:(change (x ∈ dom
	                     (store_restrict τ ({[x]} : aset) : gmap atom value));
		                     rewrite elem_of_dom; eexists;
		                     apply storeA_restrict_lookup_some_2;
	                     [rewrite <- lstore_lift_free_lookup_free; exact Hxlook
	                     |set_solver])
		                   Heval_ret_restrict) as Hxvy.
	                 apply storeA_restrict_lookup_some in Hxvy as [_ Hxvy].
		                 assert (Hxlook_atom : τ !! x = Some v).
		                 { rewrite <- lstore_lift_free_lookup_free. exact Hxlook. }
	                 change ((τ : StoreT) !! x = Some vy) in Hxvy.
	                 pose proof (eq_trans (eq_sym Hxvy) Hxlook_atom) as HeqSome.
	                 inversion HeqSome.
		                 reflexivity.
           ++ exact Heval.
  - intros z τ v Heq Hτ Heval.
    inversion Heq. subst z.
    pose proof (expr_result_formula_fiber_witness e x m Hplainx
      τ v Hτ Heval) as [τv [Hτv [Hproj Hxlook]]].
    specialize (Hstore_y τv Hτv) as [_ [vy [Hylook Heval_ret]]].
	    exists τv. split; [exact Hτv|]. split; [exact Hproj|].
	    transitivity (Some vy).
	    + rewrite <- lstore_lift_free_lookup_free. exact Hylook.
	    + assert (Heval_ret_full :
	          tm_eval_in_store τv (tret (vfvar x)) vy).
	      {
	        change (tm_eval_in_store τv (tret (vfvar x)) vy).
	        exact Heval_ret.
	      }
	      assert (Heval_ret_restrict :
	          tm_eval_in_store (store_restrict τv ({[x]} : aset))
	            (tret (vfvar x)) vy).
	      {
	        apply (proj2 (tm_eval_in_store_restrict_fv_subset
	          τv (tret (vfvar x)) vy ({[x]} : aset)
	          ltac:(cbn [fv_tm fv_value]; set_solver))).
	        exact Heval_ret_full.
	      }
	      pose proof (tm_eval_in_store_ret_fvar_inv
	        (store_restrict τv ({[x]} : aset)) x vy
	        (Hclosed_x τv Hτv)
	        ltac:(change (x ∈ dom
	          (store_restrict τv ({[x]} : aset) : gmap atom value));
	          rewrite elem_of_dom; eexists;
	          apply storeA_restrict_lookup_some_2;
	          [exact Hxlook|set_solver])
		        Heval_ret_restrict) as Hxvy.
	      apply storeA_restrict_lookup_some in Hxvy as [_ Hxvy].
	      change ((τv : StoreT) !! x = Some vy) in Hxvy.
	      pose proof (eq_trans (eq_sym Hxvy) Hxlook) as HeqSome.
	      inversion HeqSome.
	      reflexivity.
Qed.

Lemma expr_result_extension_open_fiber_alias
    e x F (m mx : WfWorldT) (φ : qualifier (V := value)) :
  expr_result_extension_witness e x F ->
  res_extend_by m F mx ->
  expr_total_on_atom_world e m ->
  lc_tm e ->
  wfworld_closed_on (fv_tm e) m ->
  x ∉ lvars_fv (qual_vars φ) ->
  wfworld_closed_on ({[x]} : aset) mx ->
  ∃ L : aset,
    forall y : atom, y ∉ L ->
      forall my : WfWorldT,
        world_dom (my : WorldT) = world_dom (mx : WorldT) ∪ {[y]} ->
        res_restrict my (world_dom (mx : WorldT)) = mx ->
      forall σ mfib,
        res_fiber_from_projection my
          (lvars_fv (lvars_open 0 y (qual_vars φ ∖ {[LVBound 0]}))) σ mfib ->
        mfib ⊨ formula_msubst_store σ
          (formula_open 0 y
            (expr_result_formula
              (tm_shift 0 (tret (vfvar x))) (LVBound 0))) ->
        mfib ⊨ formula_msubst_store σ
          (formula_open 0 y
            (expr_result_formula (tm_shift 0 e) (LVBound 0))).
Proof.
  intros HF Hext Htotal Hlc_e Hclosed_e Hxφ Hclosed_x.
  exists (world_dom (mx : WorldT) ∪ fv_tm e ∪ lvars_fv (qual_vars φ)).
  intros y Hy my Hdom_my Hrestrict_my σ mfib Hproj Hret.
  assert (Hy_e : y ∉ fv_tm e) by set_solver.
  assert (Hy_x : y <> x).
  {
    intros ->. apply Hy.
    pose proof (res_extend_by_dom m F mx Hext) as Hmx_dom.
    destruct HF as [_ [_ Hout] _].
    unfold ext_out in Hout.
    rewrite Hmx_dom, Hout. set_solver.
  }
  assert (Hyφ : y ∉ lvars_fv (qual_vars φ)) by set_solver.
  assert (Hopen_dom :
      lvars_fv (lvars_open 0 y (qual_vars φ ∖ {[LVBound 0]})) ⊆
      lvars_fv (qual_vars φ)).
  {
    intros a Ha.
    rewrite lvars_open_fresh_index in Ha.
    - eapply lvars_fv_mono; [|exact Ha].
      intros v Hv. apply elem_of_difference in Hv as [Hv _]. exact Hv.
    - intros Hbad.
      rewrite lvars_bv_elem in Hbad.
      apply elem_of_difference in Hbad as [_ Hbad].
      apply Hbad. apply elem_of_singleton. reflexivity.
    - intros Hbad. apply Hyφ.
      eapply lvars_fv_mono; [|exact Hbad].
      intros v Hv. apply elem_of_difference in Hv as [Hv _]. exact Hv.
  }
  assert (Hx_proj :
      x ∉ lvars_fv (lvars_open 0 y (qual_vars φ ∖ {[LVBound 0]}))).
  { intros Hbad. apply Hxφ. apply Hopen_dom. exact Hbad. }
  assert (Hy_proj :
      y ∉ lvars_fv (lvars_open 0 y (qual_vars φ ∖ {[LVBound 0]}))).
  { intros Hbad. apply Hyφ. apply Hopen_dom. exact Hbad. }
  assert (Hxσ : x ∉ dom (σ : StoreT)).
  {
    intros Hbad.
    apply res_fiber_from_projection_store_dom_subset in Hproj.
    exact (Hx_proj (Hproj _ Hbad)).
  }
  assert (Hyσ : y ∉ dom (σ : StoreT)).
  {
    intros Hbad.
    apply res_fiber_from_projection_store_dom_subset in Hproj.
    exact (Hy_proj (Hproj _ Hbad)).
  }
  assert (Hy_ret_x : y ∉ fv_tm (tret (vfvar x))).
  { cbn [fv_tm fv_value]. set_solver. }
  rewrite formula_msubst_store_expr_result_formula_shift0 in Hret by
    (try (apply lc_ret_iff_value; apply LC_fvar);
     try exact Hy_ret_x; exact Hyσ).
  cbn [tm_shift] in Hret.
  rewrite formula_msubst_store_expr_result_formula_restrict in Hret by exact Hyσ.
  replace (store_restrict σ (fv_tm (tret (vfvar x))) : StoreT)
    with (∅ : StoreT) in Hret.
  2:{
    apply storeA_map_eq. intros a.
    cbn [fv_tm fv_value].
    rewrite storeA_restrict_lookup.
    destruct (decide (a ∈ {[x]})) as [Ha|Ha]; [|reflexivity].
    apply elem_of_singleton in Ha. subst a.
    destruct (σ !! x) as [vx|] eqn:Hxlook; [|reflexivity].
    exfalso. apply Hxσ.
    change (x ∈ dom (σ : gmap atom value)).
    rewrite elem_of_dom. eauto.
  }
  rewrite formula_msubst_store_empty in Hret by reflexivity.
  rewrite formula_msubst_store_expr_result_formula_shift0 by
    (try exact Hlc_e; try exact Hy_e; exact Hyσ).
  rewrite formula_msubst_store_expr_result_formula_restrict by exact Hyσ.
  eapply expr_result_formula_msubst_alias_ret_fvar.
  - intros Hy_bad.
    apply elem_of_union in Hy_bad as [Hy_bad|Hy_bad].
    + exact (Hy_e Hy_bad).
    + apply elem_of_singleton in Hy_bad. exact (Hy_x Hy_bad).
	  - intros Hbad. apply Hxσ.
	    change (x ∈ dom (store_restrict σ (fv_tm e) : gmap atom value)) in Hbad.
	    rewrite elem_of_dom in Hbad.
	    destruct Hbad as [vx Hlook].
	    apply storeA_restrict_lookup_some in Hlook as [_ Hlook].
	    change (x ∈ dom (σ : gmap atom value)).
	    rewrite elem_of_dom. eauto.
	  - intros Hbad. apply Hyσ.
	    change (y ∈ dom (store_restrict σ (fv_tm e) : gmap atom value)) in Hbad.
	    rewrite elem_of_dom in Hbad.
	    destruct Hbad as [vy Hlook].
	    apply storeA_restrict_lookup_some in Hlook as [_ Hlook].
	    change (y ∈ dom (σ : gmap atom value)).
	    rewrite elem_of_dom. eauto.
  - intros τ Hτ.
    pose proof (res_fiber_from_projection_store_source
      my mfib (lvars_fv (lvars_open 0 y (qual_vars φ ∖ {[LVBound 0]})))
      σ τ Hproj Hτ) as Hτ_my.
	    assert (Hτmx : (mx : WorldT)
	        (store_restrict τ (world_dom (mx : WorldT)))).
	    {
	      assert (Hr :
	          (res_restrict my (world_dom (mx : WorldT)) : WorldT)
	            (store_restrict τ (world_dom (mx : WorldT)))).
	      {
	        change ((rawA_restrict (my : WorldT) (world_dom (mx : WorldT)))
	          (store_restrict τ (world_dom (mx : WorldT)))).
	        cbn [rawA_restrict worldA_stores].
	        exists τ. split; [exact Hτ_my|reflexivity].
	      }
	      rewrite Hrestrict_my in Hr. exact Hr.
	    }
	    specialize (Hclosed_x _ Hτmx).
	    rewrite <- (storeA_restrict_twice_subset τ (world_dom (mx : WorldT))
	      ({[x]} : aset)) by
	      (pose proof (res_extend_by_dom m F mx Hext) as Hdom_mx;
	      destruct HF as [_ [_ Hout] _];
	      rewrite Hdom_mx; set_solver).
	    exact Hclosed_x.
  - intros τ Hτ.
    pose proof (res_fiber_from_projection_store_restrict_substore
      my mfib
      (lvars_fv (lvars_open 0 y (qual_vars φ ∖ {[LVBound 0]})))
      (fv_tm e) σ τ Hproj Hτ) as Hfix.
    replace (dom ((store_restrict (store_restrict σ (fv_tm e)) (fv_tm e)) : StoreT))
      with (dom (store_restrict σ (fv_tm e) : StoreT)).
    2:{
      rewrite storeA_restrict_twice_subset by set_solver.
      reflexivity.
    }
    rewrite storeA_restrict_twice_subset by set_solver.
    exact Hfix.
  - eapply (expr_result_extension_fiber_models_result_slot
      e x F m mx my mfib
      (lvars_fv (lvars_open 0 y (qual_vars φ ∖ {[LVBound 0]}))) σ);
      eauto.
    intros a Ha.
    apply elem_of_intersection in Ha as [HaX Hamy].
    rewrite Hdom_my in Hamy.
    apply elem_of_union in Hamy as [Hamx|Hay].
    * exact Hamx.
    * apply elem_of_singleton in Hay. subst a.
      exfalso. exact (Hy_proj HaX).
  - exact Hret.
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
  { cbn [fv_tm]. set_solver. }
  pose proof Hlc_tlet as Hlc_tlet_parts.
  apply lc_lete_iff_body in Hlc_tlet_parts as [_ Hbody_e2].
  split.
  - intros [σ [Hσmx [HσX He2x]]].
    assert (Hclosedσ : store_closed (store_restrict σ (fv_tm (tlete e1 e2)))).
    { exact (Hclosed_tlet σ Hσmx). }
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
    assert (Hzσ : z ∉ dom (σ : StoreT)) by set_solver.
    assert (Hze1 : z ∉ fv_tm e1) by set_solver.
    assert (Hze2 : z ∉ fv_tm e2) by set_solver.
    assert (Hz_ne_x : z <> x) by set_solver.
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
      - pose proof (open_fv_tm e2 (vfvar z) 0) as Hopen.
        cbn [fv_value] in Hopen. set_solver.
      - exact Hzσ.
      - cbn [fv_tm]. set_solver.
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
          cbn [fv_tm]. set_solver.
      }
      apply (proj1 (tm_eval_in_store_agree_on_fv
        (store_restrict σ (fv_tm e1))
        (store_restrict σ (fv_tm (tlete e1 e2))) e1 vx Hagree_e1)).
      exact He1.
    }
    exists σ. split; [exact Hσmx|]. split; [exact HσX|].
    eapply tm_eval_in_store_tlete_intro_closed_on; eauto;
      try set_solver; try exact He1_tlet.
  - intros [σ [Hσmx [HσX Hlet]]].
    assert (Hclosedσ : store_closed (store_restrict σ (fv_tm (tlete e1 e2)))).
    { exact (Hclosed_tlet σ Hσmx). }
    set (z := fresh_for (dom (σ : StoreT) ∪ fv_tm e1 ∪ fv_tm e2 ∪ X ∪ {[x]})).
    assert (Hzfresh :
        z ∉ dom (σ : StoreT) ∪ fv_tm e1 ∪ fv_tm e2 ∪ X ∪ {[x]})
      by (subst z; apply fresh_for_not_in).
    assert (Hze2 : z ∉ fv_tm e2) by set_solver.
    assert (Hztlet : z ∉ fv_tm (tlete e1 e2)).
    { cbn [fv_tm]. set_solver. }
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
      rewrite storeA_restrict_dom.
      pose proof (wfworldA_store_dom m σm Hσm) as Hdomσm.
      change (dom (σm : StoreT) = world_dom (m : WorldT)) in Hdomσm.
      pose proof (res_extend_by_input_dom m Fx mx Hext) as Hin_sub.
      set_solver.
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
        rewrite Hσe_dom. set_solver.
      }
      apply (proj1 (tm_eval_in_store_agree_on_fv
        (store_restrict ((σm : StoreT) ∪ σe) (fv_tm e1))
        (store_restrict σm (fv_tm e1)) e1 vx Hagree_e1)).
      exact He1.
    }
    assert (Hσm_dom_fv :
        dom (store_restrict σm (fv_tm e1) : StoreT) = fv_tm e1).
    {
      change (dom (storeA_restrict σm (fv_tm e1) : gmap atom value) =
        fv_tm e1).
      rewrite storeA_restrict_dom.
      pose proof (res_extend_by_input_dom m Fx mx Hext) as Hin_sub.
      pose proof (wfworldA_store_dom m σm Hσm) as Hσm_dom.
      change (dom (σm : StoreT) = world_dom (m : WorldT)) in Hσm_dom.
      apply set_eq. intros a.
      rewrite elem_of_intersection.
      unfold ext_in in Hin. rewrite <- Hin.
      set_solver.
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
        rewrite Hdom_single. set_solver.
      - symmetry.
        apply storeA_restrict_union_ignore_r.
        change (dom (σe : StoreT) ## X).
        rewrite Hσe_dom. set_solver.
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
        apply elem_of_dom_2 in Hlook. set_solver.
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
        { pose proof (open_fv_tm e2 (vfvar z) 0 a Ha) as Hopen.
          cbn [fv_value] in Hopen. exact Hopen. }
        assert (Hax : a <> x) by set_solver.
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
	          2:{ exfalso. cbn [fv_tm] in Ha_tlet. set_solver. }
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
	                rewrite Hσe_dom. set_solver.
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
	        unfold σx.
	        intros Hzdom.
	        change (z ∈ dom
	          ((((σm : StoreT) : gmap atom value) ∪
	            ({[x := vx]} : gmap atom value)) : gmap atom value)) in Hzdom.
	        apply elem_of_dom in Hzdom as [vz Hlook].
	        apply map_lookup_union_Some_raw in Hlook as [Hlook|[_ Hlook]].
		        - assert (Hzold : z ∈ dom ((σm : StoreT) ∪ σe : StoreT)).
		          {
		            change (z ∈ dom
		              ((((σm : StoreT) : gmap atom value) ∪
		                ((σe : StoreT) : gmap atom value)) : gmap atom value)).
		            rewrite elem_of_dom. exists vz.
		            apply map_lookup_union_Some_raw. left. exact Hlook.
		          }
		          apply Hzfresh. set_solver.
		        - destruct (decide (z = x)) as [->|Hzx].
		          + apply Hzfresh. set_solver.
		          + assert (Hzin_single :
		                z ∈ dom (({[x := vx]} : gmap atom value))).
		            {
		              rewrite elem_of_dom. exists vz.
		              change ((({[x := vx]} : gmap atom value) !! z) = Some vz).
		              exact Hlook.
		            }
		            pose proof (dom_singleton_L (M:=gmap atom) x vx) as Hdom_single.
		            change (dom (({[x := vx]} : gmap atom value)) = {[x]})
		              in Hdom_single.
		            rewrite Hdom_single in Hzin_single. set_solver.
	      }
	      apply (proj2 (tm_eval_in_store_open_alias e2 σx x z vx v
	        Hx_lookup_σx Hzσx
	        Hxe2 Hze2 Hscope_x)).
	      exact He2z_full.
	    }
    exists σx. split; [exact Hσx_mx|]. split; [exact HσxX|exact He2x].
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
  { subst X. apply Hclosed. exact Hσ. }
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
    { apply Hclosed. exact Hσ. }
    assert (Hfv_app1 : fv_tm (tapp_tm e1 (vfvar y)) ⊆ X) by set_solver.
    assert (Hfv_app2 : fv_tm (tapp_tm e2 (vfvar y)) ⊆ X) by set_solver.
    assert (Hfun_equiv :
        forall vf,
          tm_eval_in_store (store_restrict σ X) e1 vf <->
          tm_eval_in_store (store_restrict σ X) e2 vf).
    {
      intros vf. split; intros Heval_fun.
      - assert (Hres1 : tm_fiber_result_on m X e1 σ0 vf).
        { exists σ. split; [exact Hσ|]. split; [exact HσX|].
          apply (proj1 (tm_eval_in_store_restrict_fv_subset
            σ e1 vf X ltac:(cbn [fv_tm fv_value] in HfvX; set_solver))).
          exact Heval_fun. }
        destruct (proj1 (Heq σ0 Hσ0 vf) Hres1)
          as [σ2 [Hσ2 [Hσ2X Heval2]]].
        assert (Hσ_eq : store_restrict σ X = store_restrict σ2 X).
        { rewrite HσX, Hσ2X. reflexivity. }
        apply (proj2 (tm_eval_in_store_restrict_fv_subset
            σ e2 vf X ltac:(cbn [fv_tm fv_value] in HfvX; set_solver))).
        eapply tm_eval_in_store_agree_on_fv.
        2: exact Heval2.
        eapply storeA_restrict_eq_mono; [|exact Hσ_eq].
        cbn [fv_tm fv_value] in HfvX. set_solver.
      - assert (Hres2 : tm_fiber_result_on m X e2 σ0 vf).
        { exists σ. split; [exact Hσ|]. split; [exact HσX|].
          apply (proj1 (tm_eval_in_store_restrict_fv_subset
            σ e2 vf X ltac:(cbn [fv_tm fv_value] in HfvX; set_solver))).
          exact Heval_fun. }
        destruct (proj2 (Heq σ0 Hσ0 vf) Hres2)
          as [σ1 [Hσ1 [Hσ1X Heval1]]].
        assert (Hσ_eq : store_restrict σ X = store_restrict σ1 X).
        { rewrite HσX, Hσ1X. reflexivity. }
        apply (proj2 (tm_eval_in_store_restrict_fv_subset
            σ e1 vf X ltac:(cbn [fv_tm fv_value] in HfvX; set_solver))).
        eapply tm_eval_in_store_agree_on_fv.
        2: exact Heval1.
        eapply storeA_restrict_eq_mono; [|exact Hσ_eq].
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
    { apply Hclosed. exact Hσ. }
    assert (Hfv_app1 : fv_tm (tapp_tm e1 (vfvar y)) ⊆ X) by set_solver.
    assert (Hfv_app2 : fv_tm (tapp_tm e2 (vfvar y)) ⊆ X) by set_solver.
    assert (Hfun_equiv :
        forall vf,
          tm_eval_in_store (store_restrict σ X) e1 vf <->
          tm_eval_in_store (store_restrict σ X) e2 vf).
    {
      intros vf. split; intros Heval_fun.
      - assert (Hres1 : tm_fiber_result_on m X e1 σ0 vf).
        { exists σ. split; [exact Hσ|]. split; [exact HσX|].
          apply (proj1 (tm_eval_in_store_restrict_fv_subset
            σ e1 vf X ltac:(cbn [fv_tm fv_value] in HfvX; set_solver))).
          exact Heval_fun. }
        destruct (proj1 (Heq σ0 Hσ0 vf) Hres1)
          as [σ2 [Hσ2 [Hσ2X Heval2]]].
        assert (Hσ_eq : store_restrict σ X = store_restrict σ2 X).
        { rewrite HσX, Hσ2X. reflexivity. }
        apply (proj2 (tm_eval_in_store_restrict_fv_subset
            σ e2 vf X ltac:(cbn [fv_tm fv_value] in HfvX; set_solver))).
        eapply tm_eval_in_store_agree_on_fv.
        2: exact Heval2.
        eapply storeA_restrict_eq_mono; [|exact Hσ_eq].
        cbn [fv_tm fv_value] in HfvX. set_solver.
      - assert (Hres2 : tm_fiber_result_on m X e2 σ0 vf).
        { exists σ. split; [exact Hσ|]. split; [exact HσX|].
          apply (proj1 (tm_eval_in_store_restrict_fv_subset
            σ e2 vf X ltac:(cbn [fv_tm fv_value] in HfvX; set_solver))).
          exact Heval_fun. }
        destruct (proj2 (Heq σ0 Hσ0 vf) Hres2)
          as [σ1 [Hσ1 [Hσ1X Heval1]]].
        assert (Hσ_eq : store_restrict σ X = store_restrict σ1 X).
        { rewrite HσX, Hσ1X. reflexivity. }
        apply (proj2 (tm_eval_in_store_restrict_fv_subset
            σ e1 vf X ltac:(cbn [fv_tm fv_value] in HfvX; set_solver))).
        eapply tm_eval_in_store_agree_on_fv.
        2: exact Heval1.
        eapply storeA_restrict_eq_mono; [|exact Hσ_eq].
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
  { subst σX X. apply Hclosed. exact Hσ. }
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
  { subst σX X. apply Hclosed. exact Hσ. }
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
