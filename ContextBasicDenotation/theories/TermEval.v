(** * BasicDenotation.TermEval

    Split out from [Term.v] to keep individual proof files small. *)

From ContextBasicDenotation Require Import Notation StoreTyping.
From ContextBasicDenotation Require Import TermSyntax.
From ContextAlgebra Require Import ResourceAlgebra.

Section TermDenotation.

Definition expr_eval_in_store (σ : LStoreT) (e : tm) (v : value) : Prop :=
  lstore_instantiate_tm σ e →* tret v.

Definition tm_eval_in_store (σ : StoreT) (e : tm) (v : value) : Prop :=
  expr_eval_in_store (lstore_lift_free σ) e v.

Lemma steps_tapp_tm_fun_equiv e e' vx v :
  lc_tm e ->
  lc_tm e' ->
  lc_value vx ->
  (forall vf, e →* tret vf <-> e' →* tret vf) ->
  (tapp_tm e vx →* tret v) <->
  (tapp_tm e' vx →* tret v).
Proof.
  intros Hlc Hlc' Hvx Hequiv.
  split.
  - intros Hsteps.
    unfold tapp_tm in Hsteps.
    apply reduction_lete in Hsteps as [vf [He Happ]].
    eapply reduction_lete_intro.
    + apply body_tapp_tm_body.
      rewrite value_shift_lc_id by exact Hvx. exact Hvx.
    + apply Hequiv. exact He.
    + exact Happ.
  - intros Hsteps.
    unfold tapp_tm in Hsteps.
    apply reduction_lete in Hsteps as [vf [He' Happ]].
    eapply reduction_lete_intro.
    + apply body_tapp_tm_body.
      rewrite value_shift_lc_id by exact Hvx. exact Hvx.
    + apply Hequiv. exact He'.
    + exact Happ.
Qed.

Lemma steps_tapp_tm_ret_equiv vf vx v :
  lc_value vf ->
  lc_value vx ->
  (tapp_tm (tret vf) vx →* tret v) <->
  (tapp vf vx →* tret v).
Proof.
  intros Hvf Hvx.
  unfold tapp_tm.
  rewrite reduction_lete_iff.
  - split.
    + intros [vf' [Hret Happ]].
      pose proof (value_steps_self vf (tret vf') Hret) as Heq.
      inversion Heq. subst vf'.
      rewrite value_shift_lc_id in Happ by exact Hvx.
      cbn [open_tm open_value] in Happ.
      rewrite open_rec_lc_value in Happ by exact Hvx.
      rewrite decide_True in Happ by lia.
      exact Happ.
    + intros Happ.
      exists vf. split.
      * apply value_reduction_any_ctx. exact Hvf.
      * rewrite value_shift_lc_id by exact Hvx.
        cbn [open_tm open_value].
        rewrite open_rec_lc_value by exact Hvx.
        rewrite decide_True by lia.
        exact Happ.
  - apply body_tapp_tm_body.
    rewrite value_shift_lc_id by exact Hvx.
    exact Hvx.
Qed.

Lemma msubst_tapp_tm_lc_arg σ e vx :
  lc_value vx ->
  lc_env σ ->
  m{σ} (tapp_tm e vx) =
  tapp_tm (m{σ} e) (m{σ} vx).
Proof.
  intros Hvx Hlcσ.
  unfold tapp_tm.
  rewrite msubst_lete, msubst_tapp.
  rewrite value_shift_lc_id by exact Hvx.
  rewrite (msubst_fresh σ (vbvar 0)).
  rewrite value_shift_lc_id.
  - reflexivity.
  - change (lc_value (m{σ} vx)).
    apply msubst_lc; [exact Hlcσ | exact Hvx].
  - cbn [fv_value]. set_solver.
Qed.

Lemma lstore_instantiate_tm_no_bvars σ e :
  lc_lstore σ ->
  closed_env (lstore_to_store σ) ->
  lstore_instantiate_tm σ e = subst_map (lstore_to_store σ) e.
Proof.
  intros Hlc Hclosed.
  unfold lstore_instantiate_tm.
  change (lstore_to_store σ) with (lstore_free_part σ).
  apply lstore_instantiate_tm_at_lc_lstore; assumption.
Qed.

Lemma expr_eval_in_store_no_bvars_iff σ e v :
  lc_lstore σ ->
  closed_env (lstore_to_store σ) ->
  expr_eval_in_store σ e v <->
  subst_map (lstore_to_store σ) e →* tret v.
Proof.
  intros Hlc Hclosed.
  unfold expr_eval_in_store.
  rewrite lstore_instantiate_tm_no_bvars by (exact Hlc || exact Hclosed).
  reflexivity.
Qed.

Lemma tm_eval_in_store_ret_fvar_lookup σ x v :
  store_closed σ ->
  σ !! x = Some v ->
  tm_eval_in_store σ (tret (vfvar x)) v.
Proof.
  intros Hclosed Hlookup.
  unfold tm_eval_in_store.
  rewrite expr_eval_in_store_no_bvars_iff.
  - rewrite lstore_free_part_lift_free.
    rewrite subst_map_tm_eq_msubst.
    rewrite (msubst_ret_fvar_lookup_closed σ x v)
      by (exact (proj1 Hclosed) || exact Hlookup).
    apply value_reduction_any_ctx.
    eapply (proj2 Hclosed); eauto.
  - apply lc_lstore_lift_free.
  - rewrite lstore_free_part_lift_free. exact (proj1 Hclosed).
Qed.

Lemma tm_eval_in_store_tapp_tm_fun_equiv σ e e' x v :
  store_closed σ ->
  lc_tm e ->
  lc_tm e' ->
  (forall vf,
    tm_eval_in_store σ e vf <->
    tm_eval_in_store σ e' vf) ->
  tm_eval_in_store σ (tapp_tm e (vfvar x)) v <->
  tm_eval_in_store σ (tapp_tm e' (vfvar x)) v.
Proof.
  intros Hclosed Hlc Hlc' Hequiv.
  unfold tm_eval_in_store.
  rewrite !expr_eval_in_store_no_bvars_iff.
  - rewrite !lstore_free_part_lift_free.
    rewrite !subst_map_tm_eq_msubst.
    rewrite !msubst_tapp_tm_lc_arg by (constructor || exact (proj2 Hclosed)).
    apply steps_tapp_tm_fun_equiv.
    + apply msubst_lc; [exact (proj2 Hclosed) | exact Hlc].
    + apply msubst_lc; [exact (proj2 Hclosed) | exact Hlc'].
    + apply msubst_lc; [exact (proj2 Hclosed) | constructor].
    + intros vf.
      specialize (Hequiv vf).
      unfold tm_eval_in_store in Hequiv.
      rewrite !expr_eval_in_store_no_bvars_iff in Hequiv.
      * rewrite !lstore_free_part_lift_free in Hequiv.
        rewrite !subst_map_tm_eq_msubst in Hequiv.
        exact Hequiv.
      * apply lc_lstore_lift_free.
      * rewrite lstore_free_part_lift_free. exact (proj1 Hclosed).
      * apply lc_lstore_lift_free.
      * rewrite lstore_free_part_lift_free. exact (proj1 Hclosed).
  - apply lc_lstore_lift_free.
  - rewrite lstore_free_part_lift_free. exact (proj1 Hclosed).
  - apply lc_lstore_lift_free.
  - rewrite lstore_free_part_lift_free. exact (proj1 Hclosed).
Qed.

Lemma tm_eval_in_store_tapp_tm_ret_equiv σ vf vx v :
  store_closed σ ->
  lc_value vf ->
  lc_value vx ->
  tm_eval_in_store σ (tapp_tm (tret vf) vx) v <->
  tm_eval_in_store σ (tapp vf vx) v.
Proof.
  intros Hclosed Hvf Hvx.
  unfold tm_eval_in_store, expr_eval_in_store.
  rewrite !lstore_instantiate_tm_no_bvars by
    (try apply lc_lstore_lift_free;
     rewrite ?lstore_free_part_lift_free; exact (proj1 Hclosed)).
  rewrite !lstore_free_part_lift_free.
  rewrite !subst_map_tm_eq_msubst.
  rewrite msubst_tapp_tm_lc_arg by (exact Hvx || exact (proj2 Hclosed)).
  rewrite msubst_ret, msubst_tapp.
  apply steps_tapp_tm_ret_equiv.
  - change (lc_value (m{σ} vf)).
    apply msubst_lc; [exact (proj2 Hclosed)|exact Hvf].
  - change (lc_value (m{σ} vx)).
    apply msubst_lc; [exact (proj2 Hclosed)|exact Hvx].
Qed.

Lemma tm_eval_in_store_tapp_tm_lam_body
    σ T e y vy v :
  store_closed σ ->
  body_tm e ->
  y ∉ fv_tm e ->
  σ !! y = Some vy ->
  tm_eval_in_store σ
    (tapp_tm (tret (vlam T e)) (vfvar y)) v <->
  tm_eval_in_store σ (e ^^ y) v.
Proof.
  intros Hclosed Hbody Hy Hσy.
  unfold tm_eval_in_store.
  rewrite !expr_eval_in_store_no_bvars_iff.
  - rewrite !lstore_free_part_lift_free.
    rewrite !subst_map_tm_eq_msubst.
    rewrite msubst_tapp_tm_lc_arg by (constructor || exact (proj2 Hclosed)).
    rewrite msubst_ret.
    rewrite msubst_vlam.
    rewrite (msubst_fvar_lookup_closed σ y vy)
      by (exact (proj1 Hclosed) || exact Hσy).
    change (m{σ} (e ^^ y)) with
      (m{σ} (open_tm 0 (vfvar y) e)).
    rewrite (msubst_open_lookup_tm σ e 0 y vy)
      by (try exact (proj1 Hclosed);
          try exact (proj2 Hclosed);
          try exact Hσy;
          try exact Hy).
    replace (m{delete y σ} e) with (m{σ} e).
    2:{
      symmetry.
      apply (msubst_agree tm (delete y σ) σ (fv_tm e) e).
      - apply closed_env_delete. exact (proj1 Hclosed).
      - exact (proj1 Hclosed).
      - reflexivity.
      - intros z Hz.
        assert (z <> y) by set_solver.
        assert (Hdel : delete y σ !! z = σ !! z).
        { apply lookup_delete_ne. congruence. }
        exact Hdel.
    }
    assert (Hbodyσ : body_tm (m{σ} e)).
    {
      exists (fv_tm e ∪ dom σ). intros z Hz.
      change (lc_tm (open_tm 0 (vfvar z) (m{σ} e))).
      assert (Hfreshz : m{σ} (vfvar z) = vfvar z).
      { apply msubst_fvar_lookup_none_closed.
        - exact (proj1 Hclosed).
        - apply not_elem_of_dom. set_solver. }
      rewrite <- Hfreshz.
      change (lc_tm ({0 ~> m{σ} (vfvar z)} (m{σ} e))).
      rewrite <- (msubst_open e 0 (vfvar z) σ)
        by (exact (proj1 Hclosed) || exact (proj2 Hclosed) || constructor).
      apply msubst_lc; [exact (proj2 Hclosed)|].
      apply body_open_tm; [exact Hbody|constructor].
    }
    unfold tapp_tm.
    split.
    + intros Hsteps.
      apply reduction_lete in Hsteps as [vf [Hfun Happ]].
      pose proof (value_steps_self
        (vlam T (m{σ} e)) (tret vf) Hfun) as Heq.
      inversion Heq. subst vf.
      eapply reduction_beta; [exact (lc_env_lookup _ _ _ (proj2 Hclosed) Hσy)|].
      rewrite value_shift_lc_id in Happ
        by (eapply lc_env_lookup; [exact (proj2 Hclosed)|exact Hσy]).
      cbn in Happ.
      rewrite (open_rec_lc_value vy
        (lc_env_lookup _ _ _ (proj2 Hclosed) Hσy) 0
        (vlam T (m{σ} e))) in Happ.
      exact Happ.
    + intros Hbody_steps.
      eapply reduction_lete_intro.
      * apply body_tapp_tm_body.
        pose proof (lc_env_lookup _ _ _ (proj2 Hclosed) Hσy) as Hvy_lc.
        rewrite value_shift_lc_id by exact Hvy_lc. exact Hvy_lc.
      * apply Steps_refl.
        apply LC_ret.
        destruct Hbodyσ as [Lσ Hbodyσ].
        exact (LC_lam T (m{σ} e) Lσ Hbodyσ).
      * cbn.
        pose proof (lc_env_lookup _ _ _ (proj2 Hclosed) Hσy) as Hvy_lc.
        rewrite value_shift_lc_id by exact Hvy_lc.
        rewrite (open_rec_lc_value vy Hvy_lc 0 (vlam T (m{σ} e))).
        eapply reduction_beta_intro.
        -- exact Hbodyσ.
        -- eapply lc_env_lookup; eauto. exact (proj2 Hclosed).
        -- exact Hbody_steps.
  - apply lc_lstore_lift_free.
  - rewrite lstore_free_part_lift_free. exact (proj1 Hclosed).
  - apply lc_lstore_lift_free.
  - rewrite lstore_free_part_lift_free. exact (proj1 Hclosed).
Qed.

Lemma tm_eval_in_store_match_true_fvar σ x et ef v :
  store_closed σ ->
  lc_tm et ->
  lc_tm ef ->
  σ !! x = Some (vconst (cbool true)) ->
  tm_eval_in_store σ (tmatch (vfvar x) et ef) v <->
  tm_eval_in_store σ et v.
Proof.
  intros Hclosed Hlcet Hlcef Hx.
  unfold tm_eval_in_store.
  rewrite !expr_eval_in_store_no_bvars_iff.
  - rewrite !lstore_free_part_lift_free.
    rewrite subst_map_tmatch.
    change (subst_map σ (vfvar x)) with (m{σ} (vfvar x)).
    rewrite (msubst_fvar_lookup_closed σ x (vconst (cbool true)))
      by (exact (proj1 Hclosed) || exact Hx).
    apply reduction_match_true_iff.
    + rewrite subst_map_tm_eq_msubst.
      apply msubst_lc; [exact (proj2 Hclosed)|exact Hlcet].
    + rewrite subst_map_tm_eq_msubst.
      apply msubst_lc; [exact (proj2 Hclosed)|exact Hlcef].
  - apply lc_lstore_lift_free.
  - rewrite lstore_free_part_lift_free. exact (proj1 Hclosed).
  - apply lc_lstore_lift_free.
  - rewrite lstore_free_part_lift_free. exact (proj1 Hclosed).
Qed.

Lemma tm_eval_in_store_match_false_fvar σ x et ef v :
  store_closed σ ->
  lc_tm et ->
  lc_tm ef ->
  σ !! x = Some (vconst (cbool false)) ->
  tm_eval_in_store σ (tmatch (vfvar x) et ef) v <->
  tm_eval_in_store σ ef v.
Proof.
  intros Hclosed Hlcet Hlcef Hx.
  unfold tm_eval_in_store.
  rewrite !expr_eval_in_store_no_bvars_iff.
  - rewrite !lstore_free_part_lift_free.
    rewrite subst_map_tmatch.
    change (subst_map σ (vfvar x)) with (m{σ} (vfvar x)).
    rewrite (msubst_fvar_lookup_closed σ x (vconst (cbool false)))
      by (exact (proj1 Hclosed) || exact Hx).
    apply reduction_match_false_iff.
    + rewrite subst_map_tm_eq_msubst.
      apply msubst_lc; [exact (proj2 Hclosed)|exact Hlcet].
    + rewrite subst_map_tm_eq_msubst.
      apply msubst_lc; [exact (proj2 Hclosed)|exact Hlcef].
  - apply lc_lstore_lift_free.
  - rewrite lstore_free_part_lift_free. exact (proj1 Hclosed).
  - apply lc_lstore_lift_free.
  - rewrite lstore_free_part_lift_free. exact (proj1 Hclosed).
Qed.

Lemma tm_eval_in_store_restrict_fv_subset σ e v X :
  fv_tm e ⊆ X ->
  tm_eval_in_store (store_restrict σ X) e v <->
  tm_eval_in_store σ e v.
Proof.
  intros Hfv.
  unfold tm_eval_in_store, expr_eval_in_store,
    lstore_instantiate_tm, lstore_instantiate_tm_at.
  rewrite !lstore_free_part_lift_free.
  rewrite !lstore_bound_part_empty_of_lc by apply lc_lstore_lift_free.
  rewrite lstore_instantiate_tm_split_restrict_fv by exact Hfv.
  reflexivity.
Qed.

Lemma tm_eval_in_world_tapp_tm_ret_equiv
    (m : WfWorldT) vf x :
  lc_value vf ->
  wfworld_closed_on
    (fv_tm (tapp_tm (tret vf) (vfvar x)) ∪
     fv_tm (tapp vf (vfvar x))) m ->
  forall σ v,
    worldA_stores (m : WorldT) σ ->
    tm_eval_in_store σ (tapp_tm (tret vf) (vfvar x)) v <->
    tm_eval_in_store σ (tapp vf (vfvar x)) v.
Proof.
  intros Hlc_vf Hclosed σ v Hσ.
  set (X := fv_tm (tapp_tm (tret vf) (vfvar x)) ∪
            fv_tm (tapp vf (vfvar x))).
  assert (HσX_closed : store_closed (store_restrict σ X)).
  { exact (Hclosed σ Hσ). }
  assert (Hfv_src : fv_tm (tapp_tm (tret vf) (vfvar x)) ⊆ X)
    by (subst X; better_set_solver).
  assert (Hfv_tgt : fv_tm (tapp vf (vfvar x)) ⊆ X)
    by (subst X; better_set_solver).
  split.
  - intros Heval_src.
    apply (proj1 (tm_eval_in_store_restrict_fv_subset
      σ (tapp vf (vfvar x)) v X Hfv_tgt)).
    apply (proj1 (tm_eval_in_store_tapp_tm_ret_equiv
      (store_restrict σ X) vf (vfvar x) v
      HσX_closed Hlc_vf ltac:(constructor))).
    apply (proj2 (tm_eval_in_store_restrict_fv_subset
      σ (tapp_tm (tret vf) (vfvar x)) v X Hfv_src)).
    exact Heval_src.
  - intros Heval_tgt.
    apply (proj1 (tm_eval_in_store_restrict_fv_subset
      σ (tapp_tm (tret vf) (vfvar x)) v X Hfv_src)).
    apply (proj2 (tm_eval_in_store_tapp_tm_ret_equiv
      (store_restrict σ X) vf (vfvar x) v
      HσX_closed Hlc_vf ltac:(constructor))).
    apply (proj2 (tm_eval_in_store_restrict_fv_subset
      σ (tapp vf (vfvar x)) v X Hfv_tgt)).
    exact Heval_tgt.
Qed.

Lemma tm_eval_in_store_restrict_fv_closed_on σ e v :
  closed_env (store_restrict σ (fv_tm e)) ->
  tm_eval_in_store (store_restrict σ (fv_tm e)) e v <->
  tm_eval_in_store σ e v.
Proof.
  intros _.
  apply tm_eval_in_store_restrict_fv_subset. set_solver.
Qed.

Lemma tm_eval_in_store_restrict_fv_exact σ e v :
  tm_eval_in_store (store_restrict σ (fv_tm e)) e v <->
  tm_eval_in_store σ e v.
Proof.
  apply tm_eval_in_store_restrict_fv_subset. set_solver.
Qed.

Lemma tm_eval_in_store_agree_on_fv σ1 σ2 e v :
  store_restrict σ1 (fv_tm e) = store_restrict σ2 (fv_tm e) ->
  tm_eval_in_store σ1 e v <->
  tm_eval_in_store σ2 e v.
Proof.
  intros Hagree.
  rewrite <- (tm_eval_in_store_restrict_fv_exact σ1 e v).
  rewrite <- (tm_eval_in_store_restrict_fv_exact σ2 e v).
  rewrite Hagree. reflexivity.
Qed.

Lemma store_insert_restrict_agree_on_open_fv
    (σ : StoreT) X e x vx :
  fv_tm e ⊆ X ->
  x ∉ X ->
  x ∉ dom (σ : gmap atom value) ->
  store_restrict (σ ∪ ({[x := vx]} : StoreT))
    (fv_tm (open_tm 0 (vfvar x) e)) =
  store_restrict (<[x := vx]> (store_restrict σ X))
    (fv_tm (open_tm 0 (vfvar x) e)).
Proof.
  intros HfvX HxX Hxσ.
  apply storeA_map_eq. intros z.
  change (((store_restrict (σ ∪ ({[x := vx]} : StoreT))
      (fv_tm (open_tm 0 (vfvar x) e)) : gmap atom value) !! z) =
    ((store_restrict (<[x := vx]> (store_restrict σ X))
      (fv_tm (open_tm 0 (vfvar x) e)) : gmap atom value) !! z)).
  assert (Hleft :
    ((store_restrict (σ ∪ ({[x := vx]} : StoreT))
      (fv_tm (open_tm 0 (vfvar x) e)) : gmap atom value) !! z) =
    if decide (z ∈ fv_tm (open_tm 0 (vfvar x) e))
    then ((σ ∪ ({[x := vx]} : StoreT)) : gmap atom value) !! z
    else None).
  { apply storeA_restrict_lookup. }
  assert (Hright :
    ((store_restrict (<[x := vx]> (store_restrict σ X))
      (fv_tm (open_tm 0 (vfvar x) e)) : gmap atom value) !! z) =
    if decide (z ∈ fv_tm (open_tm 0 (vfvar x) e))
    then ((<[x := vx]> (store_restrict σ X)) : gmap atom value) !! z
    else None).
  { apply storeA_restrict_lookup. }
  rewrite Hleft, Hright.
  destruct (decide (z ∈ fv_tm (open_tm 0 (vfvar x) e))) as [Hzopen|Hzopen];
    [|reflexivity].
  pose proof (open_fv_tm e (vfvar x) 0) as Hopen.
  cbn [fv_value] in Hopen.
  destruct (decide (z = x)) as [->|Hzx].
  - assert ((σ : gmap atom value) !! x = None) as Hσx.
    { better_map_solver. }
    change ((((σ : gmap atom value) ∪ ({[x := vx]} : gmap atom value)) !! x) =
      ((<[x := vx]> (store_restrict σ X : gmap atom value) : gmap atom value) !! x)).
	    transitivity ((({[x := vx]} : gmap atom value) !! x)).
	    + apply lookup_union_r. exact Hσx.
	    + transitivity (Some vx).
	      * apply map_lookup_insert.
	      * symmetry.
	        apply map_lookup_insert.
  - assert (HzX : z ∈ X).
    { set_solver. }
    destruct ((σ : gmap atom value) !! z) as [vz|] eqn:Hσz.
    + change ((((σ : gmap atom value) ∪ ({[x := vx]} : gmap atom value)) !! z) =
        ((<[x := vx]> (store_restrict σ X : gmap atom value) : gmap atom value) !! z)).
      transitivity (Some vz).
      * transitivity ((σ : gmap atom value) !! z).
        -- apply lookup_union_l'. exists vz. exact Hσz.
        -- rewrite Hσz. reflexivity.
      * symmetry.
        transitivity ((store_restrict σ X : StoreT) !! z).
        -- change (((<[x := vx]> (store_restrict σ X : gmap atom value) :
              gmap atom value) !! z) =
            ((store_restrict σ X : gmap atom value) !! z)).
           apply map_lookup_insert_ne. congruence.
        -- apply storeA_restrict_lookup_some_2; [exact Hσz|exact HzX].
    + change ((((σ : gmap atom value) ∪ ({[x := vx]} : gmap atom value)) !! z) =
        ((<[x := vx]> (store_restrict σ X : gmap atom value) : gmap atom value) !! z)).
      transitivity (@None value).
      * transitivity ((({[x := vx]} : StoreT) !! z)).
	        -- apply lookup_union_r. exact Hσz.
	        -- transitivity ((∅ : StoreT) !! z).
	           ++ apply map_lookup_insert_ne. congruence.
	           ++ reflexivity.
      * symmetry.
        transitivity ((store_restrict σ X : StoreT) !! z).
        -- change (((<[x := vx]> (store_restrict σ X : gmap atom value) :
              gmap atom value) !! z) =
            ((store_restrict σ X : gmap atom value) !! z)).
           apply map_lookup_insert_ne. congruence.
        -- apply storeA_restrict_lookup_none_l. exact Hσz.
Qed.

(** [expr_total_on e m] is the lworld-level totality predicate consumed by
    Logic qualifiers.  [LVFree x] entries instantiate free variables and
    [LVBound k] entries open locally-nameless bound variables. *)
Definition expr_total_on (e : tm) (m : LWorldT) : Prop :=
  tm_lvars e ⊆ worldA_dom m /\
  forall σ,
    worldA_stores m σ ->
    exists v, expr_eval_in_store σ e v.

(** Atom worlds use the same lstore semantics through the free-lvar lift. *)
Definition expr_total_on_atom_world (e : tm) (m : WfWorldT) : Prop :=
  expr_total_on e (res_lift_free m : LWorldT).

Definition expr_result_at_store (e : tm) (x : logic_var) (σ : LStoreT) : Prop :=
  x ∉ tm_lvars e /\
  exists v,
    σ !! x = Some v /\
    expr_eval_in_store σ e v.

(** A result world contains both the input variables of [e] and the fresh
    result variable [x].  Each store in that world binds [x] to a value obtained
    by evaluating [e] in the same store.  As with totality, no explicit store
    restriction is baked into the definition: [e] cannot inspect keys outside
    [tm_lvars e], while [x ∉ tm_lvars e] keeps the result cell separate from the
    input cells. *)
Definition expr_result_at_world (e : tm) (x : logic_var) (m : LWorldT) : Prop :=
  x ∉ tm_lvars e /\
  tm_lvars e ∪ {[x]} ⊆ worldA_dom m /\
  forall σ,
    worldA_stores m σ ->
    expr_result_at_store e x σ.

Lemma expr_eval_in_store_restrict_lvars e (σ : LStoreT) X v :
  tm_lvars e ⊆ X ->
  expr_eval_in_store (storeA_restrict σ X) e v <->
  expr_eval_in_store σ e v.
Proof.
  intros HX.
  unfold expr_eval_in_store.
  rewrite lstore_instantiate_tm_restrict_lvars by exact HX.
  reflexivity.
Qed.

Lemma expr_result_at_store_restrict_lvars e x (σ : LStoreT) X :
  tm_lvars e ∪ {[x]} ⊆ X ->
  expr_result_at_store e x σ ->
  expr_result_at_store e x (storeA_restrict σ X).
Proof.
  intros HX [Hx [v [Hlookup Heval]]].
  split; [exact Hx|].
  exists v. split.
  - apply storeA_restrict_lookup_some_2; [exact Hlookup|set_solver].
  - apply (proj2 (expr_eval_in_store_restrict_lvars e σ X v ltac:(set_solver))).
    exact Heval.
Qed.

Lemma lstore_lift_free_restrict_fv_lvars_eq (σ : StoreT) D :
  lc_lvars D ->
  storeA_restrict (lstore_lift_free (storeA_restrict σ (lvars_fv D)) : LStoreT) D =
  storeA_restrict (lstore_lift_free σ : LStoreT) D.
Proof.
  intros Hlc.
  apply storeA_map_eq. intros z.
  change (((storeA_restrict
      (lstore_lift_free (store_restrict σ (lvars_fv D)) : LStoreT) D
        : gmap logic_var value) !! z) =
    ((storeA_restrict (lstore_lift_free σ : LStoreT) D
        : gmap logic_var value) !! z)).
  destruct (decide (z ∈ D)) as [HzD|HzD].
	  2:{
	    transitivity (@None value).
	    - apply storeA_restrict_lookup_none_r. exact HzD.
	    - symmetry. apply storeA_restrict_lookup_none_r. exact HzD.
	  }
  destruct z as [k|y].
  - exfalso. exact (Hlc (LVBound k) HzD).
  - assert (HyD : y ∈ lvars_fv D).
    { apply lvars_fv_elem. exact HzD. }
    destruct ((σ : gmap atom value) !! y) as [u|] eqn:Hσy.
    + transitivity (Some u).
	      * apply storeA_restrict_lookup_some_2; [|exact HzD].
	        rewrite lstore_lift_free_lookup_free.
	        apply storeA_restrict_lookup_some_2; [exact Hσy|exact HyD].
      * symmetry. apply storeA_restrict_lookup_some_2; [|exact HzD].
        rewrite lstore_lift_free_lookup_free. exact Hσy.
    + transitivity (@None value).
	      * apply storeA_restrict_lookup_none_l.
	        rewrite lstore_lift_free_lookup_free.
	        apply storeA_restrict_lookup_none_l. exact Hσy.
      * symmetry. apply storeA_restrict_lookup_none_l.
        rewrite lstore_lift_free_lookup_free. exact Hσy.
Qed.

Lemma expr_result_at_world_lworld_on_lift e x
    (m : WfWorldT)
    (Hlc : lc_lvars (tm_lvars e ∪ {[x]}))
    (Hsub : lvars_fv (tm_lvars e ∪ {[x]}) ⊆ world_dom (m : WorldT)) :
  expr_result_at_world e x (res_lift_free m : LWorldT) ->
  expr_result_at_world e x
    (@lw value _ (lworld_on_lift (tm_lvars e ∪ {[x]}) m Hlc Hsub)).
Proof.
  intros [Hx [Hdom Hstores]].
  split; [exact Hx|]. split.
  - change (tm_lvars e ∪ {[x]} ⊆
      lworld_dom (@lw value _ (lworld_on_lift (tm_lvars e ∪ {[x]}) m Hlc Hsub))).
    rewrite (@lw_dom value (tm_lvars e ∪ {[x]})
      (lworld_on_lift (tm_lvars e ∪ {[x]}) m Hlc Hsub)).
    set_solver.
  - intros τ Hτ.
    unfold lworld_on_lift in Hτ.
    cbn [lw lraw_world raw_worldA worldA_stores] in Hτ.
    destruct Hτ as [τ0 [Hτ0 Hτrestrict]]. subst τ.
    destruct Hτ0 as [σr [Hσr ->]].
    simpl in Hσr.
    destruct Hσr as [σm [Hσm Hσr]]. subst σr.
    replace (storeA_restrict
        (lstore_lift_free (storeA_restrict σm
          (lvars_fv (tm_lvars e ∪ {[x]}))) : LStoreT)
        (tm_lvars e ∪ {[x]}))
      with (storeA_restrict (lstore_lift_free σm : LStoreT)
        (tm_lvars e ∪ {[x]})).
    2:{
      symmetry.
      apply lstore_lift_free_restrict_fv_lvars_eq. exact Hlc.
    }
    apply expr_result_at_store_restrict_lvars.
    + set_solver.
    + apply Hstores. exists σm. split; [exact Hσm|reflexivity].
Qed.

Definition expr_result_output_world (e : tm) (x : atom) (σ : StoreT) : WfWorldT.
Proof.
  destruct (excluded_middle_informative (exists v, tm_eval_in_store σ e v))
    as [Hex | _].
  - destruct (constructive_indefinite_description _ Hex) as [v _].
    exact (exist _ (singleton_world ({[x := v]} : StoreT))
      (wf_singleton_world ({[x := v]} : StoreT))).
  - exact (exist _ (singleton_world ({[x := inhabitant]} : StoreT))
      (wf_singleton_world ({[x := inhabitant]} : StoreT))).
Defined.

Definition expr_result_extension
    (e : tm) (x : atom) (Hfresh : x ∉ fv_tm e) : FiberExtensionT.
Proof.
  refine (mk_fiber_extension (fv_tm e) {[x]}
    (fun σ => expr_result_output_world e x σ) _ _ _).
  - set_solver.
  - intros σ Hσ. unfold expr_result_output_world.
    destruct (excluded_middle_informative (exists v, tm_eval_in_store σ e v))
      as [Hex | _].
	    + destruct (constructive_indefinite_description _ Hex) as [v _].
	      unfold world_dom, singleton_world. simpl.
	      apply dom_singleton_L.
	    + unfold world_dom, singleton_world. simpl.
	      apply dom_singleton_L.
  - intros σ Hσ. unfold expr_result_output_world.
    destruct (excluded_middle_informative (exists v, tm_eval_in_store σ e v))
      as [Hex | _].
    + destruct (constructive_indefinite_description _ Hex) as [v _].
      exists ({[x := v]} : StoreT). simpl. reflexivity.
    + exists ({[x := inhabitant]} : StoreT). simpl. reflexivity.
Defined.

Definition expr_total_lqual (e : tm) : logic_qualifier :=
  lqual (tm_lvars e)
    (fun w => expr_total_on e (@lw value _ w : LWorldT)).

Definition expr_total_formula (e : tm) : Formula :=
  FAtom (expr_total_lqual e).

Lemma formula_fv_expr_total_formula e :
  formula_fv (expr_total_formula e) = lvars_fv (tm_lvars e).
Proof.
  unfold expr_total_formula, expr_total_lqual.
  rewrite formula_fv_atom. reflexivity.
Qed.

End TermDenotation.
