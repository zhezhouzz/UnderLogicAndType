(** * BasicDenotation.BasicTypingOpen

    Opening lemmas for the basic typing side-condition formulas.  This file
    keeps the expensive locally-nameless open/close transport proofs out of
    [BasicTypingFormula.v], so files that only need model/introduction facts do
    not re-check the open transport block. *)

From ContextBasicDenotation Require Import Notation StoreTyping TermSyntax TermEval
  TermOpen BasicTypingFormula.
From ContextBase Require Import BaseTactics.
From ContextQualifier Require Import Qualifier.

Section BasicTypingOpen.

Local Ltac child_fresh_from_extended_cofinite :=
  match goal with
  | H : ?x ∉ ?L ∪ ({[?y]} : aset) |- ?x ∉ ?L =>
      intros HxL; apply H; apply elem_of_union_l; exact HxL
  end.

Local Ltac child_neq_from_extended_cofinite :=
  match goal with
  | H : ?x ∉ ?L ∪ ({[?y]} : aset) |- ?x <> ?y =>
      intros ->; apply H; apply elem_of_union_r;
      apply elem_of_singleton; reflexivity
  end.

Lemma formula_open_context_ty_wf_formula k y Σ τ :
  formula_open k y (context_ty_wf_formula Σ τ) =
  context_ty_wf_formula (lty_env_open_one k y Σ) (cty_open k y τ).
Proof.
  unfold context_ty_wf_formula, context_ty_wf_qual.
  rewrite formula_open_fiber_atom.
  apply f_equal.
  apply qual_ext.
  - rewrite lty_env_open_one_dom. reflexivity.
  - intros s1 s2 _. cbn [qual_prop].
    rewrite lty_env_open_one_dom.
    rewrite basic_context_ty_lvars_open.
    reflexivity.
Qed.

Lemma formula_open_env_context_ty_wf_formula η Σ τ :
  open_env_fresh_for_lvars η (dom Σ ∪ context_ty_lvars τ) ->
  open_env_values_inj η ->
  formula_open_env η (context_ty_wf_formula Σ τ) =
  context_ty_wf_formula (lty_env_open_lvars η Σ) (open_cty_env η τ).
Proof.
  revert Σ τ.
  induction η as [|k x η Hnone Hfold IH] using fin_maps.map_fold_ind.
  - intros Σ τ _ _.
    rewrite formula_open_env_empty, lty_env_open_lvars_empty,
      open_cty_env_empty. reflexivity.
  - intros Σ τ Hfresh Hinj.
    pose proof (open_env_values_inj_insert_inv η k x Hnone Hinj)
      as [Hinjη Havoid].
    pose proof (open_env_fresh_for_lvars_insert_tail η k x
      (dom Σ ∪ context_ty_lvars τ) Hnone Hfresh) as Hfreshη.
    rewrite formula_open_env_insert_fresh by assumption.
    rewrite IH by (exact Hfreshη || exact Hinjη).
    rewrite formula_open_context_ty_wf_formula.
    rewrite lty_env_open_lvars_insert_fresh.
    2: exact Hnone.
    2: exact Havoid.
    2:{ eapply open_env_fresh_for_lvars_mono;
          [intros v Hv; apply elem_of_union_l; exact Hv | exact Hfresh]. }
    rewrite open_cty_env_insert_fresh by assumption.
    reflexivity.
Qed.

Lemma open_value_commute_fresh_mutual :
  (forall v i j x y,
    i <> j ->
    x <> y ->
    open_value i (vfvar x) (open_value j (vfvar y) v) =
    open_value j (vfvar y) (open_value i (vfvar x) v)) *
  (forall e i j x y,
    i <> j ->
    x <> y ->
    open_tm i (vfvar x) (open_tm j (vfvar y) e) =
    open_tm j (vfvar y) (open_tm i (vfvar x) e)).
Proof.
  apply value_tm_mutind;
    cbn [open_value open_tm]; intros; try reflexivity;
    try solve [f_equal; eauto; lia].
  - destruct (decide (j = n)) as [->|Hjn];
      destruct (decide (i = n)) as [->|Hin];
      try contradiction; cbn [open_value];
      repeat case_decide; try congruence; reflexivity.
Qed.

Lemma open_value_commute_fresh v i j x y :
  i <> j ->
  x <> y ->
  open_value i (vfvar x) (open_value j (vfvar y) v) =
  open_value j (vfvar y) (open_value i (vfvar x) v).
Proof. exact (fst open_value_commute_fresh_mutual v i j x y). Qed.

Lemma open_tm_commute_fresh e i j x y :
  i <> j ->
  x <> y ->
  open_tm i (vfvar x) (open_tm j (vfvar y) e) =
  open_tm j (vfvar y) (open_tm i (vfvar x) e).
Proof. exact (snd open_value_commute_fresh_mutual e i j x y). Qed.

Lemma open_fv_fresh_inv_mutual :
  (forall v k x y,
    y <> x ->
    y ∈ fv_value (open_value k (vfvar x) v) ->
    y ∈ fv_value v) *
  (forall e k x y,
    y <> x ->
    y ∈ fv_tm (open_tm k (vfvar x) e) ->
    y ∈ fv_tm e).
Proof.
  apply value_tm_mutind;
    cbn [open_value open_tm fv_value fv_tm]; intros; try set_solver.
  destruct (decide (k = n)); cbn [fv_value] in H0; set_solver.
Qed.

Lemma open_value_fv_fresh_inv v k x y :
  y <> x ->
  y ∈ fv_value (open_value k (vfvar x) v) ->
  y ∈ fv_value v.
Proof. exact (fst open_fv_fresh_inv_mutual v k x y). Qed.

Lemma open_tm_fv_fresh_inv e k x y :
  y <> x ->
  y ∈ fv_tm (open_tm k (vfvar x) e) ->
  y ∈ fv_tm e.
Proof. exact (snd open_fv_fresh_inv_mutual e k x y). Qed.

Lemma close_open_commute_fresh_mutual :
  (forall v i j x y,
    i <> j ->
    x <> y ->
    close_value y j (open_value i (vfvar x) v) =
    open_value i (vfvar x) (close_value y j v)) *
  (forall e i j x y,
    i <> j ->
    x <> y ->
    close_tm y j (open_tm i (vfvar x) e) =
    open_tm i (vfvar x) (close_tm y j e)).
Proof.
  apply value_tm_mutind;
    cbn [close_value close_tm open_value open_tm]; intros;
    try reflexivity; try solve [f_equal; eauto; lia].
  - unfold subst_one.
    repeat case_decide; subst; cbn [open_value close_value];
      repeat case_decide; try congruence; try lia; reflexivity.
  - destruct (decide (i = n)); cbn [close_value];
      repeat case_decide; try congruence; try lia; reflexivity.
Qed.

Lemma close_value_open_commute_fresh v i j x y :
  i <> j ->
  x <> y ->
  close_value y j (open_value i (vfvar x) v) =
  open_value i (vfvar x) (close_value y j v).
Proof. exact (fst close_open_commute_fresh_mutual v i j x y). Qed.

Lemma close_tm_open_commute_fresh e i j x y :
  i <> j ->
  x <> y ->
  close_tm y j (open_tm i (vfvar x) e) =
  open_tm i (vfvar x) (close_tm y j e).
Proof. exact (snd close_open_commute_fresh_mutual e i j x y). Qed.

Lemma lty_env_open_one_commute_fresh i j x y (Σ : lty_env) :
  i <> j ->
  x <> y ->
  lty_env_open_one i x (lty_env_open_one j y Σ) =
  lty_env_open_one j y (lty_env_open_one i x Σ).
Proof.
  intros Hij Hxy.
  unfold lty_env_open_one, lvar_store_open_one.
  rewrite (storeA_rekey_compose (logic_var_open i x) (logic_var_open j y)).
  2:{ apply swap_inj. }
  2:{ intros a b Hab. eapply swap_inj. exact Hab. }
  rewrite (storeA_rekey_compose (logic_var_open j y) (logic_var_open i x)).
  2:{ apply swap_inj. }
  2:{ intros a b Hab. eapply swap_inj. exact Hab. }
  apply storeA_rekey_ext_on_dom. intros v _.
  apply logic_var_open_commute_fresh; assumption.
Qed.

Lemma lty_env_open_one_typed_bind_under_commute k x y (Σ : lty_env) T :
  x <> y ->
  LVFree y ∉ dom (lty_env_open_one 0 x (typed_lty_env_bind Σ T)) ->
  lty_env_open_one (S k) y
    (lty_env_open_one 0 x (typed_lty_env_bind Σ T)) =
  lty_env_open_one 0 x
    (typed_lty_env_bind (lty_env_open_one k y Σ) T).
Proof.
  intros Hxy Hyfresh.
  rewrite lty_env_open_one_commute_fresh by (lia || congruence).
  rewrite lvar_store_bind_open_under.
  - reflexivity.
  - intros Hbad. apply Hyfresh.
    rewrite lty_env_open_one_dom.
    replace (LVFree y) with (logic_var_open 0 x (LVFree y)).
    2:{
      rewrite logic_var_open_sym.
      unfold swap. repeat case_decide; congruence.
    }
    apply lvars_open_elem_open.
    rewrite lvar_store_bind_dom.
    apply elem_of_union_l.
    unfold lvars_shift_from.
    apply elem_of_map.
    exists (LVFree y). split; [reflexivity|exact Hbad].
Qed.

Lemma lty_env_open_one_lookup_open k y (Σ : lty_env) v T :
  Σ !! v = Some T ->
  lty_env_open_one k y Σ !! logic_var_open k y v = Some T.
Proof.
  intros Hlook.
  unfold lty_env_open_one, lvar_store_open_one.
  change ((storeA_swap (LVBound k) (LVFree y) Σ : gmap logic_var ty) !!
    swap (LVBound k) (LVFree y) v = Some T).
  unfold storeA_swap.
  rewrite (storeA_rekey_lookup (swap (LVBound k) (LVFree y))
    (swap_inj (LVBound k) (LVFree y)) Σ v).
  exact Hlook.
Qed.

Lemma lty_env_open_one_lookup_open_inv k y (Σ : lty_env) v T :
  lty_env_open_one k y Σ !! logic_var_open k y v = Some T ->
  Σ !! v = Some T.
Proof.
  intros Hlook.
  unfold lty_env_open_one, lvar_store_open_one in Hlook.
  change ((storeA_swap (LVBound k) (LVFree y) Σ : gmap logic_var ty) !!
    swap (LVBound k) (LVFree y) v = Some T) in Hlook.
  unfold storeA_swap in Hlook.
  rewrite (storeA_rekey_lookup (swap (LVBound k) (LVFree y))
    (swap_inj (LVBound k) (LVFree y)) Σ v) in Hlook.
  exact Hlook.
Qed.

Lemma lty_env_open_one_typed_bind_fresh_other x y (Σ : lty_env) T :
  x <> y ->
  y ∉ lvars_fv (dom Σ) ->
  y ∉ lvars_fv (dom (lty_env_open_one 0 x (typed_lty_env_bind Σ T))).
Proof.
  intros Hxy Hy.
  rewrite lvar_store_open_one_dom.
  intros Hbad.
  apply lvars_fv_open_subset in Hbad.
  rewrite typed_lty_env_bind_dom, lvars_fv_union,
    lvars_shift_from_fv, lvars_fv_singleton_bound in Hbad.
  better_set_solver.
Qed.

Local Ltac child_typed_bind_fresh_other :=
  eapply lty_env_open_one_typed_bind_fresh_other;
    [ child_neq_from_extended_cofinite
    | match goal with
      | Hfresh : ?y ∉ lvars_fv (dom ?Σ) |- ?y ∉ lvars_fv (dom ?Σ) =>
          exact Hfresh
      end ].

Local Ltac child_typed_bind_under_commute :=
  rewrite lty_env_open_one_typed_bind_under_commute by
    first [ child_neq_from_extended_cofinite
          | rewrite <- lvars_fv_elem; child_typed_bind_fresh_other ];
  reflexivity.

Lemma basic_has_ltype_open_one_fresh_mutual :
  (forall Σ v T,
    basic_value_has_ltype Σ v T ->
    forall k y,
	      y ∉ lvars_fv (dom Σ) ∪ fv_value v ->
	      basic_value_has_ltype (lty_env_open_one k y Σ)
	        (open_value k (vfvar y) v) T) /\
	  (forall Σ e T,
	    basic_tm_has_ltype Σ e T ->
    forall k y,
      y ∉ lvars_fv (dom Σ) ∪ fv_tm e ->
      basic_tm_has_ltype (lty_env_open_one k y Σ)
        (open_tm k (vfvar y) e) T).
Proof.
	  apply basic_has_ltype_mutind; intros; cbn [open_value open_tm].
	  - constructor.
	  - constructor.
	    replace (LVFree x) with (logic_var_open k y (LVFree x)).
	    + apply lty_env_open_one_lookup_open. exact e.
	    + change (swap (LVBound k) (LVFree y) (LVFree x) = LVFree x).
	      unfold swap. repeat case_decide; try congruence.
	      exfalso. apply H. cbn [fv_value]. set_solver.
	  - destruct (decide (k = k0)) as [->|Hneq].
	    + destruct (decide (k0 = k0)) as [_|Hfalse]; [|contradiction].
	      eapply BVT_FVar.
	      replace (LVFree y) with (logic_var_open k0 y (LVBound k0)).
	      * apply lty_env_open_one_lookup_open. exact e.
	      * better_base_solver.
	    + destruct (decide (k0 = k)) as [Heq|_]; [symmetry in Heq; contradiction|].
	      eapply BVT_BVar.
	      replace (LVBound k) with (logic_var_open k0 y (LVBound k)).
	      * apply lty_env_open_one_lookup_open. exact e.
	      * better_base_solver.
	  - eapply BVT_Lam with
	      (L := L ∪ {[y]} ∪ fv_tm e ∪ lvars_fv (dom Σ)).
	    intros x Hx.
	    cbn [open_one open_tm_atom_inst].
	    rewrite <- lty_env_open_one_typed_bind_under_commute.
	    + change (open_tm (S k) y e ^^ x) with
	        (open_tm 0 (vfvar x) (open_tm (S k) (vfvar y) e)).
	      rewrite open_tm_commute_fresh by (lia || set_solver).
	      eapply H; [set_solver|].
      intros Hbad.
      apply elem_of_union in Hbad as [Hbad|Hbad].
	      * apply H0.
	        rewrite lty_env_open_one_dom in Hbad.
	        apply lvars_fv_open_subset in Hbad.
	        rewrite lvar_store_bind_lvars_fv_dom in Hbad.
	        set_solver.
	      * pose proof (open_fv_tm' e (vfvar x) 0) as Hfv.
	        cbn [fv_value] in Hfv.
		        apply H0. cbn [fv_value].
		        apply elem_of_union_r.
		        apply (open_tm_fv_fresh_inv e 0 x y).
		        { intros ->. apply Hx. set_solver. }
		        { exact Hbad. }
    + set_solver.
	    + intros Hbad. apply H0.
	      rewrite lty_env_open_one_dom in Hbad.
	      apply lvars_fv_elem in Hbad.
	      apply lvars_fv_open_subset in Hbad.
	      rewrite lvar_store_bind_lvars_fv_dom in Hbad.
	      set_solver.
	  - eapply BVT_Fix with
	      (L := L ∪ {[y]} ∪ fv_value vf ∪ lvars_fv (dom Σ)).
	    intros x Hx.
	    cbn [open_one open_value_atom_inst].
	    rewrite <- lty_env_open_one_typed_bind_under_commute.
	    + change (open_value (S k) y vf ^^ x) with
	        (open_value 0 (vfvar x) (open_value (S k) (vfvar y) vf)).
	      rewrite open_value_commute_fresh by (lia || set_solver).
	      eapply H; [set_solver|].
      intros Hbad.
      apply elem_of_union in Hbad as [Hbad|Hbad].
	      * apply H0.
	        rewrite lty_env_open_one_dom in Hbad.
	        apply lvars_fv_open_subset in Hbad.
	        rewrite lvar_store_bind_lvars_fv_dom in Hbad.
	        set_solver.
	      * pose proof (open_fv_value' vf (vfvar x) 0) as Hfv.
	        cbn [fv_value] in Hfv.
		        apply H0. cbn [fv_value].
		        apply elem_of_union_r.
		        apply (open_value_fv_fresh_inv vf 0 x y).
		        { intros ->. apply Hx. set_solver. }
		        { exact Hbad. }
    + set_solver.
	    + intros Hbad. apply H0.
	      rewrite lty_env_open_one_dom in Hbad.
	      apply lvars_fv_elem in Hbad.
	      apply lvars_fv_open_subset in Hbad.
	      rewrite lvar_store_bind_lvars_fv_dom in Hbad.
	      set_solver.
	  - constructor. eapply H; set_solver.
	  - eapply BTT_Let with
	      (L := L ∪ {[y]} ∪ fv_tm e2 ∪ lvars_fv (dom Σ)).
	    + eapply H; set_solver.
	    + intros x Hx.
	      cbn [open_one open_tm_atom_inst].
	      rewrite <- lty_env_open_one_typed_bind_under_commute.
	      * change (open_tm (S k) y e2 ^^ x) with
	          (open_tm 0 (vfvar x) (open_tm (S k) (vfvar y) e2)).
	        rewrite open_tm_commute_fresh by (lia || set_solver).
	        eapply H0; [set_solver|].
        intros Hbad.
        apply elem_of_union in Hbad as [Hbad|Hbad].
	        -- apply H1.
	           rewrite lty_env_open_one_dom in Hbad.
	           apply lvars_fv_open_subset in Hbad.
	           rewrite lvar_store_bind_lvars_fv_dom in Hbad.
	           set_solver.
	        -- pose proof (open_fv_tm' e2 (vfvar x) 0) as Hfv.
	           cbn [fv_value] in Hfv.
		           apply H1. cbn [fv_value].
		           apply elem_of_union_r.
		           cbn [fv_tm]. apply elem_of_union_r.
		           change (fv_tm (e2 ^^ x)) with
		             (fv_tm (open_tm 0 (vfvar x) e2)) in Hbad.
		           apply (open_tm_fv_fresh_inv e2 0 x y).
		           { intros ->. apply Hx. set_solver. }
		           { exact Hbad. }
      * set_solver.
	      * intros Hbad. apply H1.
	        rewrite lty_env_open_one_dom in Hbad.
	        apply lvars_fv_elem in Hbad.
	        apply lvars_fv_open_subset in Hbad.
	        rewrite lvar_store_bind_lvars_fv_dom in Hbad.
	        set_solver.
	  - eapply BTT_Op.
	    + exact e.
	    + eapply H; set_solver.
	  - eapply BTT_BinOp; first done.
	    + eapply H; set_solver.
	    + eapply H0; set_solver.
	  - eapply BTT_App.
	    + eapply H; set_solver.
	    + eapply H0; set_solver.
	  - eapply BTT_Match.
	    + eapply H; set_solver.
	    + eapply H0; set_solver.
	    + eapply H1; set_solver.
Qed.

Lemma basic_tm_has_ltype_open_one_fresh k y Σ e T :
  y ∉ lvars_fv (dom Σ) ∪ fv_tm e ->
  basic_tm_has_ltype Σ e T ->
  basic_tm_has_ltype (lty_env_open_one k y Σ)
    (open_tm k (vfvar y) e) T.
Proof.
  intros Hy Hty.
  exact (proj2 basic_has_ltype_open_one_fresh_mutual
    Σ e T Hty k y Hy).
Qed.

Lemma atom_env_lty_env_roundtrip_closed (Σ : lty_env) :
  lty_env_closed Σ ->
  atom_env_to_lty_env (lty_env_to_atom_env Σ) = Σ.
Proof.
  intros Hclosed.
  apply map_eq. intros [k|x].
  - rewrite atom_store_to_lvar_store_lookup_bound_none.
    symmetry. apply lty_env_closed_lookup_bound_none. exact Hclosed.
  - rewrite atom_store_to_lvar_store_lookup_free.
    apply lvar_store_to_atom_store_lookup.
Qed.

Lemma basic_tm_has_ltype_of_atom_typing Σ e T :
  lty_env_closed Σ ->
  lty_env_to_atom_env Σ ⊢ₑ e ⋮ T ->
  basic_tm_has_ltype Σ e T.
Proof.
  intros Hclosed Hty.
  pose proof (basic_tm_has_ltype_of_atom_env_typing
    (lty_env_to_atom_env Σ) e T Hty) as Hbasic.
  rewrite atom_env_lty_env_roundtrip_closed in Hbasic by exact Hclosed.
  exact Hbasic.
Qed.

Lemma basic_tm_eval_value_type
    Σ σ e T v :
  lty_env_closed Σ ->
  atom_store_has_ltype Σ σ ->
  basic_tm_has_ltype Σ e T ->
  tm_eval_in_store σ e v ->
  fv_tm e ⊆ dom (σ : StoreT) ->
  ∅ ⊢ᵥ v ⋮ T.
Proof.
  intros HΣclosed Hσtyped Hty Heval Hfvcover.
  pose proof (atom_store_has_ltype_closed _ _ Hσtyped) as Hσclosed.
  destruct Hσclosed as [Hclosed Hlcenv].
  pose proof (basic_tm_has_ltype_to_atom_env_typing
    (lty_env_to_atom_env Σ) e T) as Hto_atom.
  rewrite atom_env_lty_env_roundtrip_closed in Hto_atom by exact HΣclosed.
  specialize (Hto_atom Hty) as Hty_atom.
  pose proof (atom_store_has_ltype_env_has_type Σ σ Hσtyped) as Henvty.
  pose proof (msubst_basic_typing_tm
    (lty_env_to_atom_env Σ) σ e T Hclosed Henvty Hty_atom)
    as Hsubst_ty.
  assert (Hsubst_ty_empty : ∅ ⊢ₑ m{σ} e ⋮ T).
  {
    eapply basic_typing_env_agree_tm; [exact Hsubst_ty|].
    intros y Hy.
    exfalso.
    pose proof (msubst_fv_delete_tm σ e Hclosed) as Hfv.
    set_solver.
  }
  unfold tm_eval_in_store, expr_eval_in_store in Heval.
  rewrite lstore_instantiate_tm_no_bvars in Heval.
  - rewrite lstore_free_part_lift_free in Heval.
    pose proof (basic_steps_preservation ∅ (m{σ} e) (tret v) T
      Hsubst_ty_empty Heval) as Hret.
    inversion Hret; subst.
    match goal with
    | H : ∅ ⊢ᵥ v ⋮ _ |- _ => exact H
    end.
  - apply lc_lstore_lift_free.
  - rewrite lstore_free_part_lift_free. exact Hclosed.
Qed.

Lemma basic_tm_has_ltype_close_one_fresh k y Σ e T :
  y ∉ lvars_fv (dom Σ) ∪ fv_tm e ->
  basic_tm_has_ltype (lty_env_open_one k y Σ)
    (open_tm k (vfvar y) e) T ->
  basic_tm_has_ltype Σ e T.
Proof.
  intros Hy Hty.
  assert (Hclosed :
    basic_tm_has_ltype Σ
      (close_tm y k (open_tm k (vfvar y) e)) T).
  {
    revert k y Σ e T Hy Hty.
    enough (Hclose :
	      (forall Σ v T,
	        basic_value_has_ltype Σ v T ->
	        forall k y Σ0,
	          y ∉ lvars_fv (dom Σ0) ->
	          Σ = lty_env_open_one k y Σ0 ->
	          basic_value_has_ltype Σ0 (close_value y k v) T) /\
	      (forall Σ e T,
	        basic_tm_has_ltype Σ e T ->
	        forall k y Σ0,
	          y ∉ lvars_fv (dom Σ0) ->
	          Σ = lty_env_open_one k y Σ0 ->
	          basic_tm_has_ltype Σ0 (close_tm y k e) T)).
	    {
	      intros k y Σ e T Hy Hty.
	      eapply (proj2 Hclose); [exact Hty|set_solver|reflexivity].
	    }
	    apply basic_has_ltype_mutind; intros; subst.
    - constructor.
    - destruct (decide (x = y)) as [->|Hxy].
      + cbn [close_value].
        destruct (decide (y = y)) as [_|Hneq]; [|contradiction].
        eapply BVT_BVar.
        replace (LVFree y) with (logic_var_open k y (LVBound k)) in e
          by better_base_solver.
        eapply lty_env_open_one_lookup_open_inv. exact e.
      + cbn [close_value].
        destruct (decide (y = x)) as [Heq|_]; [symmetry in Heq; contradiction|].
        eapply BVT_FVar.
        replace (LVFree x) with (logic_var_open k y (LVFree x)) in e.
        * eapply lty_env_open_one_lookup_open_inv. exact e.
        * better_base_solver.
    - eapply BVT_BVar.
      destruct (decide (k0 = k)) as [->|Hneq].
      + exfalso.
        assert (Σ0 !! LVFree y = Some T) as Hlook.
        {
          eapply lty_env_open_one_lookup_open_inv.
          replace (logic_var_open k y (LVFree y)) with (LVBound k)
            by better_base_solver.
          exact e.
        }
        apply elem_of_dom_2 in Hlook.
        rewrite <- lvars_fv_elem in Hlook.
        match goal with
        | Hfresh : y ∉ lvars_fv (dom Σ0) |- _ => exact (Hfresh Hlook)
        end.
      + replace (LVBound k) with (logic_var_open k0 y (LVBound k)) in e.
        * eapply lty_env_open_one_lookup_open_inv. exact e.
        * better_base_solver.
    - eapply BVT_Lam with (L := L ∪ {[y]}).
      intros x Hx.
      pose proof (H x ltac:(child_fresh_from_extended_cofinite) (S k) y
        (lty_env_open_one 0 x (typed_lty_env_bind Σ0 s))
        ltac:(child_typed_bind_fresh_other)
        ltac:(child_typed_bind_under_commute)) as Hbody.
      + cbn [open_one open_tm_atom_inst].
        change (e ^^ x) with (open_tm 0 (vfvar x) e) in Hbody.
        rewrite close_tm_open_commute_fresh in Hbody by (lia || set_solver).
        exact Hbody.
    - eapply BVT_Fix with (L := L ∪ {[y]}).
      intros x Hx.
      pose proof (H x ltac:(child_fresh_from_extended_cofinite) (S k) y
        (lty_env_open_one 0 x (typed_lty_env_bind Σ0 sx))
        ltac:(child_typed_bind_fresh_other)
        ltac:(child_typed_bind_under_commute)) as Hbody.
      + cbn [open_one open_value_atom_inst].
        change (vf ^^ x) with (open_value 0 (vfvar x) vf) in Hbody.
        rewrite close_value_open_commute_fresh in Hbody by (lia || set_solver).
        exact Hbody.
    - constructor.
      eapply H; [|reflexivity].
      match goal with
      | Hfresh : y ∉ lvars_fv (dom Σ0) |- _ => exact Hfresh
      end.
    - eapply BTT_Let with (L := L ∪ {[y]}).
      + eapply H; [|reflexivity].
        match goal with
        | Hfresh : y ∉ lvars_fv (dom Σ0) |- _ => exact Hfresh
        end.
      + intros x Hx.
        pose proof (H0 x ltac:(child_fresh_from_extended_cofinite) (S k) y
          (lty_env_open_one 0 x (typed_lty_env_bind Σ0 T1))
          ltac:(child_typed_bind_fresh_other)
          ltac:(child_typed_bind_under_commute)) as Hbody.
        * cbn [open_one open_tm_atom_inst].
          change (e2 ^^ x) with (open_tm 0 (vfvar x) e2) in Hbody.
          rewrite close_tm_open_commute_fresh in Hbody by (lia || set_solver).
          exact Hbody.
    - eapply BTT_Op.
      + exact e.
      + eapply H; [|reflexivity].
        match goal with
        | Hfresh : y ∉ lvars_fv (dom Σ0) |- _ => exact Hfresh
        end.
    - eapply BTT_BinOp; first done.
      + eapply H; [|reflexivity].
        match goal with
        | Hfresh : y ∉ lvars_fv (dom Σ0) |- _ => exact Hfresh
        end.
      + eapply H0; [|reflexivity].
        match goal with
        | Hfresh : y ∉ lvars_fv (dom Σ0) |- _ => exact Hfresh
        end.
    - eapply BTT_App.
      + eapply H; [|reflexivity].
        match goal with
        | Hfresh : y ∉ lvars_fv (dom Σ0) |- _ => exact Hfresh
        end.
      + eapply H0; [|reflexivity].
        match goal with
        | Hfresh : y ∉ lvars_fv (dom Σ0) |- _ => exact Hfresh
        end.
    - eapply BTT_Match.
      + eapply H; [|reflexivity].
        match goal with
        | Hfresh : y ∉ lvars_fv (dom Σ0) |- _ => exact Hfresh
        end.
      + eapply H0; [|reflexivity].
        match goal with
        | Hfresh : y ∉ lvars_fv (dom Σ0) |- _ => exact Hfresh
        end.
      + eapply H1; [|reflexivity].
        match goal with
        | Hfresh : y ∉ lvars_fv (dom Σ0) |- _ => exact Hfresh
        end.
  }
  rewrite close_open_var_tm in Hclosed by set_solver.
  exact Hclosed.
Qed.

Lemma basic_tm_has_ltype_open_one_fresh_iff k y Σ e T :
  y ∉ lvars_fv (dom Σ) ∪ fv_tm e ->
  basic_tm_has_ltype Σ e T <->
  basic_tm_has_ltype (lty_env_open_one k y Σ)
    (open_tm k (vfvar y) e) T.
Proof.
  intros Hy. split.
  - apply basic_tm_has_ltype_open_one_fresh. exact Hy.
  - apply basic_tm_has_ltype_close_one_fresh. exact Hy.
Qed.

Lemma formula_open_expr_basic_typing_formula k y Σ e T :
  y ∉ lvars_fv (dom Σ) ∪ fv_tm e ->
  formula_open k y (expr_basic_typing_formula Σ e T) =
  expr_basic_typing_formula
    (lty_env_open_one k y Σ) (open_tm k (vfvar y) e) T.
Proof.
  intros Hy.
  unfold expr_basic_typing_formula, expr_basic_typing_qual.
  rewrite formula_open_fiber_atom.
  apply f_equal.
  apply qual_ext.
  - rewrite lty_env_open_one_dom. reflexivity.
  - intros s1 s2 _. cbn [qual_prop].
    apply basic_tm_has_ltype_open_one_fresh_iff. exact Hy.
Qed.

Lemma formula_open_env_expr_basic_typing_formula η Σ e T :
  open_env_fresh_for_lvars η (dom Σ ∪ tm_lvars e) ->
  open_env_values_inj η ->
  formula_open_env η (expr_basic_typing_formula Σ e T) =
  expr_basic_typing_formula
    (lty_env_open_lvars η Σ) (open_tm_env η e) T.
Proof.
  revert Σ e.
  induction η as [|k x η Hnone Hfold IH] using fin_maps.map_fold_ind.
  - intros Σ e _ _.
    rewrite formula_open_env_empty, lty_env_open_lvars_empty.
    rewrite map_fold_empty. reflexivity.
  - intros Σ e Hfresh Hinj.
    pose proof (open_env_values_inj_insert_inv η k x Hnone Hinj)
      as [Hinjη Havoid].
    pose proof (open_env_fresh_for_lvars_insert_tail η k x
      (dom Σ ∪ tm_lvars e) Hnone Hfresh) as Hfreshη.
    rewrite formula_open_env_insert_fresh by assumption.
    rewrite IH by (exact Hfreshη || exact Hinjη).
    rewrite formula_open_expr_basic_typing_formula.
    2:{
      pose proof (open_env_fresh_for_lvars_insert_head η k x
        (dom Σ ∪ tm_lvars e) Hnone Hfresh) as Hhead.
      rewrite <- tm_lvars_fv.
      rewrite tm_lvars_open_tm_env.
      2:{ eapply open_env_fresh_for_lvars_mono.
          - intros v Hv. apply elem_of_union_r. exact Hv.
          - exact Hfreshη. }
      assert (HΣfv : lvars_fv (dom (lty_env_open_lvars η Σ)) ⊆
                     lvars_fv (lvars_open_env η (dom Σ))).
      {
        rewrite lty_env_open_lvars_dom.
        - unfold lvars_open_env. set_solver.
        - eapply open_env_fresh_for_lvars_mono;
            [intros v Hv; apply elem_of_union_l; exact Hv|exact Hfreshη].
      }
      intros Hbad. apply Hhead.
      rewrite lvars_open_env_union, lvars_fv_union.
      apply elem_of_union.
      apply elem_of_union in Hbad as [Hbad|Hbad].
      - left. apply HΣfv. exact Hbad.
      - right. exact Hbad.
    }
    rewrite lty_env_open_lvars_insert_fresh.
    2: exact Hnone.
    2: exact Havoid.
    2:{ eapply open_env_fresh_for_lvars_mono;
          [intros v Hv; apply elem_of_union_l; exact Hv|exact Hfresh]. }
    rewrite open_tm_env_insert_fresh_plain by exact Hnone.
    reflexivity.
Qed.

End BasicTypingOpen.
