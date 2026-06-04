(** * ContextTypeLanguage.WF

    Formation/scoping predicates for lvar sets, context types, and contexts. *)

From LocallyNameless Require Import Classes.
From ContextTypeLanguage Require Export LtyEnv.
From ContextBase Require Import BaseTactics.

(** ** Context-Type Formation *)


Fixpoint cty_lc_at (d : nat) (τ : context_ty) : Prop :=
  match τ with
  | CTOver _ φ | CTUnder _ φ =>
      lvars_lc_at (S d) (qual_vars φ)
  | CTInter τ1 τ2
  | CTUnion τ1 τ2
  | CTSum τ1 τ2 =>
      cty_lc_at d τ1 /\ cty_lc_at d τ2
  | CTArrow τx τ
  | CTWand τx τ =>
      cty_lc_at d τx /\ cty_lc_at (S d) τ
  end.

Definition lc_context_ty (τ : context_ty) : Prop :=
  cty_lc_at 0 τ.

Fixpoint context_ty_shape_ok (τ : context_ty) : Prop :=
  match τ with
  | CTOver _ _ | CTUnder _ _ => True
  | CTInter τ1 τ2 | CTUnion τ1 τ2 | CTSum τ1 τ2 =>
      context_ty_shape_ok τ1 /\
      context_ty_shape_ok τ2 /\
      erase_ty τ1 = erase_ty τ2
  | CTArrow τx τ | CTWand τx τ =>
      context_ty_shape_ok τx /\ context_ty_shape_ok τ
  end.

Definition basic_context_ty_lvars (D : lvset) (τ : context_ty) : Prop :=
  context_ty_lvars τ ⊆ D /\ context_ty_shape_ok τ.

Lemma context_ty_shape_ok_msubst_store σ τ :
  context_ty_shape_ok (context_ty_msubst_store σ τ) <->
  context_ty_shape_ok τ.
Proof.
  induction τ; cbn [context_ty_msubst_store context_ty_shape_ok];
    try rewrite ?IHτ1, ?IHτ2, ?erase_ty_context_ty_msubst_store; tauto.
Qed.

Lemma basic_context_ty_lvars_msubst_store σ D τ :
  basic_context_ty_lvars D τ ->
  basic_context_ty_lvars
    (D ∖ lvars_of_atoms (dom (σ : gmap atom value)))
    (context_ty_msubst_store σ τ).
Proof.
  intros [Hvars Hshape]. split.
  - rewrite context_ty_lvars_msubst_store. set_solver.
  - apply context_ty_shape_ok_msubst_store. exact Hshape.
Qed.

Lemma basic_context_ty_lvars_mono D E τ :
  D ⊆ E ->
  basic_context_ty_lvars D τ ->
  basic_context_ty_lvars E τ.
Proof.
  intros HDE [Hvars Hshape]. split; [set_solver|exact Hshape].
Qed.

Lemma basic_context_ty_lvars_insert D x τ :
  basic_context_ty_lvars D τ ->
  basic_context_ty_lvars ({[LVFree x]} ∪ D) τ.
Proof.
  apply basic_context_ty_lvars_mono. set_solver.
Qed.

Lemma basic_context_ty_lvars_insert_fresh
    (Σ : gmap logic_var ty) x T τ :
  basic_context_ty_lvars (dom Σ) τ ->
  basic_context_ty_lvars (dom (<[LVFree x := T]> Σ)) τ.
Proof.
  intros Hbasic.
  eapply basic_context_ty_lvars_mono; [|exact Hbasic].
  rewrite (dom_insert_L (M := gmap logic_var) (D := gset logic_var)).
  set_solver.
Qed.

Lemma basic_context_ty_lvars_insert_free_fv_drop
    (Σ : gmap logic_var ty) τ x T :
  LVFree x ∉ context_ty_lvars τ ->
  basic_context_ty_lvars (dom (<[LVFree x := T]> Σ)) τ ->
  fv_cty τ ⊆ lvars_fv (dom Σ).
Proof.
  intros Hfresh [Hsub _].
  rewrite <- context_ty_lvars_fv.
  eapply lvars_fv_subset_insert_free_drop; [exact Hfresh|].
  intros v Hv.
  specialize (Hsub v Hv).
  rewrite dom_insert_L in Hsub.
  exact Hsub.
Qed.

Fixpoint wf_context_ty_at (d : nat) (D : aset) (τ : context_ty) : Prop :=
  match τ with
  | CTOver _ φ | CTUnder _ φ =>
      lvars_wf_at (S d) D (qual_vars φ)
  | CTInter τ1 τ2
  | CTUnion τ1 τ2
  | CTSum τ1 τ2 =>
      wf_context_ty_at d D τ1 /\
      wf_context_ty_at d D τ2 /\
      erase_ty τ1 = erase_ty τ2
  | CTArrow τx τ =>
      wf_context_ty_at d D τx /\
      wf_context_ty_at (S d) D τ
  | CTWand τx τ =>
      wf_context_ty_at 0 ∅ τx /\
      wf_context_ty_at (S d) D τ
  end.

Definition basic_context_ty (D : aset) (τ : context_ty) : Prop :=
  wf_context_ty_at 0 D τ.

#[global] Instance lc_cty_inst : Lc context_ty := lc_context_ty.
Arguments lc_cty_inst /.

Class ScopedIn A := scoped_in : aset -> A -> Prop.

#[global] Instance scoped_context_ty : ScopedIn context_ty := basic_context_ty.

Notation "D '⊢s' x" := (scoped_in D x)
  (at level 40, x at level 40).
Notation "D '⊢sτ' τ" := (basic_context_ty D τ)
  (at level 40, τ at level 40, only printing).

Lemma scoped_context_ty_iff D τ :
  D ⊢s τ <-> basic_context_ty D τ.
Proof. reflexivity. Qed.

Lemma wf_context_ty_at_shift d D τ k :
  d <= k ->
  wf_context_ty_at d D τ ->
  wf_context_ty_at d D (cty_shift k τ).
Proof.
  induction τ as [b φ|b φ|τ1 IHτ1 τ2 IHτ2|τ1 IHτ1 τ2 IHτ2
                 |τ1 IHτ1 τ2 IHτ2|τ1 IHτ1 τ2 IHτ2|τ1 IHτ1 τ2 IHτ2]
    in d, D, k |- *; cbn [wf_context_ty_at cty_shift]; intros Hdk Hwf.
  - rewrite qual_shift_from_vars.
    eapply (lvars_wf_at_shift (S d) D (qual_vars φ) (S k));
      [lia|exact Hwf].
  - rewrite qual_shift_from_vars.
    eapply (lvars_wf_at_shift (S d) D (qual_vars φ) (S k));
      [lia|exact Hwf].
  - destruct Hwf as [H1 [H2 Herase]]. repeat split.
    + eapply IHτ1; [lia|exact H1].
    + eapply IHτ2; [lia|exact H2].
    + rewrite !cty_shift_preserves_erasure. exact Herase.
  - destruct Hwf as [H1 [H2 Herase]]. repeat split.
    + eapply IHτ1; [lia|exact H1].
    + eapply IHτ2; [lia|exact H2].
    + rewrite !cty_shift_preserves_erasure. exact Herase.
  - destruct Hwf as [H1 [H2 Herase]]. repeat split.
    + eapply IHτ1; [lia|exact H1].
    + eapply IHτ2; [lia|exact H2].
    + rewrite !cty_shift_preserves_erasure. exact Herase.
  - destruct Hwf as [H1 H2]. split.
    + eapply IHτ1; [lia|exact H1].
    + eapply IHτ2; [lia|exact H2].
  - destruct Hwf as [H1 H2]. split.
    + eapply IHτ1; [lia|exact H1].
    + eapply IHτ2; [lia|exact H2].
Qed.

Lemma wf_context_ty_at_mono d D E τ :
  D ⊆ E ->
  wf_context_ty_at d D τ ->
  wf_context_ty_at d E τ.
Proof.
  induction τ in d |- *; cbn [wf_context_ty_at]; intros HDE Hwf;
    try solve [eapply lvars_wf_at_mono; eauto].
  all: repeat match goal with
  | H : _ /\ _ |- _ => destruct H
  | H : _ /\ _ /\ _ |- _ => destruct H as [? [? ?]]
  end; repeat split; eauto.
Qed.

Lemma lvars_at_depth_subset_of_atoms_wf d D L :
  lvars_at_depth d L ⊆ lvars_of_atoms D ->
  lvars_wf_at d D L.
Proof.
  intros Hsub [n|x] Hv; cbn [lvar_wf_at].
  - destruct (decide (d <= n)) as [Hdn|Hdn]; [|lia].
    assert (LVBound (n - d) ∈ lvars_at_depth d L) as Hin.
    {
      apply lvars_at_depth_elem.
      exists (LVBound n). split; [exact Hv|].
      cbn [logic_var_at_depth]. destruct (decide (d <= n)); [reflexivity|lia].
    }
    specialize (Hsub _ Hin).
    unfold lvars_of_atoms in Hsub.
    apply elem_of_map in Hsub as [? [Hbad _]]. discriminate.
  - assert (LVFree x ∈ lvars_at_depth d L) as Hin.
    {
      apply lvars_at_depth_elem.
      exists (LVFree x). split; [exact Hv|reflexivity].
    }
    specialize (Hsub _ Hin).
    unfold lvars_of_atoms in Hsub.
    apply elem_of_map in Hsub as [y [Heq Hy]].
    inversion Heq. subst. exact Hy.
Qed.

Lemma lvars_wf_at_subset_of_atoms_depth d D L :
  lvars_wf_at d D L ->
  lvars_at_depth d L ⊆ lvars_of_atoms D.
Proof.
  intros Hwf u Hu.
  apply lvars_at_depth_elem in Hu as [[n|x] [Hv Hdepth]].
  - cbn [logic_var_at_depth] in Hdepth.
    destruct (decide (d <= n)) as [Hdn|Hdn]; [|discriminate].
    exfalso.
    specialize (Hwf (LVBound n) Hv). cbn [lvar_wf_at] in Hwf. lia.
  - cbn [logic_var_at_depth] in Hdepth.
    inversion Hdepth. subst u.
    unfold lvars_of_atoms. apply elem_of_map.
    exists x. split; [reflexivity|].
    exact (Hwf (LVFree x) Hv).
Qed.

Lemma basic_context_ty_iff_wf_context_ty_at D τ :
  basic_context_ty D τ <-> wf_context_ty_at 0 D τ.
Proof.
  reflexivity.
Qed.

Lemma basic_context_ty_mono D E τ :
  D ⊆ E ->
  basic_context_ty D τ ->
  basic_context_ty E τ.
Proof.
  apply wf_context_ty_at_mono.
Qed.

Lemma context_ty_shape_ok_open k x τ :
  context_ty_shape_ok (cty_open k x τ) <-> context_ty_shape_ok τ.
Proof.
  induction τ in k |- *; cbn [context_ty_shape_ok cty_open];
    try tauto.
  all: try rewrite !cty_open_preserves_erasure.
  all: try rewrite IHτ1, IHτ2.
  all: tauto.
Qed.

Lemma basic_context_ty_lvars_open k x D τ :
  basic_context_ty_lvars (lvars_open k x D) (cty_open k x τ) <->
  basic_context_ty_lvars D τ.
Proof.
  unfold basic_context_ty_lvars.
  split; intros [Hvars Hshape]; split.
  - rewrite cty_open_vars in Hvars.
    apply lvars_open_subseteq_iff in Hvars. exact Hvars.
  - apply context_ty_shape_ok_open in Hshape. exact Hshape.
  - rewrite cty_open_vars.
    apply lvars_open_subseteq_iff. exact Hvars.
  - apply context_ty_shape_ok_open. exact Hshape.
Qed.

Lemma cty_lc_at_mono_depth d d' τ :
  d <= d' ->
  cty_lc_at d τ ->
  cty_lc_at d' τ.
Proof.
  induction τ in d, d' |- *; cbn [cty_lc_at]; intros Hdd Hlc.
  - intros k Hk. specialize (Hlc k Hk). lia.
  - intros k Hk. specialize (Hlc k Hk). lia.
  - destruct Hlc as [H1 H2]. split; eauto.
  - destruct Hlc as [H1 H2]. split; eauto.
  - destruct Hlc as [H1 H2]. split; eauto.
  - destruct Hlc as [H1 H2]. split.
    + eapply IHτ1; [exact Hdd|exact H1].
    + eapply (IHτ2 (S d) (S d')); [lia|exact H2].
  - destruct Hlc as [H1 H2]. split.
    + eapply IHτ1; [exact Hdd|exact H1].
    + eapply (IHτ2 (S d) (S d')); [lia|exact H2].
Qed.

Lemma wf_context_ty_at_lc d D τ :
  wf_context_ty_at d D τ ->
  cty_lc_at d τ.
Proof.
  induction τ in d, D |- *; cbn [wf_context_ty_at cty_lc_at]; intros Hwf;
    try solve [apply lvars_wf_at_lc with (D := D); exact Hwf].
  - destruct Hwf as [H1 [H2 _]]. repeat split; eauto.
  - destruct Hwf as [H1 [H2 _]]. repeat split; eauto.
  - destruct Hwf as [H1 [H2 _]]. repeat split; eauto.
  - destruct Hwf as [H1 H2]. repeat split; eauto.
  - destruct Hwf as [H1 H2]. split.
    + eapply (cty_lc_at_mono_depth 0 d); [lia|].
      eapply IHτ1. exact H1.
    + eapply IHτ2. exact H2.
Qed.

Lemma basic_context_ty_lc D τ :
  basic_context_ty D τ ->
  lc_context_ty τ.
Proof.
  rewrite basic_context_ty_iff_wf_context_ty_at.
  apply wf_context_ty_at_lc.
Qed.

Lemma lvars_lc_at_depth_bv_empty d L :
  lvars_lc_at d L ->
  lvars_bv (lvars_at_depth d L) = ∅.
Proof.
  intros Hlc.
  apply set_eq. intros k.
  rewrite elem_of_empty, lvars_bv_elem, lvars_at_depth_elem.
  split; [|set_solver].
  intros [v [Hv Hdepth]].
  destruct v as [n|x]; cbn [logic_var_at_depth] in Hdepth.
  - destruct (decide (d <= n)) as [Hdn|Hdn]; [|discriminate].
    exfalso. specialize (Hlc n ltac:(apply lvars_bv_elem; exact Hv)).
    lia.
  - discriminate.
Qed.

Lemma cty_lc_at_lvars_bv_empty d τ :
  cty_lc_at d τ ->
  lvars_bv (context_ty_lvars_at d τ) = ∅.
Proof.
  induction τ in d |- *; cbn [cty_lc_at context_ty_lvars_at]; intros Hlc.
  - apply lvars_lc_at_depth_bv_empty. exact Hlc.
  - apply lvars_lc_at_depth_bv_empty. exact Hlc.
  - destruct Hlc as [H1 H2].
    rewrite lvars_bv_union, IHτ1, IHτ2 by assumption. set_solver.
  - destruct Hlc as [H1 H2].
    rewrite lvars_bv_union, IHτ1, IHτ2 by assumption. set_solver.
  - destruct Hlc as [H1 H2].
    rewrite lvars_bv_union, IHτ1, IHτ2 by assumption. set_solver.
  - destruct Hlc as [H1 H2].
    rewrite lvars_bv_union, IHτ1, IHτ2 by assumption. set_solver.
  - destruct Hlc as [H1 H2].
    rewrite lvars_bv_union, IHτ1, IHτ2 by assumption. set_solver.
Qed.

Lemma lc_context_ty_lvars_bv_empty τ :
  lc_context_ty τ ->
  lvars_bv (context_ty_lvars τ) = ∅.
Proof.
  apply cty_lc_at_lvars_bv_empty.
Qed.

Lemma lc_context_ty_lvars_subset_atoms τ :
  lc_context_ty τ ->
  context_ty_lvars τ ⊆ lvars_of_atoms (fv_cty τ).
Proof.
  intros Hlc.
  apply lvars_bv_empty_subset_of_atoms_fv.
  apply lc_context_ty_lvars_bv_empty. exact Hlc.
Qed.

Lemma wf_context_ty_at_fv_subset d D τ :
  wf_context_ty_at d D τ ->
  fv_cty τ ⊆ D.
Proof.
  intros Hwf.
  rewrite <- (context_ty_lvars_fv_at d τ).
  induction τ in d, D, Hwf |- *; cbn [context_ty_lvars_at wf_context_ty_at] in *.
  - rewrite lvars_fv_lvars_at_depth.
    eapply lvars_wf_at_fv_subset. exact Hwf.
  - rewrite lvars_fv_lvars_at_depth.
    eapply lvars_wf_at_fv_subset. exact Hwf.
  - destruct Hwf as [H1 [H2 _]].
    rewrite lvars_fv_union. set_solver.
  - destruct Hwf as [H1 [H2 _]].
    rewrite lvars_fv_union. set_solver.
  - destruct Hwf as [H1 [H2 _]].
    rewrite lvars_fv_union. set_solver.
  - destruct Hwf as [H1 H2].
    rewrite lvars_fv_union.
    pose proof (IHτ1 d D H1).
    pose proof (IHτ2 (S d) D H2).
    set_solver.
  - destruct Hwf as [H1 H2].
    rewrite lvars_fv_union.
    pose proof (IHτ1 0 ∅ H1).
    pose proof (IHτ2 (S d) D H2).
    rewrite !context_ty_lvars_fv_at in *.
    set_solver.
Qed.

Lemma basic_context_ty_fv_subset D τ :
  basic_context_ty D τ ->
  fv_cty τ ⊆ D.
Proof.
  apply wf_context_ty_at_fv_subset.
Qed.

Lemma wf_context_ty_at_to_lvars_shape d D τ :
  wf_context_ty_at d D τ ->
  context_ty_lvars_at d τ ⊆ lvars_of_atoms D /\ context_ty_shape_ok τ.
Proof.
  intros Hwf. split.
  - intros [k|x] Hv.
    + exfalso.
      pose proof (cty_lc_at_lvars_bv_empty d τ
        (wf_context_ty_at_lc d D τ Hwf)) as Hbv.
      assert (k ∈ lvars_bv (context_ty_lvars_at d τ)) as Hk
        by (apply lvars_bv_elem; exact Hv).
      rewrite Hbv in Hk. set_solver.
    + unfold lvars_of_atoms. apply elem_of_map.
      exists x. split; [reflexivity|].
      pose proof (wf_context_ty_at_fv_subset d D τ Hwf) as Hfv.
      apply Hfv.
      rewrite <- (context_ty_lvars_fv_at d τ).
      apply lvars_fv_elem. exact Hv.
  - induction τ in d, D, Hwf |- *; cbn [wf_context_ty_at context_ty_shape_ok] in *;
      try tauto.
    all: repeat match goal with
    | H : _ /\ _ |- _ => destruct H
    | H : _ /\ _ /\ _ |- _ => destruct H as [? [? ?]]
    end; repeat split; eauto.
Qed.

Lemma basic_context_ty_to_lvars D τ :
  basic_context_ty D τ ->
  basic_context_ty_lvars (lvars_of_atoms D) τ.
Proof.
  intros Hwf.
  unfold basic_context_ty_lvars, context_ty_lvars.
  apply wf_context_ty_at_to_lvars_shape. exact Hwf.
Qed.

Lemma basic_context_ty_lvar_cty_vars_equiv D τ1 τ2 :
  τ1 ≡τv τ2 ->
  basic_context_ty D τ1 ->
  basic_context_ty D τ2.
Proof.
  revert τ2.
  enough (forall d D τ1 τ2,
    τ1 ≡τv τ2 ->
    wf_context_ty_at d D τ1 ->
    wf_context_ty_at d D τ2) as Hgen.
  {
    intros τ2 Heq Hwf.
    apply basic_context_ty_iff_wf_context_ty_at.
    eapply Hgen; [exact Heq|].
    apply basic_context_ty_iff_wf_context_ty_at. exact Hwf.
  }
  clear D τ1.
  intros d D τ1.
  induction τ1 in d, D |- *; intros τ2 Heq Hwf;
    destruct τ2; cbn [cty_vars_equiv wf_context_ty_at] in *;
    try contradiction.
  - destruct Heq as [_ Hvars]. rewrite <- Hvars. exact Hwf.
  - destruct Heq as [_ Hvars]. rewrite <- Hvars. exact Hwf.
  - destruct Heq as [Heq1 Heq2].
    destruct Hwf as [H1 [H2 Herase]]. repeat split.
    + eapply IHτ1_1; eauto.
    + eapply IHτ1_2; eauto.
    + rewrite <- (cty_vars_equiv_erase _ _ Heq1).
      rewrite <- (cty_vars_equiv_erase _ _ Heq2).
      exact Herase.
  - destruct Heq as [Heq1 Heq2].
    destruct Hwf as [H1 [H2 Herase]]. repeat split.
    + eapply IHτ1_1; eauto.
    + eapply IHτ1_2; eauto.
    + rewrite <- (cty_vars_equiv_erase _ _ Heq1).
      rewrite <- (cty_vars_equiv_erase _ _ Heq2).
      exact Herase.
  - destruct Heq as [Heq1 Heq2].
    destruct Hwf as [H1 [H2 Herase]]. repeat split.
    + eapply IHτ1_1; eauto.
    + eapply IHτ1_2; eauto.
    + rewrite <- (cty_vars_equiv_erase _ _ Heq1).
      rewrite <- (cty_vars_equiv_erase _ _ Heq2).
      exact Herase.
  - destruct Heq as [Heq1 Heq2].
    destruct Hwf as [H1 H2]. split.
    + eapply IHτ1_1; eauto.
    + eapply IHτ1_2; eauto.
  - destruct Heq as [Heq1 Heq2].
    destruct Hwf as [H1 H2]. split.
    + eapply IHτ1_1; eauto.
    + eapply IHτ1_2; eauto.
Qed.

Lemma wf_context_ty_at_drop_fresh d D x τ :
  x ∉ fv_cty τ ->
  wf_context_ty_at d (D ∪ {[x]}) τ ->
  wf_context_ty_at d D τ.
Proof.
  induction τ in d |- *; cbn [wf_context_ty_at]; intros Hfresh Hwf.
  - eapply lvars_wf_at_drop_fresh; [|exact Hwf].
    intros Hbad. apply Hfresh.
    unfold fv_cty, context_ty_lvars. cbn [context_ty_lvars_at].
    rewrite lvars_fv_lvars_at_depth. exact Hbad.
  - eapply lvars_wf_at_drop_fresh; [|exact Hwf].
    intros Hbad. apply Hfresh.
    unfold fv_cty, context_ty_lvars. cbn [context_ty_lvars_at].
    rewrite lvars_fv_lvars_at_depth. exact Hbad.
  - destruct Hwf as [H1 [H2 Herase]]. repeat split.
    + eapply IHτ1; [|exact H1].
      intros Hbad. apply Hfresh. unfold fv_cty, context_ty_lvars in *.
      cbn [context_ty_lvars_at] in *. rewrite lvars_fv_union.
      apply elem_of_union_l. rewrite context_ty_lvars_fv_at. exact Hbad.
    + eapply IHτ2; [|exact H2].
      intros Hbad. apply Hfresh. unfold fv_cty, context_ty_lvars in *.
      cbn [context_ty_lvars_at] in *. rewrite lvars_fv_union.
      apply elem_of_union_r. rewrite context_ty_lvars_fv_at. exact Hbad.
    + exact Herase.
  - destruct Hwf as [H1 [H2 Herase]]. repeat split.
    + eapply IHτ1; [|exact H1].
      intros Hbad. apply Hfresh. unfold fv_cty, context_ty_lvars in *.
      cbn [context_ty_lvars_at] in *. rewrite lvars_fv_union.
      apply elem_of_union_l. rewrite context_ty_lvars_fv_at. exact Hbad.
    + eapply IHτ2; [|exact H2].
      intros Hbad. apply Hfresh. unfold fv_cty, context_ty_lvars in *.
      cbn [context_ty_lvars_at] in *. rewrite lvars_fv_union.
      apply elem_of_union_r. rewrite context_ty_lvars_fv_at. exact Hbad.
    + exact Herase.
  - destruct Hwf as [H1 [H2 Herase]]. repeat split.
    + eapply IHτ1; [|exact H1].
      intros Hbad. apply Hfresh. unfold fv_cty, context_ty_lvars in *.
      cbn [context_ty_lvars_at] in *. rewrite lvars_fv_union.
      apply elem_of_union_l. rewrite context_ty_lvars_fv_at. exact Hbad.
    + eapply IHτ2; [|exact H2].
      intros Hbad. apply Hfresh. unfold fv_cty, context_ty_lvars in *.
      cbn [context_ty_lvars_at] in *. rewrite lvars_fv_union.
      apply elem_of_union_r. rewrite context_ty_lvars_fv_at. exact Hbad.
    + exact Herase.
  - destruct Hwf as [H1 H2]. split.
    + eapply IHτ1; [|exact H1].
      intros Hbad. apply Hfresh. unfold fv_cty, context_ty_lvars in *.
      cbn [context_ty_lvars_at] in *. rewrite lvars_fv_union.
      apply elem_of_union_l. rewrite context_ty_lvars_fv_at. exact Hbad.
    + eapply IHτ2; [|exact H2].
      intros Hbad. apply Hfresh. unfold fv_cty, context_ty_lvars in *.
      cbn [context_ty_lvars_at] in *. rewrite lvars_fv_union.
      apply elem_of_union_r. rewrite context_ty_lvars_fv_at. exact Hbad.
  - destruct Hwf as [H1 H2]. split.
    + exact H1.
    + eapply IHτ2; [|exact H2].
      intros Hbad. apply Hfresh. unfold fv_cty, context_ty_lvars in *.
      cbn [context_ty_lvars_at] in *. rewrite lvars_fv_union.
      apply elem_of_union_r. rewrite context_ty_lvars_fv_at. exact Hbad.
Qed.

Lemma basic_context_ty_drop_fresh D x τ :
  x ∉ fv_cty τ ->
  basic_context_ty (D ∪ {[x]}) τ ->
  basic_context_ty D τ.
Proof.
  apply wf_context_ty_at_drop_fresh.
Qed.

Lemma basic_context_ty_drop_insert_fresh
    (Σ : gmap atom ty) x T τ :
  x ∉ dom Σ ->
  x ∉ fv_cty τ ->
  basic_context_ty (dom (<[x := T]> Σ)) τ ->
  basic_context_ty (dom Σ) τ.
Proof.
  intros Hx Hfresh Hbasic.
  apply (basic_context_ty_drop_fresh (dom Σ) x τ); [exact Hfresh|].
  replace (dom Σ ∪ {[x]}) with ({[x]} ∪ dom Σ) by set_solver.
  rewrite <- (dom_insert_L (M := gmap atom) (D := gset atom) Σ x T).
  exact Hbasic.
Qed.


Lemma cty_lc_at_open_fresh_at d k x τ :
  cty_lc_at d τ ->
  x ∉ fv_cty τ ->
  {d + k ~> x} τ = τ.
Proof.
  induction τ in d, k |- *; cbn [cty_lc_at];
    intros Hlc Hfresh.
  - change ({d + k ~> x} CTOver b φ) with
      (cty_open (d + k) x (CTOver b φ)).
    cbn [cty_open].
    rewrite qual_open_atom_fresh_index.
    + reflexivity.
    + intros Hbad. cbn [qual_bvars qual_vars] in Hbad.
      specialize (Hlc (S (d + k)) Hbad). lia.
    + unfold qual_dom. intros Hbad. apply Hfresh.
      unfold fv_cty, context_ty_lvars. cbn [context_ty_lvars_at].
      rewrite lvars_fv_lvars_at_depth. exact Hbad.
  - change ({d + k ~> x} CTUnder b φ) with
      (cty_open (d + k) x (CTUnder b φ)).
    cbn [cty_open].
    rewrite qual_open_atom_fresh_index.
    + reflexivity.
    + intros Hbad. cbn [qual_bvars qual_vars] in Hbad.
      specialize (Hlc (S (d + k)) Hbad). lia.
    + unfold qual_dom. intros Hbad. apply Hfresh.
      unfold fv_cty, context_ty_lvars. cbn [context_ty_lvars_at].
      rewrite lvars_fv_lvars_at_depth. exact Hbad.
  - destruct Hlc as [H1 H2].
    change ({d + k ~> x} CTInter τ1 τ2) with
      (cty_open (d + k) x (CTInter τ1 τ2)).
    cbn [cty_open].
    rewrite IHτ1, IHτ2 by (try assumption; unfold fv_cty, context_ty_lvars in *;
      cbn [context_ty_lvars_at] in *; rewrite lvars_fv_union in *; set_solver).
    reflexivity.
  - destruct Hlc as [H1 H2].
    change ({d + k ~> x} CTUnion τ1 τ2) with
      (cty_open (d + k) x (CTUnion τ1 τ2)).
    cbn [cty_open].
    rewrite IHτ1, IHτ2 by (try assumption; unfold fv_cty, context_ty_lvars in *;
      cbn [context_ty_lvars_at] in *; rewrite lvars_fv_union in *; set_solver).
    reflexivity.
  - destruct Hlc as [H1 H2].
    change ({d + k ~> x} CTSum τ1 τ2) with
      (cty_open (d + k) x (CTSum τ1 τ2)).
    cbn [cty_open].
    rewrite IHτ1, IHτ2 by (try assumption; unfold fv_cty, context_ty_lvars in *;
      cbn [context_ty_lvars_at] in *; rewrite lvars_fv_union in *; set_solver).
    reflexivity.
  - destruct Hlc as [H1 H2].
    change ({d + k ~> x} CTArrow τ1 τ2) with
      (cty_open (d + k) x (CTArrow τ1 τ2)).
    cbn [cty_open].
    assert (Hfresh1 : x ∉ fv_cty τ1).
    { intros Hbad. apply Hfresh. unfold fv_cty, context_ty_lvars.
      cbn [context_ty_lvars_at]. rewrite lvars_fv_union.
      apply elem_of_union_l. rewrite context_ty_lvars_fv_at. exact Hbad. }
    assert (Hfresh2 : x ∉ fv_cty τ2).
    { intros Hbad. apply Hfresh. unfold fv_cty, context_ty_lvars.
      cbn [context_ty_lvars_at]. rewrite lvars_fv_union.
      apply elem_of_union_r. rewrite context_ty_lvars_fv_at. exact Hbad. }
    rewrite IHτ1 by assumption.
    replace (S (d + k)) with (S d + k) by lia.
    rewrite IHτ2 by assumption.
    reflexivity.
  - destruct Hlc as [H1 H2].
    change ({d + k ~> x} CTWand τ1 τ2) with
      (cty_open (d + k) x (CTWand τ1 τ2)).
    cbn [cty_open].
    assert (Hfresh1 : x ∉ fv_cty τ1).
    { intros Hbad. apply Hfresh. unfold fv_cty, context_ty_lvars.
      cbn [context_ty_lvars_at]. rewrite lvars_fv_union.
      apply elem_of_union_l. rewrite context_ty_lvars_fv_at. exact Hbad. }
    assert (Hfresh2 : x ∉ fv_cty τ2).
    { intros Hbad. apply Hfresh. unfold fv_cty, context_ty_lvars.
      cbn [context_ty_lvars_at]. rewrite lvars_fv_union.
      apply elem_of_union_r. rewrite context_ty_lvars_fv_at. exact Hbad. }
    rewrite IHτ1 by assumption.
    replace (S (d + k)) with (S d + k) by lia.
    rewrite IHτ2 by assumption.
    reflexivity.
Qed.

Lemma lc_context_ty_open_fresh k x τ :
  lc_context_ty τ ->
  x ∉ fv_cty τ ->
  {k ~> x} τ = τ.
Proof.
  intros Hlc Hfresh.
  replace k with (0 + k) at 1 by lia.
  apply cty_lc_at_open_fresh_at; assumption.
Qed.

Lemma wf_context_ty_at_open_at d D τ x :
  x ∉ D ->
  wf_context_ty_at (S d) D τ ->
  wf_context_ty_at d (D ∪ {[x]}) ({d ~> x} τ).
Proof.
  induction τ in d |- *; cbn [wf_context_ty_at]; intros Hx Hwf.
  - change ({d ~> x} CTOver b φ) with (cty_open d x (CTOver b φ)).
    cbn [cty_open wf_context_ty_at].
    rewrite qual_open_atom_vars.
    apply lvars_wf_at_open_at; assumption.
  - change ({d ~> x} CTUnder b φ) with (cty_open d x (CTUnder b φ)).
    cbn [cty_open wf_context_ty_at].
    rewrite qual_open_atom_vars.
    apply lvars_wf_at_open_at; assumption.
  - change ({d ~> x} CTInter τ1 τ2) with (cty_open d x (CTInter τ1 τ2)).
    cbn [cty_open wf_context_ty_at] in *.
    destruct Hwf as [H1 [H2 Herase]]. repeat split.
    + apply IHτ1; assumption.
    + apply IHτ2; assumption.
    + rewrite !cty_open_preserves_erasure. exact Herase.
  - change ({d ~> x} CTUnion τ1 τ2) with (cty_open d x (CTUnion τ1 τ2)).
    cbn [cty_open wf_context_ty_at] in *.
    destruct Hwf as [H1 [H2 Herase]]. repeat split.
    + apply IHτ1; assumption.
    + apply IHτ2; assumption.
    + rewrite !cty_open_preserves_erasure. exact Herase.
  - change ({d ~> x} CTSum τ1 τ2) with (cty_open d x (CTSum τ1 τ2)).
    cbn [cty_open wf_context_ty_at] in *.
    destruct Hwf as [H1 [H2 Herase]]. repeat split.
    + apply IHτ1; assumption.
    + apply IHτ2; assumption.
    + rewrite !cty_open_preserves_erasure. exact Herase.
  - change ({d ~> x} CTArrow τ1 τ2) with (cty_open d x (CTArrow τ1 τ2)).
    cbn [cty_open wf_context_ty_at] in *.
    destruct Hwf as [H1 H2]. split.
    + apply IHτ1; assumption.
    + apply IHτ2; assumption.
  - change ({d ~> x} CTWand τ1 τ2) with (cty_open d x (CTWand τ1 τ2)).
    cbn [cty_open wf_context_ty_at] in *.
    destruct Hwf as [H1 H2]. split.
    + replace (cty_open d x τ1) with τ1.
      * exact H1.
      * symmetry. apply lc_context_ty_open_fresh.
        -- eapply wf_context_ty_at_lc. exact H1.
        -- pose proof (wf_context_ty_at_fv_subset 0 ∅ τ1 H1). set_solver.
    + apply IHτ2; assumption.
Qed.

Lemma basic_context_ty_open_body D τ x :
  x ∉ D ->
  wf_context_ty_at 1 D τ ->
  basic_context_ty (D ∪ {[x]}) ({0 ~> x} τ).
Proof.
  intros Hx Hwf.
  apply basic_context_ty_iff_wf_context_ty_at.
  apply wf_context_ty_at_open_at; assumption.
Qed.

Lemma basic_context_ty_open_body_cofinite D τ (L0 : aset) :
  wf_context_ty_at 1 D τ ->
  exists L,
    L0 ⊆ L /\
    forall y,
      y ∉ L ->
      basic_context_ty (D ∪ {[y]}) ({0 ~> y} τ).
Proof.
  intros Hwf.
  exists (L0 ∪ D). split; [set_solver|].
  intros y Hy.
  apply basic_context_ty_open_body; [set_solver|exact Hwf].
Qed.

Lemma basic_context_ty_arrow_inv D τx τ :
  basic_context_ty D (CTArrow τx τ) ->
  basic_context_ty D τx /\ wf_context_ty_at 1 D τ.
Proof.
  rewrite basic_context_ty_iff_wf_context_ty_at.
  cbn [wf_context_ty_at].
  intros [Hτx Hτ]. split; [|exact Hτ].
  apply basic_context_ty_iff_wf_context_ty_at. exact Hτx.
Qed.

Lemma basic_context_ty_wand_inv D τx τ :
  basic_context_ty D (CTWand τx τ) ->
  basic_context_ty ∅ τx /\ wf_context_ty_at 1 D τ.
Proof.
  rewrite basic_context_ty_iff_wf_context_ty_at.
  cbn [wf_context_ty_at].
  intros [Hτx Hτ]. split; [|exact Hτ].
  apply basic_context_ty_iff_wf_context_ty_at. exact Hτx.
Qed.

Lemma basic_context_ty_open_arrow_body_cofinite
    (Δ : gmap atom ty) τx τ (L0 : gset atom) :
  basic_context_ty (dom Δ) (CTArrow τx τ) ->
  exists L,
    L0 ⊆ L /\
    forall y,
      y ∉ L ->
      basic_context_ty (dom (<[y := erase_ty τx]> Δ)) ({0 ~> y} τ).
Proof.
  intros Hbasic.
  destruct (basic_context_ty_arrow_inv _ _ _ Hbasic) as [_ Hbody].
  destruct (basic_context_ty_open_body_cofinite (dom Δ) τ L0 Hbody)
    as [L [HL Hopen]].
  exists L. split; [exact HL|].
  intros y Hy.
  specialize (Hopen y Hy).
  replace (dom (<[y := erase_ty τx]> Δ)) with (dom Δ ∪ {[y]}).
  - exact Hopen.
  - transitivity ({[y]} ∪ dom Δ).
    + set_solver.
    + symmetry. apply (dom_insert_L (M := gmap atom) (D := gset atom)).
Qed.

Lemma basic_context_ty_open_wand_body_cofinite
    (Δ : gmap atom ty) τx τ (L0 : gset atom) :
  basic_context_ty (dom Δ) (CTWand τx τ) ->
  exists L,
    L0 ⊆ L /\
    forall y,
      y ∉ L ->
      basic_context_ty (dom (<[y := erase_ty τx]> Δ)) ({0 ~> y} τ).
Proof.
  intros Hbasic.
  destruct (basic_context_ty_wand_inv _ _ _ Hbasic) as [_ Hbody].
  destruct (basic_context_ty_open_body_cofinite (dom Δ) τ L0 Hbody)
    as [L [HL Hopen]].
  exists L. split; [exact HL|].
  intros y Hy.
  specialize (Hopen y Hy).
  replace (dom (<[y := erase_ty τx]> Δ)) with (dom Δ ∪ {[y]}).
  - exact Hopen.
  - transitivity ({[y]} ∪ dom Δ).
    + set_solver.
    + symmetry. apply (dom_insert_L (M := gmap atom) (D := gset atom)).
Qed.

Lemma basic_context_ty_shift D τ k :
  basic_context_ty D τ ->
  basic_context_ty D (cty_shift k τ).
Proof.
  rewrite !basic_context_ty_iff_wf_context_ty_at.
  intros H.
  eapply wf_context_ty_at_shift; [lia|exact H].
Qed.

(** ** Context Formation *)


Fixpoint basic_ctx (D : aset) (Γ : ctx) : Prop :=
  match Γ with
  | CtxEmpty => True
  | CtxBind x τ =>
      x ∉ D /\ basic_context_ty D τ
  | CtxComma Γ1 Γ2 =>
      basic_ctx D Γ1 /\
      basic_ctx (D ∪ ctx_dom Γ1) Γ2 /\
      ctx_dom Γ1 ## ctx_dom Γ2
  | CtxStar Γ1 Γ2 =>
      basic_ctx D Γ1 /\
      basic_ctx D Γ2 /\
      ctx_dom Γ1 ## ctx_dom Γ2
  | CtxSum Γ1 Γ2 =>
      basic_ctx D Γ1 /\
      basic_ctx D Γ2 /\
      ctx_dom Γ1 = ctx_dom Γ2 /\
      erase_ctx Γ1 = erase_ctx Γ2
  end.

#[global] Instance scoped_ctx : ScopedIn ctx := basic_ctx.

Notation "D '⊢sΓ' Γ" := (basic_ctx D Γ)
  (at level 40, Γ at level 40, only printing).

Lemma scoped_ctx_iff D Γ :
  D ⊢s Γ <-> basic_ctx D Γ.
Proof. reflexivity. Qed.

Lemma basic_ctx_weaken_fresh D E Γ :
  D ⊆ E ->
  ctx_dom Γ ## E ->
  basic_ctx D Γ ->
  basic_ctx E Γ.
Proof.
  induction Γ in D, E |- *; cbn [basic_ctx ctx_dom]; intros HDE Hdom Hbasic.
  - exact I.
  - destruct Hbasic as [Hx Hτ]. split.
    + set_solver.
    + eapply basic_context_ty_mono; [exact HDE|exact Hτ].
  - destruct Hbasic as [H1 [H2 Hdisj]]. repeat split.
    + eapply IHΓ1; [exact HDE|set_solver|exact H1].
    + eapply (IHΓ2 (D ∪ ctx_dom Γ1) (E ∪ ctx_dom Γ1)).
      * set_solver.
      * set_solver.
      * exact H2.
    + exact Hdisj.
  - destruct Hbasic as [H1 [H2 Hdisj]]. repeat split.
    + eapply IHΓ1; [exact HDE|set_solver|exact H1].
    + eapply IHΓ2; [exact HDE|set_solver|exact H2].
    + exact Hdisj.
  - destruct Hbasic as [H1 [H2 [Hdom12 Herase]]]. repeat split.
    + eapply IHΓ1; [exact HDE|set_solver|exact H1].
    + eapply IHΓ2; [exact HDE|set_solver|exact H2].
    + exact Hdom12.
    + exact Herase.
Qed.

Lemma basic_ctx_fv_subset D Γ :
  basic_ctx D Γ ->
  ctx_fv Γ ⊆ D.
Proof.
  induction Γ in D |- *; cbn [basic_ctx ctx_fv ctx_dom]; intros Hbasic.
  - set_solver.
  - destruct Hbasic as [_ Hτ].
    apply basic_context_ty_fv_subset. exact Hτ.
  - destruct Hbasic as [H1 [H2 _]].
    specialize (IHΓ1 D H1).
    specialize (IHΓ2 (D ∪ ctx_dom Γ1) H2).
    set_solver.
  - destruct Hbasic as [H1 [H2 _]].
    specialize (IHΓ1 D H1).
    specialize (IHΓ2 D H2).
    set_solver.
  - destruct Hbasic as [H1 [H2 [_ _]]].
    specialize (IHΓ1 D H1).
    specialize (IHΓ2 D H2).
    set_solver.
Qed.

Lemma basic_ctx_fv_subset_weak D Γ :
  basic_ctx D Γ ->
  ctx_fv Γ ⊆ D ∪ ctx_dom Γ.
Proof.
  intros Hbasic.
  pose proof (basic_ctx_fv_subset D Γ Hbasic). set_solver.
Qed.

Lemma basic_ctx_dom_fresh D Γ :
  basic_ctx D Γ ->
  ctx_dom Γ ## D.
Proof.
  induction Γ in D |- *; cbn [basic_ctx ctx_dom]; intros Hbasic.
  - set_solver.
  - destruct Hbasic as [Hx _]. set_solver.
  - destruct Hbasic as [H1 [H2 Hdisj]].
    specialize (IHΓ1 D H1).
    specialize (IHΓ2 (D ∪ ctx_dom Γ1) H2).
    set_solver.
  - destruct Hbasic as [H1 [H2 _]].
    specialize (IHΓ1 D H1).
    specialize (IHΓ2 D H2).
    set_solver.
  - destruct Hbasic as [H1 [H2 [_ _]]].
    specialize (IHΓ1 D H1).
    specialize (IHΓ2 D H2).
    set_solver.
Qed.

Lemma basic_ctx_dom_fv_disjoint D Γ :
  basic_ctx D Γ ->
  ctx_dom Γ ## ctx_fv Γ.
Proof.
  intros Hbasic.
  pose proof (basic_ctx_dom_fresh D Γ Hbasic).
  pose proof (basic_ctx_fv_subset D Γ Hbasic).
  set_solver.
Qed.

Lemma basic_ctx_bind_lc D x τ :
  basic_ctx D (CtxBind x τ) ->
  lc_context_ty τ.
Proof.
  intros [_ Hτ]. apply (basic_context_ty_lc D). exact Hτ.
Qed.

Lemma basic_ctx_lc D Γ :
  basic_ctx D Γ ->
  forall x τ, Γ = CtxBind x τ -> lc_context_ty τ.
Proof.
  intros Hbasic x τ ->.
  apply (basic_ctx_bind_lc D x τ). exact Hbasic.
Qed.

Lemma basic_ctx_erase_dom D Γ :
  basic_ctx D Γ ->
  dom (erase_ctx Γ) = ctx_dom Γ.
Proof.
  induction Γ in D |- *; cbn [basic_ctx erase_ctx ctx_dom]; intros Hbasic.
  - rewrite dom_empty_L. reflexivity.
  - apply (dom_singleton_L (M := gmap atom) (D := gset atom)).
  - destruct Hbasic as [H1 [H2 _]].
    change (dom (erase_ctx Γ1 ∪ erase_ctx Γ2) = ctx_dom Γ1 ∪ ctx_dom Γ2).
    transitivity (dom (erase_ctx Γ1) ∪ dom (erase_ctx Γ2)).
    + apply (dom_union_L (M := gmap atom) (D := gset atom)).
    + rewrite (IHΓ1 D) by exact H1.
      rewrite (IHΓ2 (D ∪ ctx_dom Γ1)) by exact H2.
      reflexivity.
  - destruct Hbasic as [H1 [H2 _]].
    change (dom (erase_ctx Γ1 ∪ erase_ctx Γ2) = ctx_dom Γ1 ∪ ctx_dom Γ2).
    transitivity (dom (erase_ctx Γ1) ∪ dom (erase_ctx Γ2)).
    + apply (dom_union_L (M := gmap atom) (D := gset atom)).
    + rewrite (IHΓ1 D) by exact H1.
      rewrite (IHΓ2 D) by exact H2.
      reflexivity.
  - destruct Hbasic as [H1 [_ [Hdom _]]].
    rewrite (IHΓ1 D) by exact H1.
    set_solver.
Qed.

Lemma basic_ctx_empty_fv Γ :
  basic_ctx ∅ Γ ->
  ctx_fv Γ ⊆ ctx_dom Γ.
Proof.
  intros Hbasic.
  pose proof (basic_ctx_fv_subset ∅ Γ Hbasic).
  set_solver.
Qed.

(** ** Basic Qualifier Formation *)


Definition basic_qualifier (D : aset) (q : type_qualifier) : Prop :=
  lvars_wf_at 0 D (qual_vars q).

Definition basic_qualifier_body (D : aset) (q : type_qualifier) : Prop :=
  lvars_wf_at 1 D (qual_vars q).

Lemma basic_qualifier_lc D q :
  basic_qualifier D q ->
  lc_qualifier q.
Proof.
  intros Hwf [k|x] Hv; cbn [lc_logic_var_key].
  - exfalso.
    specialize (Hwf (LVBound k) Hv). cbn [lvar_wf_at] in Hwf. lia.
  - exact I.
Qed.

Lemma basic_qualifier_body_lc D q :
  basic_qualifier_body D q ->
  body_qualifier q.
Proof.
  intros Hwf.
  exists D. intros x Hx.
  apply basic_qualifier_lc with (D := D ∪ {[x]}).
  unfold basic_qualifier.
  rewrite qual_open_atom_vars.
  apply lvars_wf_at_open_body; assumption.
Qed.

Lemma basic_qualifier_fv_subset D q :
  basic_qualifier D q ->
  qual_dom q ⊆ D.
Proof.
  apply lvars_wf_at_fv_subset.
Qed.

Lemma basic_qualifier_body_fv_subset D q :
  basic_qualifier_body D q ->
  qual_dom q ⊆ D.
Proof.
  apply lvars_wf_at_fv_subset.
Qed.

Lemma basic_qualifier_body_top D :
  basic_qualifier_body D qual_top.
Proof.
  unfold basic_qualifier_body, qual_top. cbn [qual_vars qual_lvars].
  intros v Hv. set_solver.
Qed.

Lemma basic_context_ty_over D b q :
  basic_qualifier_body D q ->
  basic_context_ty D (CTOver b q).
Proof.
  intros Hq.
  apply basic_context_ty_iff_wf_context_ty_at.
  exact Hq.
Qed.

Lemma basic_context_ty_under D b q :
  basic_qualifier_body D q ->
  basic_context_ty D (CTUnder b q).
Proof.
  intros Hq.
  apply basic_context_ty_iff_wf_context_ty_at.
  exact Hq.
Qed.

Lemma basic_context_ty_inter D τ1 τ2 :
  basic_context_ty D τ1 ->
  basic_context_ty D τ2 ->
  erase_ty τ1 = erase_ty τ2 ->
  basic_context_ty D (CTInter τ1 τ2).
Proof.
  intros H1 H2 Herase.
  apply basic_context_ty_iff_wf_context_ty_at.
  cbn [wf_context_ty_at]. repeat split; try assumption;
    apply basic_context_ty_iff_wf_context_ty_at; assumption.
Qed.

Lemma basic_ctx_empty D :
  basic_ctx D CtxEmpty.
Proof.
  exact I.
Qed.

Lemma basic_ctx_bind D x τ :
  x ∉ D ->
  basic_context_ty D τ ->
  basic_ctx D (CtxBind x τ).
Proof.
  intros Hx Hτ. split; assumption.
Qed.

Lemma basic_ctx_star D Γ1 Γ2 :
  basic_ctx D Γ1 ->
  basic_ctx D Γ2 ->
  ctx_dom Γ1 ## ctx_dom Γ2 ->
  basic_ctx D (CtxStar Γ1 Γ2).
Proof.
  intros H1 H2 Hdisj. repeat split; assumption.
Qed.

Lemma basic_ctx_sum D Γ1 Γ2 :
  basic_ctx D Γ1 ->
  basic_ctx D Γ2 ->
  ctx_dom Γ1 = ctx_dom Γ2 ->
  erase_ctx Γ1 = erase_ctx Γ2 ->
  basic_ctx D (CtxSum Γ1 Γ2).
Proof.
  intros H1 H2 Hdom Herase. repeat split; assumption.
Qed.

#[global] Instance OpenFv_qualifier : OpenFv atom type_qualifier.
Proof.
  intros q x k.
  cbn [Stale_atom stale_qualifier].
  intros y Hy.
  pose proof (qual_open_atom_dom_subset k x q y Hy) as Hy'.
  apply elem_of_union in Hy' as [Hyq|Hyx].
  - apply elem_of_union_r. exact Hyq.
  - apply elem_of_union_l. exact Hyx.
Qed.

#[global] Instance OpenFv_cty : OpenFv atom context_ty.
Proof.
  intros τ x k.
  cbn [Stale_atom stale_cty_inst].
  intros y Hy.
  pose proof (cty_open_fv_subset k x τ y Hy) as Hy'.
  apply elem_of_union in Hy' as [Hyτ|Hyx].
  - apply elem_of_union_r. exact Hyτ.
  - apply elem_of_union_l. exact Hyx.
Qed.

#[global] Hint Resolve
  basic_context_ty_lc
  basic_context_ty_fv_subset
  basic_qualifier_lc
  basic_qualifier_body_lc
  basic_qualifier_fv_subset
  basic_qualifier_body_fv_subset
  basic_ctx_dom_fresh
  basic_ctx_empty
  basic_ctx_bind
  basic_ctx_star
  basic_ctx_sum
  : type_lang.
