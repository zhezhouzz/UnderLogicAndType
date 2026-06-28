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
  | CTPersist τ =>
      cty_lc_at d τ
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
  | CTPersist τ =>
      context_ty_shape_ok τ
  end.

Definition basic_context_ty_lvars (D : lvset) (τ : context_ty) : Prop :=
  context_ty_lvars τ ⊆ D /\ context_ty_shape_ok τ.

Lemma basic_context_ty_lvars_mono D E τ :
  D ⊆ E ->
  basic_context_ty_lvars D τ ->
  basic_context_ty_lvars E τ.
Proof.
  intros HDE [Hvars Hshape]. split; [set_solver|exact Hshape].
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
  | CTPersist τ =>
      wf_context_ty_at d D τ
  end.

Definition basic_context_ty (D : aset) (τ : context_ty) : Prop :=
  wf_context_ty_at 0 D τ.

Lemma wf_context_ty_at_mono_env d D E τ :
  D ⊆ E ->
  wf_context_ty_at d D τ ->
  wf_context_ty_at d E τ.
Proof.
  induction τ in d, D, E |- *; cbn [wf_context_ty_at]; intros HDE Hwf.
  - eapply lvars_wf_at_mono; eauto.
  - eapply lvars_wf_at_mono; eauto.
  - destruct Hwf as [H1 [H2 Herase]]. repeat split; eauto.
  - destruct Hwf as [H1 [H2 Herase]]. repeat split; eauto.
  - destruct Hwf as [H1 [H2 Herase]]. repeat split; eauto.
  - destruct Hwf as [H1 H2]. split; eauto.
  - destruct Hwf as [H1 H2]. split; eauto.
  - eauto.
Qed.

#[global] Instance lc_cty_inst : Lc context_ty := lc_context_ty.
Arguments lc_cty_inst /.

Class ScopedIn A := scoped_in : aset -> A -> Prop.

#[global] Instance scoped_context_ty : ScopedIn context_ty := basic_context_ty.

Lemma basic_context_ty_iff_wf_context_ty_at D τ :
  basic_context_ty D τ <-> wf_context_ty_at 0 D τ.
Proof.
  reflexivity.
Qed.

Lemma context_ty_shape_ok_open k x τ :
  context_ty_shape_ok (cty_open k x τ) <-> context_ty_shape_ok τ.
Proof.
  induction τ in k |- *; cbn [context_ty_shape_ok cty_open];
    try tauto.
  all: try rewrite !cty_open_preserves_erasure.
  all: try rewrite IHτ1, IHτ2.
  all: try rewrite IHτ.
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
  - eauto.
Qed.

Lemma cty_open_above_lc_fresh d k x τ :
  d <= k ->
  cty_lc_at d τ ->
  x ∉ fv_cty τ ->
  cty_open k x τ = τ.
Proof.
  induction τ in d, k |- *;
    cbn [cty_lc_at cty_open open_one open_cty_atom_inst];
    intros Hdk Hlc Hx.
  - f_equal. apply qual_open_atom_fresh_lc_at.
    + intros n Hn. specialize (Hlc n Hn). lia.
    + unfold fv_cty, context_ty_lvars, qual_dom in Hx.
      cbn [context_ty_lvars_at] in Hx.
      rewrite lvars_fv_lvars_at_depth in Hx. exact Hx.
  - f_equal. apply qual_open_atom_fresh_lc_at.
    + intros n Hn. specialize (Hlc n Hn). lia.
    + unfold fv_cty, context_ty_lvars, qual_dom in Hx.
      cbn [context_ty_lvars_at] in Hx.
      rewrite lvars_fv_lvars_at_depth in Hx. exact Hx.
  - destruct Hlc as [Hlc1 Hlc2]. f_equal.
    + eapply IHτ1; [exact Hdk|exact Hlc1|].
      unfold fv_cty, context_ty_lvars in Hx |- *.
      cbn [context_ty_lvars_at] in Hx.
      rewrite lvars_fv_union, !context_ty_lvars_fv_at in Hx. set_solver.
    + eapply IHτ2; [exact Hdk|exact Hlc2|].
      unfold fv_cty, context_ty_lvars in Hx |- *.
      cbn [context_ty_lvars_at] in Hx.
      rewrite lvars_fv_union, !context_ty_lvars_fv_at in Hx. set_solver.
  - destruct Hlc as [Hlc1 Hlc2]. f_equal.
    + eapply IHτ1; [exact Hdk|exact Hlc1|].
      unfold fv_cty, context_ty_lvars in Hx |- *.
      cbn [context_ty_lvars_at] in Hx.
      rewrite lvars_fv_union, !context_ty_lvars_fv_at in Hx. set_solver.
    + eapply IHτ2; [exact Hdk|exact Hlc2|].
      unfold fv_cty, context_ty_lvars in Hx |- *.
      cbn [context_ty_lvars_at] in Hx.
      rewrite lvars_fv_union, !context_ty_lvars_fv_at in Hx. set_solver.
  - destruct Hlc as [Hlc1 Hlc2]. f_equal.
    + eapply IHτ1; [exact Hdk|exact Hlc1|].
      unfold fv_cty, context_ty_lvars in Hx |- *.
      cbn [context_ty_lvars_at] in Hx.
      rewrite lvars_fv_union, !context_ty_lvars_fv_at in Hx. set_solver.
    + eapply IHτ2; [exact Hdk|exact Hlc2|].
      unfold fv_cty, context_ty_lvars in Hx |- *.
      cbn [context_ty_lvars_at] in Hx.
      rewrite lvars_fv_union, !context_ty_lvars_fv_at in Hx. set_solver.
  - destruct Hlc as [Hlc1 Hlc2]. f_equal.
    + eapply IHτ1; [exact Hdk|exact Hlc1|].
      unfold fv_cty, context_ty_lvars in Hx |- *.
      cbn [context_ty_lvars_at] in Hx.
      rewrite lvars_fv_union, !context_ty_lvars_fv_at in Hx. set_solver.
    + eapply (IHτ2 (S d) (S k)); [lia|exact Hlc2|].
      unfold fv_cty, context_ty_lvars in Hx |- *.
      cbn [context_ty_lvars_at] in Hx.
      rewrite lvars_fv_union, !context_ty_lvars_fv_at in Hx. set_solver.
  - destruct Hlc as [Hlc1 Hlc2]. f_equal.
    + eapply IHτ1; [exact Hdk|exact Hlc1|].
      unfold fv_cty, context_ty_lvars in Hx |- *.
      cbn [context_ty_lvars_at] in Hx.
      rewrite lvars_fv_union, !context_ty_lvars_fv_at in Hx. set_solver.
    + eapply (IHτ2 (S d) (S k)); [lia|exact Hlc2|].
      unfold fv_cty, context_ty_lvars in Hx |- *.
      cbn [context_ty_lvars_at] in Hx.
      rewrite lvars_fv_union, !context_ty_lvars_fv_at in Hx. set_solver.
  - f_equal. eapply IHτ; eauto.
Qed.

Lemma cty_open_shift_from_lc_fresh d x τ :
  cty_lc_at d τ ->
  x ∉ fv_cty τ ->
  cty_open d x (cty_shift d τ) = τ.
Proof.
  induction τ in d |- *;
    cbn [cty_lc_at cty_open cty_shift open_one open_cty_atom_inst];
    intros Hlc Hx.
  - f_equal.
    apply (qual_open_shift_from_lc_fresh _ _ _ Hlc).
    unfold fv_cty, context_ty_lvars, qual_dom in Hx.
    cbn [context_ty_lvars_at] in Hx.
    rewrite lvars_fv_lvars_at_depth in Hx. exact Hx.
  - f_equal.
    apply (qual_open_shift_from_lc_fresh _ _ _ Hlc).
    unfold fv_cty, context_ty_lvars, qual_dom in Hx.
    cbn [context_ty_lvars_at] in Hx.
    rewrite lvars_fv_lvars_at_depth in Hx. exact Hx.
  - destruct Hlc as [Hlc1 Hlc2].
    f_equal.
    + apply IHτ1; [exact Hlc1|].
      unfold fv_cty, context_ty_lvars in Hx |- *.
      cbn [context_ty_lvars_at] in Hx. rewrite lvars_fv_union, !context_ty_lvars_fv_at in Hx.
      set_solver.
    + apply IHτ2; [exact Hlc2|].
      unfold fv_cty, context_ty_lvars in Hx |- *.
      cbn [context_ty_lvars_at] in Hx. rewrite lvars_fv_union, !context_ty_lvars_fv_at in Hx.
      set_solver.
  - destruct Hlc as [Hlc1 Hlc2].
    f_equal.
    + apply IHτ1; [exact Hlc1|].
      unfold fv_cty, context_ty_lvars in Hx |- *.
      cbn [context_ty_lvars_at] in Hx. rewrite lvars_fv_union, !context_ty_lvars_fv_at in Hx.
      set_solver.
    + apply IHτ2; [exact Hlc2|].
      unfold fv_cty, context_ty_lvars in Hx |- *.
      cbn [context_ty_lvars_at] in Hx. rewrite lvars_fv_union, !context_ty_lvars_fv_at in Hx.
      set_solver.
  - destruct Hlc as [Hlc1 Hlc2].
    f_equal.
    + apply IHτ1; [exact Hlc1|].
      unfold fv_cty, context_ty_lvars in Hx |- *.
      cbn [context_ty_lvars_at] in Hx. rewrite lvars_fv_union, !context_ty_lvars_fv_at in Hx.
      set_solver.
    + apply IHτ2; [exact Hlc2|].
      unfold fv_cty, context_ty_lvars in Hx |- *.
      cbn [context_ty_lvars_at] in Hx. rewrite lvars_fv_union, !context_ty_lvars_fv_at in Hx.
      set_solver.
  - destruct Hlc as [Hlc1 Hlc2].
    f_equal.
    + apply IHτ1; [exact Hlc1|].
      unfold fv_cty, context_ty_lvars in Hx |- *.
      cbn [context_ty_lvars_at] in Hx. rewrite lvars_fv_union, !context_ty_lvars_fv_at in Hx.
      set_solver.
    + apply IHτ2; [exact Hlc2|].
      unfold fv_cty, context_ty_lvars in Hx |- *.
      cbn [context_ty_lvars_at] in Hx. rewrite lvars_fv_union, !context_ty_lvars_fv_at in Hx.
      set_solver.
  - destruct Hlc as [Hlc1 Hlc2].
    f_equal.
    + apply IHτ1; [exact Hlc1|].
      unfold fv_cty, context_ty_lvars in Hx |- *.
      cbn [context_ty_lvars_at] in Hx. rewrite lvars_fv_union, !context_ty_lvars_fv_at in Hx.
      set_solver.
    + apply IHτ2; [exact Hlc2|].
      unfold fv_cty, context_ty_lvars in Hx |- *.
      cbn [context_ty_lvars_at] in Hx. rewrite lvars_fv_union, !context_ty_lvars_fv_at in Hx.
      set_solver.
  - f_equal. apply IHτ; assumption.
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
  - eauto.
Qed.

Lemma basic_context_ty_lc D τ :
  basic_context_ty D τ ->
  lc_context_ty τ.
Proof.
  rewrite basic_context_ty_iff_wf_context_ty_at.
  apply wf_context_ty_at_lc.
Qed.

Lemma context_ty_lvars_at_lc d D τ :
  lc_lvars D ->
  context_ty_lvars_at d τ ⊆ D ->
  context_ty_shape_ok τ ->
  cty_lc_at d τ.
Proof.
  intros HD Hvars Hshape.
  induction τ in d, D, HD, Hvars, Hshape |- *;
    cbn [cty_lc_at context_ty_lvars_at context_ty_shape_ok] in *.
  - intros k Hk.
    destruct (decide (S d <= k)) as [Hle|Hlt]; [|lia].
    exfalso.
    specialize (HD (LVBound (k - S d))).
    apply HD.
    apply Hvars.
    rewrite lvars_at_depth_elem.
    exists (LVBound k). split; [rewrite <- lvars_bv_elem; exact Hk|].
    cbn [logic_var_at_depth].
    rewrite decide_True by lia.
    reflexivity.
  - intros k Hk.
    destruct (decide (S d <= k)) as [Hle|Hlt]; [|lia].
    exfalso.
    specialize (HD (LVBound (k - S d))).
    apply HD.
    apply Hvars.
    rewrite lvars_at_depth_elem.
    exists (LVBound k). split; [rewrite <- lvars_bv_elem; exact Hk|].
    cbn [logic_var_at_depth].
    rewrite decide_True by lia.
    reflexivity.
  - destruct Hshape as [Hshape1 [Hshape2 _]].
    split.
    + eapply IHτ1; [exact HD| |exact Hshape1].
      intros v Hv. apply Hvars. set_solver.
    + eapply IHτ2; [exact HD| |exact Hshape2].
      intros v Hv. apply Hvars. set_solver.
  - destruct Hshape as [Hshape1 [Hshape2 _]].
    split.
    + eapply IHτ1; [exact HD| |exact Hshape1].
      intros v Hv. apply Hvars. set_solver.
    + eapply IHτ2; [exact HD| |exact Hshape2].
      intros v Hv. apply Hvars. set_solver.
  - destruct Hshape as [Hshape1 [Hshape2 _]].
    split.
    + eapply IHτ1; [exact HD| |exact Hshape1].
      intros v Hv. apply Hvars. set_solver.
    + eapply IHτ2; [exact HD| |exact Hshape2].
      intros v Hv. apply Hvars. set_solver.
  - destruct Hshape as [Hshape1 Hshape2].
    split.
    + eapply IHτ1; [exact HD| |exact Hshape1].
      intros v Hv. apply Hvars. set_solver.
    + eapply IHτ2; [exact HD| |exact Hshape2].
      intros v Hv. apply Hvars. set_solver.
  - destruct Hshape as [Hshape1 Hshape2].
    split.
    + eapply IHτ1; [exact HD| |exact Hshape1].
      intros v Hv. apply Hvars. set_solver.
    + eapply IHτ2; [exact HD| |exact Hshape2].
      intros v Hv. apply Hvars. set_solver.
  - eapply IHτ; [exact HD| |exact Hshape].
    exact Hvars.
Qed.

Lemma basic_context_ty_lvars_lc D τ :
  lc_lvars D ->
  basic_context_ty_lvars D τ ->
  lc_context_ty τ.
Proof.
  intros HD [Hvars Hshape].
  unfold lc_context_ty, context_ty_lvars in *.
  eapply context_ty_lvars_at_lc; eauto.
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
    exfalso. specialize (Hlc n ltac:(rewrite lvars_bv_elem; exact Hv)).
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
  - eauto.
Qed.

Lemma context_ty_lvars_at_lc_of_cty_lc d τ :
  cty_lc_at d τ ->
  lc_lvars (context_ty_lvars_at d τ).
Proof.
  intros Hlc v Hv.
  destruct v as [k|a]; [|exact I].
  pose proof (cty_lc_at_lvars_bv_empty d τ Hlc) as Hempty.
  assert (Hk : k ∈ lvars_bv (context_ty_lvars_at d τ))
    by (rewrite lvars_bv_elem; exact Hv).
  rewrite Hempty in Hk.
  rewrite elem_of_empty in Hk.
  exact Hk.
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
  - eauto.
Qed.

Lemma wf_context_ty_at_notin_fv d D τ x :
  wf_context_ty_at d D τ ->
  x ∉ D ->
  x ∉ fv_cty τ.
Proof.
  intros Hwf HxD Hxτ.
  apply HxD.
  eapply wf_context_ty_at_fv_subset; [exact Hwf|exact Hxτ].
Qed.

Lemma wf_context_ty_at_open_at d D τ x :
  x ∉ D ->
  wf_context_ty_at (S d) D τ ->
  wf_context_ty_at d (D ∪ {[x]}) (cty_open d x τ).
Proof.
  induction τ in d, D |- *; cbn [wf_context_ty_at cty_open];
    intros Hx Hwf.
  - rewrite qual_open_atom_vars.
    apply lvars_wf_at_open_at; exact Hx || exact Hwf.
  - rewrite qual_open_atom_vars.
    apply lvars_wf_at_open_at; exact Hx || exact Hwf.
  - destruct Hwf as [H1 [H2 Herase]].
    repeat split.
    + apply IHτ1; assumption.
    + apply IHτ2; assumption.
    + rewrite !cty_open_preserves_erasure. exact Herase.
  - destruct Hwf as [H1 [H2 Herase]].
    repeat split.
    + apply IHτ1; assumption.
    + apply IHτ2; assumption.
    + rewrite !cty_open_preserves_erasure. exact Herase.
  - destruct Hwf as [H1 [H2 Herase]].
    repeat split.
    + apply IHτ1; assumption.
    + apply IHτ2; assumption.
    + rewrite !cty_open_preserves_erasure. exact Herase.
  - destruct Hwf as [H1 H2]. split.
    + apply IHτ1; assumption.
    + apply (IHτ2 (S d)); assumption.
  - destruct Hwf as [H1 H2]. split.
    + rewrite (cty_open_above_lc_fresh 0 d x τ1).
      * exact H1.
      * lia.
      * eapply wf_context_ty_at_lc. exact H1.
      * pose proof (wf_context_ty_at_fv_subset 0 ∅ τ1 H1) as Hfv.
        set_solver.
    + apply (IHτ2 (S d)); assumption.
  - apply IHτ; assumption.
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
        by (rewrite lvars_bv_elem; exact Hv).
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

Lemma lc_context_ty_over_lt_bound_fvar b x :
  lc_context_ty (over_ty b (mk_q_lt_base b (vbvar 0) (vfvar x))).
Proof.
  unfold lc_context_ty, over_ty, mk_q_lt_base.
  cbn [cty_lc_at qual_vars qual_lvars lvar_value_keys lvars_lc_at].
  intros k Hk.
  rewrite lvars_bv_union in Hk.
  apply elem_of_union in Hk as [Hk | Hk].
  - rewrite lvars_bv_elem in Hk.
    apply elem_of_singleton in Hk.
    inversion Hk. subst. lia.
  - rewrite lvars_bv_elem in Hk.
    apply elem_of_singleton in Hk.
    discriminate.
Qed.

Lemma lc_context_ty_fix_rec_call_ty b x τx τ :
  lc_context_ty τx ->
  lc_context_ty τ ->
  lc_context_ty (fix_rec_call_ty b x τx τ).
Proof.
  intros Hτx Hτ.
  unfold lc_context_ty, fix_rec_call_ty.
  cbn [cty_lc_at].
  split.
  - split.
    + exact Hτx.
    + apply lc_context_ty_over_lt_bound_fvar.
  - eapply (cty_lc_at_mono_depth 0 1); [lia|exact Hτ].
Qed.

Lemma cty_open_shift_fix_rec_call_ty_fresh b x z τx τ :
  z <> x ->
  z ∉ fv_cty τx ->
  z ∉ fv_cty τ ->
  lc_context_ty τx ->
  lc_context_ty τ ->
  cty_open 0 z (cty_shift 0 (fix_rec_call_ty b x τx τ)) =
    fix_rec_call_ty b x τx τ.
Proof.
  intros Hzx Hzτx Hzτ Hτx Hτ.
  apply cty_open_shift_from_lc_fresh.
  - apply lc_context_ty_fix_rec_call_ty; assumption.
  - apply fv_cty_fix_rec_call_ty_fresh; assumption.
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
