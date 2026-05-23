(** * ChoiceTypeLanguage.WFChoiceTy

    Formation/scoping predicates for choice types. *)

From ChoiceTypeLanguage Require Export WFLvars.

Fixpoint cty_lc_at (d : nat) (τ : choice_ty) : Prop :=
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

Definition lc_choice_ty (τ : choice_ty) : Prop :=
  cty_lc_at 0 τ.

Fixpoint wf_choice_ty_at (d : nat) (D : aset) (τ : choice_ty) : Prop :=
  match τ with
  | CTOver _ φ | CTUnder _ φ =>
      lvars_wf_at (S d) D (qual_vars φ)
  | CTInter τ1 τ2
  | CTUnion τ1 τ2
  | CTSum τ1 τ2 =>
      wf_choice_ty_at d D τ1 /\
      wf_choice_ty_at d D τ2 /\
      erase_ty τ1 = erase_ty τ2
  | CTArrow τx τ
  | CTWand τx τ =>
      wf_choice_ty_at d D τx /\
      wf_choice_ty_at (S d) D τ
  end.

Definition basic_choice_ty (D : aset) (τ : choice_ty) : Prop :=
  wf_choice_ty_at 0 D τ.

#[global] Instance lc_cty_inst : Lc choice_ty := lc_choice_ty.
Arguments lc_cty_inst /.

Class ScopedIn A := scoped_in : aset -> A -> Prop.

#[global] Instance scoped_choice_ty : ScopedIn choice_ty := basic_choice_ty.

Notation "D '⊢s' x" := (scoped_in D x)
  (at level 40, x at level 40).
Notation "D '⊢sτ' τ" := (basic_choice_ty D τ)
  (at level 40, τ at level 40, only printing).

Lemma scoped_choice_ty_iff D τ :
  D ⊢s τ <-> basic_choice_ty D τ.
Proof. reflexivity. Qed.

Lemma wf_choice_ty_at_shift d D τ k :
  d <= k ->
  wf_choice_ty_at d D τ ->
  wf_choice_ty_at d D (cty_shift k τ).
Proof.
  induction τ as [b φ|b φ|τ1 IHτ1 τ2 IHτ2|τ1 IHτ1 τ2 IHτ2
                 |τ1 IHτ1 τ2 IHτ2|τ1 IHτ1 τ2 IHτ2|τ1 IHτ1 τ2 IHτ2]
    in d, k |- *; cbn [wf_choice_ty_at cty_shift]; intros Hdk Hwf.
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

Lemma wf_choice_ty_at_mono d D E τ :
  D ⊆ E ->
  wf_choice_ty_at d D τ ->
  wf_choice_ty_at d E τ.
Proof.
  induction τ in d |- *; cbn [wf_choice_ty_at]; intros HDE Hwf;
    try solve [eapply lvars_wf_at_mono; eauto].
  all: repeat match goal with
  | H : _ /\ _ |- _ => destruct H
  | H : _ /\ _ /\ _ |- _ => destruct H as [? [? ?]]
  end; repeat split; eauto.
Qed.

Lemma basic_choice_ty_mono D E τ :
  D ⊆ E ->
  basic_choice_ty D τ ->
  basic_choice_ty E τ.
Proof.
  apply wf_choice_ty_at_mono.
Qed.

Lemma wf_choice_ty_at_lc d D τ :
  wf_choice_ty_at d D τ ->
  cty_lc_at d τ.
Proof.
  induction τ in d |- *; cbn [wf_choice_ty_at cty_lc_at]; intros Hwf;
    try solve [apply lvars_wf_at_lc with (D := D); exact Hwf].
  all: repeat match goal with
  | H : _ /\ _ |- _ => destruct H
  | H : _ /\ _ /\ _ |- _ => destruct H as [? [? ?]]
  end; repeat split; eauto.
Qed.

Lemma basic_choice_ty_lc D τ :
  basic_choice_ty D τ ->
  lc_choice_ty τ.
Proof.
  apply wf_choice_ty_at_lc.
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
  lvars_bv (choice_ty_lvars_at d τ) = ∅.
Proof.
  induction τ in d |- *; cbn [cty_lc_at choice_ty_lvars_at]; intros Hlc.
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

Lemma lc_choice_ty_lvars_bv_empty τ :
  lc_choice_ty τ ->
  lvars_bv (choice_ty_lvars τ) = ∅.
Proof.
  apply cty_lc_at_lvars_bv_empty.
Qed.

Lemma lc_choice_ty_lvars_subset_atoms τ :
  lc_choice_ty τ ->
  choice_ty_lvars τ ⊆ lvars_of_atoms (fv_cty τ).
Proof.
  intros Hlc.
  apply lvars_bv_empty_subset_of_atoms_fv.
  apply lc_choice_ty_lvars_bv_empty. exact Hlc.
Qed.

Lemma wf_choice_ty_at_fv_subset d D τ :
  wf_choice_ty_at d D τ ->
  fv_cty τ ⊆ D.
Proof.
  intros Hwf.
  rewrite <- (choice_ty_lvars_fv_at d τ).
  induction τ in d, Hwf |- *; cbn [choice_ty_lvars_at wf_choice_ty_at] in *.
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
    rewrite lvars_fv_union. set_solver.
  - destruct Hwf as [H1 H2].
    rewrite lvars_fv_union. set_solver.
Qed.

Lemma basic_choice_ty_fv_subset D τ :
  basic_choice_ty D τ ->
  fv_cty τ ⊆ D.
Proof.
  apply wf_choice_ty_at_fv_subset.
Qed.

Lemma basic_choice_ty_lvar_cty_vars_equiv D τ1 τ2 :
  τ1 ≡τv τ2 ->
  basic_choice_ty D τ1 ->
  basic_choice_ty D τ2.
Proof.
  revert τ2.
  enough (forall d D τ1 τ2,
    τ1 ≡τv τ2 ->
    wf_choice_ty_at d D τ1 ->
    wf_choice_ty_at d D τ2) as Hgen.
  { intros τ2 Heq Hwf. eapply Hgen; eauto. }
  clear D τ1.
  intros d D τ1.
  induction τ1 in d |- *; intros τ2 Heq Hwf;
    destruct τ2; cbn [cty_vars_equiv wf_choice_ty_at] in *;
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

Lemma wf_choice_ty_at_drop_fresh d D x τ :
  x ∉ fv_cty τ ->
  wf_choice_ty_at d (D ∪ {[x]}) τ ->
  wf_choice_ty_at d D τ.
Proof.
  induction τ in d |- *; cbn [wf_choice_ty_at]; intros Hfresh Hwf.
  - eapply lvars_wf_at_drop_fresh; [|exact Hwf].
    intros Hbad. apply Hfresh.
    unfold fv_cty, choice_ty_lvars. cbn [choice_ty_lvars_at].
    rewrite lvars_fv_lvars_at_depth. exact Hbad.
  - eapply lvars_wf_at_drop_fresh; [|exact Hwf].
    intros Hbad. apply Hfresh.
    unfold fv_cty, choice_ty_lvars. cbn [choice_ty_lvars_at].
    rewrite lvars_fv_lvars_at_depth. exact Hbad.
  - destruct Hwf as [H1 [H2 Herase]]. repeat split.
    + eapply IHτ1; [|exact H1].
      intros Hbad. apply Hfresh. unfold fv_cty, choice_ty_lvars in *.
      cbn [choice_ty_lvars_at] in *. rewrite lvars_fv_union.
      apply elem_of_union_l. rewrite choice_ty_lvars_fv_at. exact Hbad.
    + eapply IHτ2; [|exact H2].
      intros Hbad. apply Hfresh. unfold fv_cty, choice_ty_lvars in *.
      cbn [choice_ty_lvars_at] in *. rewrite lvars_fv_union.
      apply elem_of_union_r. rewrite choice_ty_lvars_fv_at. exact Hbad.
    + exact Herase.
  - destruct Hwf as [H1 [H2 Herase]]. repeat split.
    + eapply IHτ1; [|exact H1].
      intros Hbad. apply Hfresh. unfold fv_cty, choice_ty_lvars in *.
      cbn [choice_ty_lvars_at] in *. rewrite lvars_fv_union.
      apply elem_of_union_l. rewrite choice_ty_lvars_fv_at. exact Hbad.
    + eapply IHτ2; [|exact H2].
      intros Hbad. apply Hfresh. unfold fv_cty, choice_ty_lvars in *.
      cbn [choice_ty_lvars_at] in *. rewrite lvars_fv_union.
      apply elem_of_union_r. rewrite choice_ty_lvars_fv_at. exact Hbad.
    + exact Herase.
  - destruct Hwf as [H1 [H2 Herase]]. repeat split.
    + eapply IHτ1; [|exact H1].
      intros Hbad. apply Hfresh. unfold fv_cty, choice_ty_lvars in *.
      cbn [choice_ty_lvars_at] in *. rewrite lvars_fv_union.
      apply elem_of_union_l. rewrite choice_ty_lvars_fv_at. exact Hbad.
    + eapply IHτ2; [|exact H2].
      intros Hbad. apply Hfresh. unfold fv_cty, choice_ty_lvars in *.
      cbn [choice_ty_lvars_at] in *. rewrite lvars_fv_union.
      apply elem_of_union_r. rewrite choice_ty_lvars_fv_at. exact Hbad.
    + exact Herase.
  - destruct Hwf as [H1 H2]. split.
    + eapply IHτ1; [|exact H1].
      intros Hbad. apply Hfresh. unfold fv_cty, choice_ty_lvars in *.
      cbn [choice_ty_lvars_at] in *. rewrite lvars_fv_union.
      apply elem_of_union_l. rewrite choice_ty_lvars_fv_at. exact Hbad.
    + eapply IHτ2; [|exact H2].
      intros Hbad. apply Hfresh. unfold fv_cty, choice_ty_lvars in *.
      cbn [choice_ty_lvars_at] in *. rewrite lvars_fv_union.
      apply elem_of_union_r. rewrite choice_ty_lvars_fv_at. exact Hbad.
  - destruct Hwf as [H1 H2]. split.
    + eapply IHτ1; [|exact H1].
      intros Hbad. apply Hfresh. unfold fv_cty, choice_ty_lvars in *.
      cbn [choice_ty_lvars_at] in *. rewrite lvars_fv_union.
      apply elem_of_union_l. rewrite choice_ty_lvars_fv_at. exact Hbad.
    + eapply IHτ2; [|exact H2].
      intros Hbad. apply Hfresh. unfold fv_cty, choice_ty_lvars in *.
      cbn [choice_ty_lvars_at] in *. rewrite lvars_fv_union.
      apply elem_of_union_r. rewrite choice_ty_lvars_fv_at. exact Hbad.
Qed.

Lemma basic_choice_ty_drop_fresh D x τ :
  x ∉ fv_cty τ ->
  basic_choice_ty (D ∪ {[x]}) τ ->
  basic_choice_ty D τ.
Proof.
  apply wf_choice_ty_at_drop_fresh.
Qed.

Lemma basic_choice_ty_drop_insert_fresh
    (Σ : gmap atom ty) x T τ :
  x ∉ dom Σ ->
  x ∉ fv_cty τ ->
  basic_choice_ty (dom (<[x := T]> Σ)) τ ->
  basic_choice_ty (dom Σ) τ.
Proof.
  intros Hx Hfresh Hbasic.
  apply (basic_choice_ty_drop_fresh (dom Σ) x τ); [exact Hfresh|].
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
      unfold fv_cty, choice_ty_lvars. cbn [choice_ty_lvars_at].
      rewrite lvars_fv_lvars_at_depth. exact Hbad.
  - change ({d + k ~> x} CTUnder b φ) with
      (cty_open (d + k) x (CTUnder b φ)).
    cbn [cty_open].
    rewrite qual_open_atom_fresh_index.
    + reflexivity.
    + intros Hbad. cbn [qual_bvars qual_vars] in Hbad.
      specialize (Hlc (S (d + k)) Hbad). lia.
    + unfold qual_dom. intros Hbad. apply Hfresh.
      unfold fv_cty, choice_ty_lvars. cbn [choice_ty_lvars_at].
      rewrite lvars_fv_lvars_at_depth. exact Hbad.
  - destruct Hlc as [H1 H2].
    change ({d + k ~> x} CTInter τ1 τ2) with
      (cty_open (d + k) x (CTInter τ1 τ2)).
    cbn [cty_open].
    rewrite IHτ1, IHτ2 by (try assumption; unfold fv_cty, choice_ty_lvars in *;
      cbn [choice_ty_lvars_at] in *; rewrite lvars_fv_union in *; set_solver).
    reflexivity.
  - destruct Hlc as [H1 H2].
    change ({d + k ~> x} CTUnion τ1 τ2) with
      (cty_open (d + k) x (CTUnion τ1 τ2)).
    cbn [cty_open].
    rewrite IHτ1, IHτ2 by (try assumption; unfold fv_cty, choice_ty_lvars in *;
      cbn [choice_ty_lvars_at] in *; rewrite lvars_fv_union in *; set_solver).
    reflexivity.
  - destruct Hlc as [H1 H2].
    change ({d + k ~> x} CTSum τ1 τ2) with
      (cty_open (d + k) x (CTSum τ1 τ2)).
    cbn [cty_open].
    rewrite IHτ1, IHτ2 by (try assumption; unfold fv_cty, choice_ty_lvars in *;
      cbn [choice_ty_lvars_at] in *; rewrite lvars_fv_union in *; set_solver).
    reflexivity.
  - destruct Hlc as [H1 H2].
    change ({d + k ~> x} CTArrow τ1 τ2) with
      (cty_open (d + k) x (CTArrow τ1 τ2)).
    cbn [cty_open].
    assert (Hfresh1 : x ∉ fv_cty τ1).
    { intros Hbad. apply Hfresh. unfold fv_cty, choice_ty_lvars.
      cbn [choice_ty_lvars_at]. rewrite lvars_fv_union.
      apply elem_of_union_l. rewrite choice_ty_lvars_fv_at. exact Hbad. }
    assert (Hfresh2 : x ∉ fv_cty τ2).
    { intros Hbad. apply Hfresh. unfold fv_cty, choice_ty_lvars.
      cbn [choice_ty_lvars_at]. rewrite lvars_fv_union.
      apply elem_of_union_r. rewrite choice_ty_lvars_fv_at. exact Hbad. }
    rewrite IHτ1 by assumption.
    replace (S (d + k)) with (S d + k) by lia.
    rewrite IHτ2 by assumption.
    reflexivity.
  - destruct Hlc as [H1 H2].
    change ({d + k ~> x} CTWand τ1 τ2) with
      (cty_open (d + k) x (CTWand τ1 τ2)).
    cbn [cty_open].
    assert (Hfresh1 : x ∉ fv_cty τ1).
    { intros Hbad. apply Hfresh. unfold fv_cty, choice_ty_lvars.
      cbn [choice_ty_lvars_at]. rewrite lvars_fv_union.
      apply elem_of_union_l. rewrite choice_ty_lvars_fv_at. exact Hbad. }
    assert (Hfresh2 : x ∉ fv_cty τ2).
    { intros Hbad. apply Hfresh. unfold fv_cty, choice_ty_lvars.
      cbn [choice_ty_lvars_at]. rewrite lvars_fv_union.
      apply elem_of_union_r. rewrite choice_ty_lvars_fv_at. exact Hbad. }
    rewrite IHτ1 by assumption.
    replace (S (d + k)) with (S d + k) by lia.
    rewrite IHτ2 by assumption.
    reflexivity.
Qed.

Lemma lc_choice_ty_open_fresh k x τ :
  lc_choice_ty τ ->
  x ∉ fv_cty τ ->
  {k ~> x} τ = τ.
Proof.
  intros Hlc Hfresh.
  replace k with (0 + k) at 1 by lia.
  apply cty_lc_at_open_fresh_at; assumption.
Qed.

Lemma wf_choice_ty_at_open_at d D τ x :
  x ∉ D ->
  wf_choice_ty_at (S d) D τ ->
  wf_choice_ty_at d (D ∪ {[x]}) ({d ~> x} τ).
Proof.
  induction τ in d |- *; cbn [wf_choice_ty_at]; intros Hx Hwf.
  - change ({d ~> x} CTOver b φ) with (cty_open d x (CTOver b φ)).
    cbn [cty_open wf_choice_ty_at].
    rewrite qual_open_atom_vars.
    apply lvars_wf_at_open_at; assumption.
  - change ({d ~> x} CTUnder b φ) with (cty_open d x (CTUnder b φ)).
    cbn [cty_open wf_choice_ty_at].
    rewrite qual_open_atom_vars.
    apply lvars_wf_at_open_at; assumption.
  - change ({d ~> x} CTInter τ1 τ2) with (cty_open d x (CTInter τ1 τ2)).
    cbn [cty_open wf_choice_ty_at] in *.
    destruct Hwf as [H1 [H2 Herase]]. repeat split.
    + apply IHτ1; assumption.
    + apply IHτ2; assumption.
    + rewrite !cty_open_preserves_erasure. exact Herase.
  - change ({d ~> x} CTUnion τ1 τ2) with (cty_open d x (CTUnion τ1 τ2)).
    cbn [cty_open wf_choice_ty_at] in *.
    destruct Hwf as [H1 [H2 Herase]]. repeat split.
    + apply IHτ1; assumption.
    + apply IHτ2; assumption.
    + rewrite !cty_open_preserves_erasure. exact Herase.
  - change ({d ~> x} CTSum τ1 τ2) with (cty_open d x (CTSum τ1 τ2)).
    cbn [cty_open wf_choice_ty_at] in *.
    destruct Hwf as [H1 [H2 Herase]]. repeat split.
    + apply IHτ1; assumption.
    + apply IHτ2; assumption.
    + rewrite !cty_open_preserves_erasure. exact Herase.
  - change ({d ~> x} CTArrow τ1 τ2) with (cty_open d x (CTArrow τ1 τ2)).
    cbn [cty_open wf_choice_ty_at] in *.
    destruct Hwf as [H1 H2]. split.
    + apply IHτ1; assumption.
    + apply IHτ2; assumption.
  - change ({d ~> x} CTWand τ1 τ2) with (cty_open d x (CTWand τ1 τ2)).
    cbn [cty_open wf_choice_ty_at] in *.
    destruct Hwf as [H1 H2]. split.
    + apply IHτ1; assumption.
    + apply IHτ2; assumption.
Qed.

Lemma basic_choice_ty_open_body D τ x :
  x ∉ D ->
  wf_choice_ty_at 1 D τ ->
  basic_choice_ty (D ∪ {[x]}) ({0 ~> x} τ).
Proof.
  apply wf_choice_ty_at_open_at.
Qed.

Lemma basic_choice_ty_open_body_cofinite D τ (L0 : aset) :
  wf_choice_ty_at 1 D τ ->
  exists L,
    L0 ⊆ L /\
    forall y,
      y ∉ L ->
      basic_choice_ty (D ∪ {[y]}) ({0 ~> y} τ).
Proof.
  intros Hwf.
  exists (L0 ∪ D). split; [set_solver|].
  intros y Hy.
  apply basic_choice_ty_open_body; [set_solver|exact Hwf].
Qed.

Lemma basic_choice_ty_arrow_inv D τx τ :
  basic_choice_ty D (CTArrow τx τ) ->
  basic_choice_ty D τx /\ wf_choice_ty_at 1 D τ.
Proof.
  intros H. exact H.
Qed.

Lemma basic_choice_ty_wand_inv D τx τ :
  basic_choice_ty D (CTWand τx τ) ->
  basic_choice_ty D τx /\ wf_choice_ty_at 1 D τ.
Proof.
  intros H. exact H.
Qed.

Lemma basic_choice_ty_open_arrow_body_cofinite
    (Δ : gmap atom ty) τx τ (L0 : gset atom) :
  basic_choice_ty (dom Δ) (CTArrow τx τ) ->
  exists L,
    L0 ⊆ L /\
    forall y,
      y ∉ L ->
      basic_choice_ty (dom (<[y := erase_ty τx]> Δ)) ({0 ~> y} τ).
Proof.
  intros Hbasic.
  destruct (basic_choice_ty_arrow_inv _ _ _ Hbasic) as [_ Hbody].
  destruct (basic_choice_ty_open_body_cofinite (dom Δ) τ L0 Hbody)
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

Lemma basic_choice_ty_open_wand_body_cofinite
    (Δ : gmap atom ty) τx τ (L0 : gset atom) :
  basic_choice_ty (dom Δ) (CTWand τx τ) ->
  exists L,
    L0 ⊆ L /\
    forall y,
      y ∉ L ->
      basic_choice_ty (dom (<[y := erase_ty τx]> Δ)) ({0 ~> y} τ).
Proof.
  intros Hbasic.
  destruct (basic_choice_ty_wand_inv _ _ _ Hbasic) as [_ Hbody].
  destruct (basic_choice_ty_open_body_cofinite (dom Δ) τ L0 Hbody)
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

Lemma basic_choice_ty_shift D τ k :
  basic_choice_ty D τ ->
  basic_choice_ty D (cty_shift k τ).
Proof.
  intros H.
  eapply wf_choice_ty_at_shift; [lia|exact H].
Qed.
