(** * ContextTypeLanguage.SyntaxLvars

    Lvar support computations for context syntax. *)

From ContextTypeLanguage Require Export SyntaxCore.
From ContextBase Require Import BaseTactics.

Lemma context_ty_lvars_at_open d k x τ :
  context_ty_lvars_at d ({d + k ~> x} τ) =
  lvars_open k x (context_ty_lvars_at d τ).
Proof.
  induction τ in d, k |- *; cbn [context_ty_lvars_at].
  - change ({d + k ~> x} CTOver b φ) with (cty_open (d + k) x (CTOver b φ)).
    cbn [cty_open context_ty_lvars_at].
    replace (S (d + k)) with (S d + k) by lia.
    rewrite qual_open_atom_vars.
    apply lvars_at_depth_open.
  - change ({d + k ~> x} CTUnder b φ) with (cty_open (d + k) x (CTUnder b φ)).
    cbn [cty_open context_ty_lvars_at].
    replace (S (d + k)) with (S d + k) by lia.
    rewrite qual_open_atom_vars.
    apply lvars_at_depth_open.
  - change ({d + k ~> x} CTInter τ1 τ2) with
      (cty_open (d + k) x (CTInter τ1 τ2)).
    cbn [cty_open context_ty_lvars_at].
    rewrite IHτ1, IHτ2.
    symmetry. rewrite set_swap_union. reflexivity.
  - change ({d + k ~> x} CTUnion τ1 τ2) with
      (cty_open (d + k) x (CTUnion τ1 τ2)).
    cbn [cty_open context_ty_lvars_at].
    rewrite IHτ1, IHτ2.
    symmetry. rewrite set_swap_union. reflexivity.
  - change ({d + k ~> x} CTSum τ1 τ2) with
      (cty_open (d + k) x (CTSum τ1 τ2)).
    cbn [cty_open context_ty_lvars_at].
    rewrite IHτ1, IHτ2.
    symmetry. rewrite set_swap_union. reflexivity.
  - change ({d + k ~> x} CTArrow τ1 τ2) with
      (cty_open (d + k) x (CTArrow τ1 τ2)).
    cbn [cty_open context_ty_lvars_at].
    rewrite IHτ1.
    replace (S (d + k)) with (S d + k) by lia.
    rewrite IHτ2.
    symmetry. rewrite set_swap_union. reflexivity.
  - change ({d + k ~> x} CTWand τ1 τ2) with
      (cty_open (d + k) x (CTWand τ1 τ2)).
    cbn [cty_open context_ty_lvars_at].
    rewrite IHτ1.
    replace (S (d + k)) with (S d + k) by lia.
    rewrite IHτ2.
    symmetry. rewrite set_swap_union. reflexivity.
Qed.

Lemma cty_open_vars k x τ :
  context_ty_lvars ({k ~> x} τ) = context_ty_open_lvars k x τ.
Proof.
  unfold context_ty_lvars, context_ty_open_lvars.
  replace k with (0 + k) at 1 by lia.
  apply context_ty_lvars_at_open.
Qed.

Lemma context_ty_lvars_at_depth τ c d :
  lvars_at_depth d (context_ty_lvars_at c τ) =
  context_ty_lvars_at (c + d) τ.
Proof.
  induction τ in c, d |- *; cbn [context_ty_lvars_at];
    rewrite ?lvars_at_depth_union, ?IHτ1, ?IHτ2.
  - rewrite lvars_at_depth_depth. reflexivity.
  - rewrite lvars_at_depth_depth. reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - replace (S c + d) with (S (c + d)) by lia. reflexivity.
  - replace (S c + d) with (S (c + d)) by lia. reflexivity.
Qed.

Lemma context_ty_lvars_depth τ d :
  lvars_at_depth d (context_ty_lvars τ) = context_ty_lvars_at d τ.
Proof.
  unfold context_ty_lvars.
  rewrite context_ty_lvars_at_depth. reflexivity.
Qed.

Lemma context_ty_lvars_open_body_without_fresh_closed
    (D : lvset) τ y :
  lc_lvars D ->
  LVFree y ∉ D ->
  context_ty_lvars_at 1 τ ⊆ D ->
  context_ty_lvars (cty_open 0 y τ) ∖ {[LVFree y]} ⊆
  context_ty_lvars_at 1 τ.
Proof.
  intros Hlc HyD Hτ.
  rewrite cty_open_vars.
  unfold context_ty_open_lvars.
  rewrite <- (context_ty_lvars_depth τ 1).
  eapply lvars_open0_difference_subset_depth1 with (D := D).
  - exact Hlc.
  - exact HyD.
  - rewrite context_ty_lvars_depth. exact Hτ.
Qed.

Lemma context_ty_lvars_fv_at d τ :
  lvars_fv (context_ty_lvars_at d τ) = fv_cty τ.
Proof.
  induction τ in d |- *; unfold fv_cty, context_ty_lvars in *;
    cbn [context_ty_lvars_at] in *.
  - rewrite lvars_fv_lvars_at_depth, lvars_fv_lvars_at_depth. reflexivity.
  - rewrite lvars_fv_lvars_at_depth, lvars_fv_lvars_at_depth. reflexivity.
  - rewrite !lvars_fv_union, IHτ1, IHτ2. reflexivity.
  - rewrite !lvars_fv_union, IHτ1, IHτ2. reflexivity.
  - rewrite !lvars_fv_union, IHτ1, IHτ2. reflexivity.
  - rewrite !lvars_fv_union, IHτ1, (IHτ2 (S d)), <- (IHτ2 1). reflexivity.
  - rewrite !lvars_fv_union, IHτ1, (IHτ2 (S d)), <- (IHτ2 1). reflexivity.
Qed.

Lemma context_ty_lvars_fv τ :
  lvars_fv (context_ty_lvars τ) = fv_cty τ.
Proof.
  apply context_ty_lvars_fv_at.
Qed.

Lemma context_ty_lvars_over_fv b q :
  lvars_fv (context_ty_lvars (CTOver b q)) = qual_dom q.
Proof.
  cbn [context_ty_lvars context_ty_lvars_at].
  rewrite lvars_fv_lvars_at_depth. reflexivity.
Qed.

Lemma context_ty_lvars_under_fv b q :
  lvars_fv (context_ty_lvars (CTUnder b q)) = qual_dom q.
Proof.
  cbn [context_ty_lvars context_ty_lvars_at].
  rewrite lvars_fv_lvars_at_depth. reflexivity.
Qed.

Lemma context_ty_over_fresh_open_qual_dom x y b q :
  LVFree x ∉ context_ty_lvars (CTOver b q) ->
  x <> y ->
  x ∉ qual_dom (q ^q^ y).
Proof.
  intros Hx Hxy.
  apply qual_open_atom_dom_fresh_ne; [|exact Hxy].
  intros Hbad. apply Hx. apply lvars_fv_elem.
  rewrite context_ty_lvars_over_fv. exact Hbad.
Qed.

Lemma context_ty_under_fresh_open_qual_dom x y b q :
  LVFree x ∉ context_ty_lvars (CTUnder b q) ->
  x <> y ->
  x ∉ qual_dom (q ^q^ y).
Proof.
  intros Hx Hxy.
  apply qual_open_atom_dom_fresh_ne; [|exact Hxy].
  intros Hbad. apply Hx. apply lvars_fv_elem.
  rewrite context_ty_lvars_under_fv. exact Hbad.
Qed.

Lemma context_ty_lvars_at_shift_under d k τ :
  k <= d ->
  context_ty_lvars_at (S d) (cty_shift k τ) =
  context_ty_lvars_at d τ.
Proof.
  induction τ in d, k |- *; cbn [context_ty_lvars_at cty_shift]; intros Hkd.
  - rewrite qual_shift_from_vars.
    apply lvars_at_depth_shift_under. lia.
  - rewrite qual_shift_from_vars.
    apply lvars_at_depth_shift_under. lia.
  - rewrite IHτ1, IHτ2 by exact Hkd. reflexivity.
  - rewrite IHτ1, IHτ2 by exact Hkd. reflexivity.
  - rewrite IHτ1, IHτ2 by exact Hkd. reflexivity.
  - rewrite IHτ1 by exact Hkd.
    rewrite IHτ2 by lia. reflexivity.
  - rewrite IHτ1 by exact Hkd.
    rewrite IHτ2 by lia. reflexivity.
Qed.

Lemma context_ty_lvars_at_succ_body d τ :
  context_ty_lvars_at d τ ⊆
  lvars_shift_from 0 (context_ty_lvars_at (S d) τ) ∪ {[LVBound 0]}.
Proof.
  induction τ in d |- *; cbn [context_ty_lvars_at].
  - apply lvars_at_depth_succ_body.
  - apply lvars_at_depth_succ_body.
  - eapply lvars_shift_from_succ_body_union; [apply IHτ1 | apply IHτ2].
  - eapply lvars_shift_from_succ_body_union; [apply IHτ1 | apply IHτ2].
  - eapply lvars_shift_from_succ_body_union; [apply IHτ1 | apply IHτ2].
  - eapply lvars_shift_from_succ_body_union; [apply IHτ1 | apply IHτ2].
  - eapply lvars_shift_from_succ_body_union; [apply IHτ1 | apply IHτ2].
Qed.

Lemma context_ty_lvars_body_subset D τ :
  context_ty_lvars_at 1 τ ⊆ lvars_of_atoms D ->
  context_ty_lvars τ ⊆ lvars_shift_from 0 (lvars_of_atoms D) ∪ {[LVBound 0]}.
Proof.
  intros Hsub.
  transitivity (lvars_shift_from 0 (context_ty_lvars_at 1 τ) ∪ {[LVBound 0]}).
  - apply context_ty_lvars_at_succ_body.
  - set_solver.
Qed.

Lemma context_ty_lvars_at_shift d k τ :
  context_ty_lvars_at d (cty_shift (d + k) τ) =
  lvars_shift_from k (context_ty_lvars_at d τ).
Proof.
  induction τ in d, k |- *; cbn [context_ty_lvars_at cty_shift].
  - replace (S (d + k)) with (S d + k) by lia.
    rewrite qual_shift_from_vars.
    apply lvars_at_depth_shift_from.
  - replace (S (d + k)) with (S d + k) by lia.
    rewrite qual_shift_from_vars.
    apply lvars_at_depth_shift_from.
  - rewrite IHτ1, IHτ2. symmetry. apply lvars_shift_from_union.
  - rewrite IHτ1, IHτ2. symmetry. apply lvars_shift_from_union.
  - rewrite IHτ1, IHτ2. symmetry. apply lvars_shift_from_union.
  - rewrite IHτ1.
    replace (S (d + k)) with (S d + k) by lia.
    rewrite IHτ2.
    symmetry. apply lvars_shift_from_union.
  - rewrite IHτ1.
    replace (S (d + k)) with (S d + k) by lia.
    rewrite IHτ2.
    symmetry. apply lvars_shift_from_union.
Qed.

Lemma cty_shift0_vars τ :
  context_ty_lvars (cty_shift 0 τ) = context_ty_shift_lvars τ.
Proof.
  unfold context_ty_lvars, context_ty_shift_lvars.
  change (cty_shift 0 τ) with (cty_shift (0 + 0) τ).
  apply context_ty_lvars_at_shift.
Qed.

Lemma cty_shift_vars τ :
  context_ty_lvars (cty_shift 0 τ) = context_ty_shift_lvars τ.
Proof.
  apply cty_shift0_vars.
Qed.

Lemma cty_open_fv_subset k x τ :
  fv_cty ({k ~> x} τ) ⊆ fv_cty τ ∪ {[x]}.
Proof.
  unfold fv_cty.
  rewrite cty_open_vars.
  apply lvars_fv_open_subset.
Qed.

Lemma cty_shift_fv k τ :
  fv_cty (cty_shift k τ) = fv_cty τ.
Proof.
  unfold fv_cty, context_ty_lvars.
  rewrite <- (Nat.add_0_l k) at 1.
  rewrite context_ty_lvars_at_shift.
  apply lvars_shift_from_fv.
Qed.

Lemma context_ty_lvars_open_shift_fresh x y τ :
  x <> y ->
  LVFree x ∉ context_ty_lvars τ ->
  LVFree x ∉ context_ty_lvars (cty_open 0 y (cty_shift 0 τ)).
Proof.
  intros Hxy Hfresh Hin.
  apply lvars_fv_elem in Hin.
  pose proof (cty_open_fv_subset 0 y (cty_shift 0 τ) x Hin) as Hsub.
  rewrite cty_shift_fv in Hsub.
  apply elem_of_union in Hsub as [Hinτ|Hy].
  - apply Hfresh. apply lvars_fv_elem. exact Hinτ.
  - rewrite elem_of_singleton in Hy. congruence.
Qed.
