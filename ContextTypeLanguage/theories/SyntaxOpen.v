(** * ContextTypeLanguage.SyntaxOpen

    Open/shift structural laws for context syntax. *)

From ContextTypeLanguage Require Export SyntaxLvars.

Lemma cty_open_preserves_erasure k x τ :
  erase_ty ({k ~> x} τ) = erase_ty τ.
Proof.
  induction τ in k |- *; simpl; try rewrite ?IHτ1, ?IHτ2; reflexivity.
Qed.

Lemma cty_shift_preserves_erasure k τ :
  erase_ty (cty_shift k τ) = erase_ty τ.
Proof.
  induction τ in k |- *; simpl; try rewrite ?IHτ1, ?IHτ2; reflexivity.
Qed.

Lemma cty_open_preserves_depth k x τ :
  cty_depth ({k ~> x} τ) = cty_depth τ.
Proof.
  induction τ in k |- *; simpl; try rewrite ?IHτ1, ?IHτ2; reflexivity.
Qed.

Lemma cty_shift_preserves_depth k τ :
  cty_depth (cty_shift k τ) = cty_depth τ.
Proof.
  induction τ in k |- *; simpl; try rewrite ?IHτ1, ?IHτ2; reflexivity.
Qed.

Lemma cty_open_shift_under_gen j k x τ :
  j <= k ->
  {S k ~> x} (cty_shift j τ) =
  cty_shift j ({k ~> x} τ).
Proof.
  induction τ in j, k |- *;
    cbn [cty_open cty_shift open_one open_cty_atom_inst]; intros Hjk;
    try rewrite ?IHτ1, ?IHτ2 by lia; try reflexivity.
  - rewrite (qual_open_shift_from_under_gen (S j) (S k)) by lia. reflexivity.
  - rewrite (qual_open_shift_from_under_gen (S j) (S k)) by lia. reflexivity.
Qed.

Lemma cty_open_shift_under j k x τ :
  j <= k ->
  {S (S k) ~> x} (cty_shift (S j) τ) =
  cty_shift (S j) ({S k ~> x} τ).
Proof.
  intros Hjk. apply cty_open_shift_under_gen. lia.
Qed.

Lemma cty_shift_open_commute k x τ :
  {S (S k) ~> x} (cty_shift (S k) τ) =
  cty_shift (S k) ({S k ~> x} τ).
Proof.
  apply cty_open_shift_under_gen. lia.
Qed.

Lemma cty_open_same_index_absorb k x y τ :
  x <> y ->
  x ∉ fv_cty τ ->
  y ∉ fv_cty τ ->
  {k ~> y} ({k ~> x} τ) = {k ~> x} τ.
Proof.
  induction τ as [b φ|b φ|τ1 IHτ1 τ2 IHτ2|τ1 IHτ1 τ2 IHτ2
                 |τ1 IHτ1 τ2 IHτ2|τ1 IHτ1 τ2 IHτ2|τ1 IHτ1 τ2 IHτ2]
    in k |- *; cbn [cty_open open_one open_cty_atom_inst];
    intros Hxy Hx Hy.
  - rewrite qual_open_same_index_absorb; try exact Hxy.
    + reflexivity.
    + unfold qual_dom. intros Hbad. apply Hx.
      unfold fv_cty, context_ty_lvars. cbn [context_ty_lvars_at].
      rewrite lvars_fv_lvars_at_depth. exact Hbad.
    + unfold qual_dom. intros Hbad. apply Hy.
      unfold fv_cty, context_ty_lvars. cbn [context_ty_lvars_at].
      rewrite lvars_fv_lvars_at_depth. exact Hbad.
  - rewrite qual_open_same_index_absorb; try exact Hxy.
    + reflexivity.
    + unfold qual_dom. intros Hbad. apply Hx.
      unfold fv_cty, context_ty_lvars. cbn [context_ty_lvars_at].
      rewrite lvars_fv_lvars_at_depth. exact Hbad.
    + unfold qual_dom. intros Hbad. apply Hy.
      unfold fv_cty, context_ty_lvars. cbn [context_ty_lvars_at].
      rewrite lvars_fv_lvars_at_depth. exact Hbad.
  - rewrite IHτ1, IHτ2 by (try exact Hxy; unfold fv_cty in *;
      cbn [context_ty_lvars context_ty_lvars_at] in *; rewrite lvars_fv_union in *; set_solver).
    reflexivity.
  - rewrite IHτ1, IHτ2 by (try exact Hxy; unfold fv_cty in *;
      cbn [context_ty_lvars context_ty_lvars_at] in *; rewrite lvars_fv_union in *; set_solver).
    reflexivity.
  - rewrite IHτ1, IHτ2 by (try exact Hxy; unfold fv_cty in *;
      cbn [context_ty_lvars context_ty_lvars_at] in *; rewrite lvars_fv_union in *; set_solver).
    reflexivity.
  - assert (Hx1 : x ∉ fv_cty τ1).
    { intros Hbad. apply Hx. unfold fv_cty, context_ty_lvars.
      cbn [context_ty_lvars_at]. rewrite lvars_fv_union.
      apply elem_of_union. left. rewrite context_ty_lvars_fv_at. exact Hbad. }
    assert (Hy1 : y ∉ fv_cty τ1).
    { intros Hbad. apply Hy. unfold fv_cty, context_ty_lvars.
      cbn [context_ty_lvars_at]. rewrite lvars_fv_union.
      apply elem_of_union. left. rewrite context_ty_lvars_fv_at. exact Hbad. }
    assert (Hx2 : x ∉ fv_cty τ2).
    { intros Hbad. apply Hx. unfold fv_cty, context_ty_lvars.
      cbn [context_ty_lvars_at]. rewrite lvars_fv_union.
      apply elem_of_union. right. rewrite context_ty_lvars_fv_at. exact Hbad. }
    assert (Hy2 : y ∉ fv_cty τ2).
    { intros Hbad. apply Hy. unfold fv_cty, context_ty_lvars.
      cbn [context_ty_lvars_at]. rewrite lvars_fv_union.
      apply elem_of_union. right. rewrite context_ty_lvars_fv_at. exact Hbad. }
    f_equal.
    + apply IHτ1; assumption.
    + apply IHτ2; assumption.
  - assert (Hx1 : x ∉ fv_cty τ1).
    { intros Hbad. apply Hx. unfold fv_cty, context_ty_lvars.
      cbn [context_ty_lvars_at]. rewrite lvars_fv_union.
      apply elem_of_union. left. rewrite context_ty_lvars_fv_at. exact Hbad. }
    assert (Hy1 : y ∉ fv_cty τ1).
    { intros Hbad. apply Hy. unfold fv_cty, context_ty_lvars.
      cbn [context_ty_lvars_at]. rewrite lvars_fv_union.
      apply elem_of_union. left. rewrite context_ty_lvars_fv_at. exact Hbad. }
    assert (Hx2 : x ∉ fv_cty τ2).
    { intros Hbad. apply Hx. unfold fv_cty, context_ty_lvars.
      cbn [context_ty_lvars_at]. rewrite lvars_fv_union.
      apply elem_of_union. right. rewrite context_ty_lvars_fv_at. exact Hbad. }
    assert (Hy2 : y ∉ fv_cty τ2).
    { intros Hbad. apply Hy. unfold fv_cty, context_ty_lvars.
      cbn [context_ty_lvars_at]. rewrite lvars_fv_union.
      apply elem_of_union. right. rewrite context_ty_lvars_fv_at. exact Hbad. }
    f_equal.
    + apply IHτ1; assumption.
    + apply IHτ2; assumption.
Qed.

Lemma cty_open_commute_fvar i j x y τ :
  i <> j ->
  x <> y ->
  {i ~> x} ({j ~> y} τ) = {j ~> y} ({i ~> x} τ).
Proof.
  induction τ in i, j |- *; cbn [cty_open open_one open_cty_atom_inst]; intros Hij Hxy;
    try rewrite ?IHτ1, ?IHτ2 by lia; try reflexivity.
  - rewrite qual_open_commute_fvar by (try lia; exact Hxy). reflexivity.
  - rewrite qual_open_commute_fvar by (try lia; exact Hxy). reflexivity.
Qed.
