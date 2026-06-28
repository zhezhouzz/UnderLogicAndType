(** * Regular facts for context-type syntax. *)

From Stdlib Require Import Arith.Wf_nat Classes.RelationClasses.
From ContextTypeLanguage Require Export SyntaxCore.
From ContextBase Require Import BaseTactics.

Lemma erase_ctx_bind_dom x τ :
  dom (erase_ctx (CtxBind x τ)) = ({[x]} : aset).
Proof.
  cbn [erase_ctx].
  apply set_eq. intros z. split.
  - intros Hz.
    apply elem_of_dom in Hz as [T Hz].
    apply (proj1 (lookup_singleton_Some x z (erase_ty τ) T)) in Hz
      as [Hzx _].
    subst z. set_solver.
  - intros Hz.
    apply elem_of_singleton in Hz. subst z.
    apply elem_of_dom. exists (erase_ty τ).
    apply map_lookup_singleton.
Qed.

Lemma erase_ctx_comma_bind_dom Γ y τ :
  dom (erase_ctx (CtxComma Γ (CtxBind y τ))) =
  dom (erase_ctx Γ) ∪ ({[y]} : aset).
Proof.
  cbn [erase_ctx].
  change (dom ((erase_ctx Γ : gmap atom ty) ∪
      ({[y := erase_ty τ]} : gmap atom ty)) =
    dom (erase_ctx Γ) ∪ ({[y]} : aset)).
  apply set_eq. intros z. split.
  - intros Hz.
    apply elem_of_dom in Hz as [T Hlook].
    apply map_lookup_union_Some_raw in Hlook as [Hlook|[_ Hlook]].
    + apply elem_of_union. left. apply elem_of_dom. eauto.
    + apply elem_of_union. right.
      apply (proj1 (lookup_singleton_Some y z (erase_ty τ) T)) in Hlook
        as [-> _].
      set_solver.
  - intros Hz.
    apply elem_of_union in Hz as [Hz|Hz].
    + apply elem_of_dom in Hz as [T Hlook].
      apply elem_of_dom. exists T.
      apply map_lookup_union_Some_raw. left. exact Hlook.
    + apply elem_of_singleton in Hz. subst z.
      destruct ((erase_ctx Γ : gmap atom ty) !! y) as [T|] eqn:HΓ.
      * apply elem_of_dom. exists T.
        apply map_lookup_union_Some_raw. left. exact HΓ.
      * apply elem_of_dom. exists (erase_ty τ).
        apply map_lookup_union_Some_raw. right.
        split; [exact HΓ|apply map_lookup_singleton].
Qed.

Lemma erase_ctx_star_bind_dom Γ y τ :
  dom (erase_ctx (CtxStar Γ (CtxBind y τ))) =
  dom (erase_ctx Γ) ∪ ({[y]} : aset).
Proof.
  cbn [erase_ctx].
  change (dom ((erase_ctx Γ : gmap atom ty) ∪
      ({[y := erase_ty τ]} : gmap atom ty)) =
    dom (erase_ctx Γ) ∪ ({[y]} : aset)).
  apply set_eq. intros z. split.
  - intros Hz.
    apply elem_of_dom in Hz as [T Hlook].
    apply map_lookup_union_Some_raw in Hlook as [Hlook|[_ Hlook]].
    + apply elem_of_union. left. apply elem_of_dom. eauto.
    + apply elem_of_union. right.
      apply (proj1 (lookup_singleton_Some y z (erase_ty τ) T)) in Hlook
        as [-> _].
      set_solver.
  - intros Hz.
    apply elem_of_union in Hz as [Hz|Hz].
    + apply elem_of_dom in Hz as [T Hlook].
      apply elem_of_dom. exists T.
      apply map_lookup_union_Some_raw. left. exact Hlook.
    + apply elem_of_singleton in Hz. subst z.
      destruct ((erase_ctx Γ : gmap atom ty) !! y) as [T|] eqn:HΓ.
      * apply elem_of_dom. exists T.
        apply map_lookup_union_Some_raw. left. exact HΓ.
      * apply elem_of_dom. exists (erase_ty τ).
        apply map_lookup_union_Some_raw. right.
        split; [exact HΓ|apply map_lookup_singleton].
Qed.

Lemma erase_ctx_comma_bind_fresh Γ y τ :
  y ∉ dom (erase_ctx Γ) ->
  erase_ctx (CtxComma Γ (CtxBind y τ)) =
  <[y := erase_ty τ]> (erase_ctx Γ).
Proof.
  intros Hy.
  cbn [erase_ctx].
  apply storeA_union_singleton_insert_fresh. exact Hy.
Qed.

Lemma erase_ctx_star_bind_fresh Γ y τ :
  y ∉ dom (erase_ctx Γ) ->
  erase_ctx (CtxStar Γ (CtxBind y τ)) =
  <[y := erase_ty τ]> (erase_ctx Γ).
Proof.
  intros Hy.
  cbn [erase_ctx].
  apply storeA_union_singleton_insert_fresh. exact Hy.
Qed.


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
  - change ({d + k ~> x} CTPersist τ) with
      (cty_open (d + k) x (CTPersist τ)).
    cbn [cty_open context_ty_lvars_at].
    rewrite IHτ. reflexivity.
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
  - rewrite IHτ. reflexivity.
Qed.

Lemma context_ty_lvars_depth τ d :
  lvars_at_depth d (context_ty_lvars τ) = context_ty_lvars_at d τ.
Proof.
  unfold context_ty_lvars.
  rewrite context_ty_lvars_at_depth. reflexivity.
Qed.

Lemma cty_lvars_open_body_closed_no_fresh
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
  - rewrite IHτ. reflexivity.
Qed.

Lemma context_ty_lvars_fv τ :
  lvars_fv (context_ty_lvars τ) = fv_cty τ.
Proof.
  apply context_ty_lvars_fv_at.
Qed.

Lemma context_ty_lvars_free_notin_of_fv x τ :
  x ∉ fv_cty τ ->
  LVFree x ∉ context_ty_lvars τ.
Proof.
  intros Hx Hbad.
  apply lvars_fv_elem in Hbad.
  rewrite context_ty_lvars_fv in Hbad.
  exact (Hx Hbad).
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
  - rewrite IHτ by exact Hkd. reflexivity.
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
  - rewrite IHτ. reflexivity.
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

Lemma cty_open_fresh_notin τ y z :
  z ∉ fv_cty τ ∪ {[y]} ->
  z ∉ fv_cty ({0 ~> y} τ).
Proof.
  intros Hz.
  pose proof (cty_open_fv_subset 0 y τ) as Hτopen.
  set_solver.
Qed.

Lemma cty_shift_fv k τ :
  fv_cty (cty_shift k τ) = fv_cty τ.
Proof.
  unfold fv_cty, context_ty_lvars.
  rewrite <- (Nat.add_0_l k) at 1.
  rewrite context_ty_lvars_at_shift.
  apply lvars_shift_from_fv.
Qed.

(** * ContextTypeLanguage.Syntax

    Open/shift structural laws for context syntax. *)


Lemma cty_open_preserves_erasure k x τ :
  erase_ty ({k ~> x} τ) = erase_ty τ.
Proof.
  induction τ in k |- *; simpl; try rewrite ?IHτ, ?IHτ1, ?IHτ2; reflexivity.
Qed.

Lemma cty_shift_preserves_erasure k τ :
  erase_ty (cty_shift k τ) = erase_ty τ.
Proof.
  induction τ in k |- *; simpl; try rewrite ?IHτ, ?IHτ1, ?IHτ2; reflexivity.
Qed.

Lemma cty_open_preserves_depth k x τ :
  cty_depth ({k ~> x} τ) = cty_depth τ.
Proof.
  induction τ in k |- *; simpl; try rewrite ?IHτ, ?IHτ1, ?IHτ2; reflexivity.
Qed.

Lemma cty_shift_preserves_depth k τ :
  cty_depth (cty_shift k τ) = cty_depth τ.
Proof.
  induction τ in k |- *; simpl; try rewrite ?IHτ, ?IHτ1, ?IHτ2; reflexivity.
Qed.

Lemma cty_open_shift_under_gen j k x τ :
  j <= k ->
  {S k ~> x} (cty_shift j τ) =
  cty_shift j ({k ~> x} τ).
Proof.
  induction τ in j, k |- *;
    cbn [cty_open cty_shift open_one open_cty_atom_inst]; intros Hjk;
    try rewrite ?IHτ, ?IHτ1, ?IHτ2 by lia; try reflexivity.
  - rewrite (qual_open_shift_from_under_gen (S j) (S k)) by lia. reflexivity.
  - rewrite (qual_open_shift_from_under_gen (S j) (S k)) by lia. reflexivity.
Qed.

Lemma cty_open_commute_fvar i j x y τ :
  i <> j ->
  x <> y ->
  {i ~> x} ({j ~> y} τ) = {j ~> y} ({i ~> x} τ).
Proof.
  induction τ in i, j |- *; cbn [cty_open open_one open_cty_atom_inst]; intros Hij Hxy;
    try rewrite ?IHτ, ?IHτ1, ?IHτ2 by lia; try reflexivity.
  - rewrite qual_open_commute_fvar by (try lia; exact Hxy). reflexivity.
  - rewrite qual_open_commute_fvar by (try lia; exact Hxy). reflexivity.
Qed.

(** * ContextTypeLanguage.Syntax

    Variables-equivalence and context support lemmas. *)



Lemma cty_vars_equiv_erase τ1 τ2 :
  τ1 ≡τv τ2 ->
  erase_ty τ1 = erase_ty τ2.
Proof.
  induction τ1 in τ2 |- *; destruct τ2; cbn [cty_vars_equiv erase_ty];
    try tauto.
  all: try (intros H; destruct H as [H1 H2]; subst; eauto;
    rewrite ?(IHτ1_1 _ H1), ?(IHτ1_2 _ H2); reflexivity).
  intros H. apply IHτ1. exact H.
Qed.

Lemma cty_vars_equiv_open k x τ1 τ2 :
  τ1 ≡τv τ2 ->
  {k ~> x} τ1 ≡τv {k ~> x} τ2.
Proof.
  induction τ1 in k, τ2 |- *; destruct τ2;
    cbn [cty_vars_equiv cty_open open_one open_cty_atom_inst];
    try tauto.
  all: try (intros H; destruct H as [H1 H2]; split; try congruence;
    try (rewrite !qual_open_atom_vars, H2; reflexivity);
    try (apply IHτ1_1; exact H1);
    try (apply IHτ1_2; exact H2)).
  intros H. apply IHτ1. exact H.
Qed.

Lemma ctx_stale_eq_fv_dom Γ :
  ctx_stale Γ = ctx_fv Γ ∪ ctx_dom Γ.
Proof.
  induction Γ; simpl.
  - set_solver.
  - set_solver.
  - apply set_eq. intros z.
    rewrite IHΓ1, IHΓ2.
    rewrite !elem_of_union, elem_of_difference.
    split.
    + intros [[Hzfv1 | Hzdom1] | [Hzfv2 | Hzdom2]].
      * left. left. exact Hzfv1.
      * right. left. exact Hzdom1.
      * destruct (decide (z ∈ ctx_dom Γ1)) as [Hzdom1 | Hznotdom1].
        -- right. left. exact Hzdom1.
        -- left. right. split; [exact Hzfv2 | exact Hznotdom1].
      * right. right. exact Hzdom2.
    + intros [[Hzfv1 | [Hzfv2 Hznotdom1]] | [Hzdom1 | Hzdom2]].
      * left. left. exact Hzfv1.
      * right. left. exact Hzfv2.
      * left. right. exact Hzdom1.
      * right. right. exact Hzdom2.
  - rewrite IHΓ1, IHΓ2. set_solver.
  - rewrite IHΓ1, IHΓ2. set_solver.
Qed.

(** * ContextTypeLanguage.Syntax

    Syntax-shape normalization tactics for context types and contexts.  These
    are deliberately pure: denotation-specific formula atoms should extend
    these tactics rather than duplicate the structural rewrites. *)

Ltac cty_lvars_syntax_norm :=
  cbn [context_ty_lvars context_ty_lvars_at context_ty_open_lvars
    context_ty_shift_lvars];
  rewrite ?cty_open_vars, ?cty_shift_vars;
  rewrite ?context_ty_lvars_fv, ?context_ty_lvars_fv_at;
  rewrite ?context_ty_lvars_over_fv, ?context_ty_lvars_under_fv;
  rewrite ?lvars_fv_union, ?lvars_fv_of_atoms,
    ?lvars_fv_singleton_bound, ?lvars_fv_singleton_free,
    ?lvars_bv_union.

Ltac cty_lvars_syntax_norm_in H :=
  cbn [context_ty_lvars context_ty_lvars_at context_ty_open_lvars
    context_ty_shift_lvars] in H;
  rewrite ?cty_open_vars in H;
  rewrite ?cty_shift_vars in H;
  rewrite ?context_ty_lvars_fv in H;
  rewrite ?context_ty_lvars_fv_at in H;
  rewrite ?context_ty_lvars_over_fv in H;
  rewrite ?context_ty_lvars_under_fv in H;
  rewrite ?lvars_fv_union in H;
  rewrite ?lvars_fv_of_atoms in H;
  rewrite ?lvars_fv_singleton_bound in H;
  rewrite ?lvars_fv_singleton_free in H;
  rewrite ?lvars_bv_union in H.

Ltac cty_fv_syntax_norm :=
  unfold fv_cty, bv_cty;
  cty_lvars_syntax_norm.

Ltac cty_fv_syntax_norm_in H :=
  unfold fv_cty, bv_cty in H;
  cty_lvars_syntax_norm_in H.

Ltac cty_open_syntax_norm :=
  cbn [cty_open open_one open_cty_atom_inst];
  rewrite ?cty_open_preserves_erasure, ?cty_open_preserves_depth.

Ltac cty_open_syntax_norm_in H :=
  cbn [cty_open open_one open_cty_atom_inst] in H;
  rewrite ?cty_open_preserves_erasure in H;
  rewrite ?cty_open_preserves_depth in H.

Ltac cty_shift_syntax_norm :=
  cbn [cty_shift shift shift_cty_inst];
  rewrite ?cty_shift_preserves_erasure, ?cty_shift_preserves_depth;
  rewrite ?cty_shift_fv, ?cty_shift_vars.

Ltac cty_shift_syntax_norm_in H :=
  cbn [cty_shift shift shift_cty_inst] in H;
  rewrite ?cty_shift_preserves_erasure in H;
  rewrite ?cty_shift_preserves_depth in H;
  rewrite ?cty_shift_fv in H;
  rewrite ?cty_shift_vars in H.

Ltac cty_erase_syntax_norm :=
  cbn [erase_ty erase_ctx lift_ty lift_ctx];
  rewrite ?cty_open_preserves_erasure, ?cty_shift_preserves_erasure;
  rewrite ?cty_vars_equiv_erase.

Ltac cty_erase_syntax_norm_in H :=
  cbn [erase_ty erase_ctx lift_ty lift_ctx] in H;
  rewrite ?cty_open_preserves_erasure in H;
  rewrite ?cty_shift_preserves_erasure in H;
  rewrite ?cty_vars_equiv_erase in H.

Ltac ctx_syntax_norm :=
  cbn [ctx_dom ctx_fv ctx_stale erase_ctx plug_ctx];
  rewrite ?ctx_stale_eq_fv_dom;
  store_normalize;
  rewrite ?dom_empty_L, ?dom_singleton_L, ?dom_union_L;
  rewrite ?erase_ctx_bind_dom, ?erase_ctx_comma_bind_dom,
    ?erase_ctx_star_bind_dom.

Ltac ctx_syntax_norm_in H :=
  cbn [ctx_dom ctx_fv ctx_stale erase_ctx plug_ctx] in H;
  rewrite ?ctx_stale_eq_fv_dom in H;
  store_normalize;
  rewrite ?dom_empty_L in H;
  rewrite ?dom_singleton_L in H;
  rewrite ?dom_union_L in H;
  rewrite ?erase_ctx_bind_dom in H;
  rewrite ?erase_ctx_comma_bind_dom in H;
  rewrite ?erase_ctx_star_bind_dom in H.

Ltac type_syntax_norm :=
  cty_fv_syntax_norm;
  cty_open_syntax_norm;
  cty_shift_syntax_norm;
  cty_erase_syntax_norm;
  ctx_syntax_norm.

Ltac type_syntax_norm_in H :=
  cty_fv_syntax_norm_in H;
  cty_open_syntax_norm_in H;
  cty_shift_syntax_norm_in H;
  cty_erase_syntax_norm_in H;
  ctx_syntax_norm_in H.

Ltac type_lvars_norm :=
  repeat match goal with
  | |- context[into_lvars ?X] =>
      let T := type of X in
      lazymatch T with
      | lvset => change (into_lvars X) with X
      | aset => change (into_lvars X) with (lvars_of_atoms X)
      | gmap atom ty => change (into_lvars X) with (lvars_of_atoms (dom X))
      | gmap logic_var ty => change (into_lvars X) with (dom X)
      end
  | H : context[into_lvars ?X] |- _ =>
      let T := type of X in
      lazymatch T with
      | lvset => change (into_lvars X) with X in H
      | aset => change (into_lvars X) with (lvars_of_atoms X) in H
      | gmap atom ty => change (into_lvars X) with (lvars_of_atoms (dom X)) in H
      | gmap logic_var ty => change (into_lvars X) with (dom X) in H
      end
  end.

(** Paper-facing context-type constructors and syntax facts. *)


Lemma constant_lt_for_base_wf b :
  well_founded (constant_lt_for_base b).
Proof.
  unfold constant_lt_for_base.
  apply well_founded_ltof.
Qed.

Notation " c1 '≺[' b ']' c2 " :=
  (constant_lt_for_base b c1 c2) (at level 20, b at next level).


Ltac cty_depth_norm :=
  cbn [cty_depth over_ty under_ty precise_ty primop_ty fix_rec_call_ty];
  rewrite ?cty_open_preserves_depth, ?cty_shift_preserves_depth.

Ltac cty_depth_norm_in H :=
  cbn [cty_depth over_ty under_ty precise_ty primop_ty fix_rec_call_ty] in H;
  rewrite ?cty_open_preserves_depth in H;
  rewrite ?cty_shift_preserves_depth in H.

Ltac cty_depth_solve :=
  cty_depth_norm; lia.

Lemma erase_fix_rec_call_ty b x τx τ t :
  erase_ty τx = TBase b ->
  erase_ty τ = t ->
  erase_ty (fix_rec_call_ty b x τx τ) = (TBase b →ₜ t).
Proof.
  intros Hτx Hτ.
  unfold fix_rec_call_ty, over_ty.
  cbn [erase_ty].
  congruence.
Qed.

Lemma fv_cty_fix_rec_call_ty_subset b x τx τ :
  fv_cty (fix_rec_call_ty b x τx τ) ⊆
    fv_cty τx ∪ {[x]} ∪ fv_cty τ.
Proof.
  intros a Ha.
  unfold fix_rec_call_ty, over_ty, mk_q_lt_base in Ha.
  cty_fv_syntax_norm_in Ha.
  cbn [qual_vars qual_lvars lvar_value_keys] in Ha.
  rewrite !context_ty_lvars_fv_at in Ha.
  rewrite !lvars_fv_lvars_at_depth in Ha.
  repeat rewrite lvars_fv_union in Ha.
  repeat rewrite lvars_fv_singleton_bound in Ha.
  repeat rewrite lvars_fv_singleton_free in Ha.
  apply elem_of_union in Ha as [Ha_left | Haτ].
  - apply elem_of_union in Ha_left as [Haτx | Ha_mid].
    + apply elem_of_union_l. apply elem_of_union_l. exact Haτx.
    + apply elem_of_union in Ha_mid as [Ha_empty | Hay].
      * rewrite elem_of_empty in Ha_empty. contradiction.
      * apply elem_of_union_l. apply elem_of_union_r. exact Hay.
  - apply elem_of_union_r. exact Haτ.
Qed.

Lemma fv_cty_fix_rec_call_ty_fresh b x τx τ z :
  z <> x ->
  z ∉ fv_cty τx ->
  z ∉ fv_cty τ ->
  z ∉ fv_cty (fix_rec_call_ty b x τx τ).
Proof.
  intros Hzx Hzτx Hzτ Hzbad.
  pose proof (fv_cty_fix_rec_call_ty_subset b x τx τ z Hzbad)
    as Hzsub.
  better_set_solver.
Qed.

Lemma fv_cty_over_lt_bound_fvar b x :
  fv_cty (over_ty b (mk_q_lt_base b (vbvar 0) (vfvar x))) = {[x]}.
Proof.
  unfold over_ty, mk_q_lt_base, fv_cty, context_ty_lvars.
  cbn [context_ty_lvars_at qual_vars qual_lvars lvar_value_keys].
  rewrite lvars_at_depth_union.
  rewrite lvars_at_depth_singleton_bound0_succ.
  rewrite lvars_at_depth_singleton_free.
  rewrite lvars_fv_union, lvars_fv_empty, lvars_fv_singleton_free.
  apply set_eq. intros a. set_unfold. tauto.
Qed.

Lemma fv_cty_over_lt_bound_fvar_fresh b x z :
  z <> x ->
  z ∉ fv_cty (over_ty b (mk_q_lt_base b (vbvar 0) (vfvar x))).
Proof.
  intros Hzx.
  rewrite fv_cty_over_lt_bound_fvar.
  intros Hz. apply elem_of_singleton in Hz. congruence.
Qed.
