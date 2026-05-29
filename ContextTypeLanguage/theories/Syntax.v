(** * ContextTypeLanguage.Syntax

    Core context-type syntax and syntax-only structural lemmas. *)

From Stdlib Require Import Classes.RelationClasses.
From ContextTypeLanguage Require Export Qualifier.
From ContextBase Require Import BaseTactics.

(** * ContextTypeLanguage.Syntax

    Core syntax and structural functions for context types and contexts. *)


Inductive context_ty : Type :=
  | CTOver  (b : base_ty) (φ : type_qualifier)
  | CTUnder (b : base_ty) (φ : type_qualifier)
  | CTInter (τ1 τ2 : context_ty)
  | CTUnion (τ1 τ2 : context_ty)
  | CTSum   (τ1 τ2 : context_ty)
  | CTArrow (τx τ : context_ty)
  | CTWand  (τx τ : context_ty).

Inductive ctx : Type :=
  | CtxEmpty
  | CtxBind  (x : atom) (τ : context_ty)
  | CtxComma (Γ1 Γ2 : ctx)
  | CtxStar  (Γ1 Γ2 : ctx)
  | CtxSum   (Γ1 Γ2 : ctx).

Inductive ctx_hole : Type :=
  | CtxHole
  | CtxHoleCtx   (Γ : ctx)
  | CtxHoleComma (Δ1 Δ2 : ctx_hole)
  | CtxHoleStar  (Δ1 Δ2 : ctx_hole)
  | CtxHoleSum   (Δ1 Δ2 : ctx_hole).

Fixpoint plug_ctx (Δ : ctx_hole) (Γ : ctx) : ctx :=
  match Δ with
  | CtxHole             => Γ
  | CtxHoleCtx Γ0       => Γ0
  | CtxHoleComma Δ1 Δ2  => CtxComma (plug_ctx Δ1 Γ) (plug_ctx Δ2 Γ)
  | CtxHoleStar  Δ1 Δ2  => CtxStar  (plug_ctx Δ1 Γ) (plug_ctx Δ2 Γ)
  | CtxHoleSum   Δ1 Δ2  => CtxSum   (plug_ctx Δ1 Γ) (plug_ctx Δ2 Γ)
  end.

Fixpoint context_ty_lvars_at (d : nat) (τ : context_ty) : lvset :=
  match τ with
  | CTOver _ φ | CTUnder _ φ => lvars_at_depth (S d) (qual_vars φ)
  | CTInter τ1 τ2
  | CTUnion τ1 τ2
  | CTSum τ1 τ2 => context_ty_lvars_at d τ1 ∪ context_ty_lvars_at d τ2
  | CTArrow τx τ
  | CTWand τx τ => context_ty_lvars_at d τx ∪ context_ty_lvars_at (S d) τ
  end.

Definition context_ty_lvars (τ : context_ty) : lvset :=
  context_ty_lvars_at 0 τ.

Definition context_ty_open_lvars (k : nat) (x : atom) (τ : context_ty) : lvset :=
  lvars_open k x (context_ty_lvars τ).

Definition context_ty_shift_lvars (τ : context_ty) : lvset :=
  lvars_shift_from 0 (context_ty_lvars τ).

Definition fv_cty (τ : context_ty) : aset :=
  lvars_fv (context_ty_lvars τ).

Definition bv_cty (τ : context_ty) : gset nat :=
  lvars_bv (context_ty_lvars τ).

Fixpoint cty_depth (τ : context_ty) : nat :=
  match τ with
  | CTOver _ _ | CTUnder _ _ => 1
  | CTInter τ1 τ2
  | CTUnion τ1 τ2
  | CTSum τ1 τ2
  | CTArrow τ1 τ2
  | CTWand τ1 τ2 => S (Nat.max (cty_depth τ1) (cty_depth τ2))
  end.

Fixpoint ctx_dom (Γ : ctx) : aset :=
  match Γ with
  | CtxEmpty        => ∅
  | CtxBind x _    => {[x]}
  | CtxComma Γ1 Γ2
  | CtxStar Γ1 Γ2
  | CtxSum Γ1 Γ2 => ctx_dom Γ1 ∪ ctx_dom Γ2
  end.

Fixpoint ctx_stale (Γ : ctx) : aset :=
  match Γ with
  | CtxEmpty        => ∅
  | CtxBind x τ    => {[x]} ∪ fv_cty τ
  | CtxComma Γ1 Γ2
  | CtxStar Γ1 Γ2
  | CtxSum Γ1 Γ2 => ctx_stale Γ1 ∪ ctx_stale Γ2
  end.

Fixpoint ctx_fv (Γ : ctx) : aset :=
  match Γ with
  | CtxEmpty        => ∅
  | CtxBind _ τ    => fv_cty τ
  | CtxComma Γ1 Γ2 => ctx_fv Γ1 ∪ (ctx_fv Γ2 ∖ ctx_dom Γ1)
  | CtxStar Γ1 Γ2
  | CtxSum Γ1 Γ2 => ctx_fv Γ1 ∪ ctx_fv Γ2
  end.

#[global] Instance stale_cty_inst : Stale context_ty := fv_cty.
#[global] Instance stale_ctx_inst : Stale ctx := ctx_stale.
Arguments stale_cty_inst /.
Arguments stale_ctx_inst /.

Fixpoint cty_open (k : nat) (x : atom) (τ : context_ty) : context_ty :=
  match τ with
  | CTOver b φ => CTOver b (qual_open_atom (S k) x φ)
  | CTUnder b φ => CTUnder b (qual_open_atom (S k) x φ)
  | CTInter τ1 τ2 => CTInter (cty_open k x τ1) (cty_open k x τ2)
  | CTUnion τ1 τ2 => CTUnion (cty_open k x τ1) (cty_open k x τ2)
  | CTSum τ1 τ2 => CTSum (cty_open k x τ1) (cty_open k x τ2)
  | CTArrow τx τ => CTArrow (cty_open k x τx) (cty_open (S k) x τ)
  | CTWand τx τ => CTWand (cty_open k x τx) (cty_open (S k) x τ)
  end.

#[global] Instance open_cty_atom_inst : Open atom context_ty := cty_open.
Arguments open_cty_atom_inst /.

(** [cty_shift] is not a basic opening operation.  It is the binder-depth
    renaming needed by context-type denotation when moving a type under an additional
    semantic result/value binder. *)
Fixpoint cty_shift (k : nat) (τ : context_ty) : context_ty :=
  match τ with
  | CTOver b φ => CTOver b (qual_shift_from (S k) φ)
  | CTUnder b φ => CTUnder b (qual_shift_from (S k) φ)
  | CTInter τ1 τ2 => CTInter (cty_shift k τ1) (cty_shift k τ2)
  | CTUnion τ1 τ2 => CTUnion (cty_shift k τ1) (cty_shift k τ2)
  | CTSum τ1 τ2 => CTSum (cty_shift k τ1) (cty_shift k τ2)
  | CTArrow τx τ => CTArrow (cty_shift k τx) (cty_shift (S k) τ)
  | CTWand τx τ => CTWand (cty_shift k τx) (cty_shift (S k) τ)
  end.

#[global] Instance shift_cty_inst : Shift context_ty := cty_shift.

Fixpoint erase_ty (τ : context_ty) : ty :=
  match τ with
  | CTOver b _ => TBase b
  | CTUnder b _ => TBase b
  | CTInter τ1 _ => erase_ty τ1
  | CTUnion τ1 _ => erase_ty τ1
  | CTSum τ1 _ => erase_ty τ1
  | CTArrow τx τ => erase_ty τx →ₜ erase_ty τ
  | CTWand τx τ => erase_ty τx →ₜ erase_ty τ
  end.

Fixpoint lift_ty (s : ty) : context_ty :=
  match s with
  | TBase b => CTOver b qual_top
  | TArrow s1 s2 => CTArrow (lift_ty s1) (lift_ty s2)
  end.

Fixpoint erase_ctx (Γ : ctx) : gmap atom ty :=
  match Γ with
  | CtxEmpty => ∅
  | CtxBind x τ => {[x := erase_ty τ]}
  | CtxComma Γ1 Γ2 => erase_ctx Γ1 ∪ erase_ctx Γ2
  | CtxStar Γ1 Γ2 => erase_ctx Γ1 ∪ erase_ctx Γ2
  | CtxSum Γ1 _ => erase_ctx Γ1
  end.

Definition lift_ctx (Γ : gmap atom ty) : ctx :=
  map_fold (fun x s acc => CtxComma (CtxBind x (lift_ty s)) acc) CtxEmpty Γ.

Notation "τ1 '→,' τ2" := (CTArrow τ1 τ2)
  (at level 30, right associativity).

Coercion lift_ty : ty >-> context_ty.

(** * ContextTypeLanguage.Syntax

    Lvar support computations for context syntax. *)


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

(** * ContextTypeLanguage.Syntax

    Open/shift structural laws for context syntax. *)


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

(** * ContextTypeLanguage.Syntax

    Variables-equivalence and context support lemmas. *)


Fixpoint cty_vars_equiv (τ1 τ2 : context_ty) : Prop :=
  match τ1, τ2 with
  | CTOver b1 φ1, CTOver b2 φ2 =>
      b1 = b2 /\ qual_vars φ1 = qual_vars φ2
  | CTUnder b1 φ1, CTUnder b2 φ2 =>
      b1 = b2 /\ qual_vars φ1 = qual_vars φ2
  | CTInter τ11 τ12, CTInter τ21 τ22
  | CTUnion τ11 τ12, CTUnion τ21 τ22
  | CTSum τ11 τ12, CTSum τ21 τ22
  | CTArrow τ11 τ12, CTArrow τ21 τ22
  | CTWand τ11 τ12, CTWand τ21 τ22 =>
      cty_vars_equiv τ11 τ21 /\ cty_vars_equiv τ12 τ22
  | _, _ => False
  end.

Notation "τ1 ≡τv τ2" := (cty_vars_equiv τ1 τ2)
  (at level 70, no associativity).

Class VarsEquiv (A : Type) := vars_equiv : relation A.

Notation "x ≈v y" := (vars_equiv x y)
  (at level 70, no associativity).

#[global] Instance vars_equiv_context_ty : VarsEquiv context_ty :=
  cty_vars_equiv.

#[global] Instance cty_vars_equiv_equivalence : Equivalence cty_vars_equiv.
Proof.
  split.
  - intro τ. induction τ; cbn [cty_vars_equiv]; try split; eauto.
  - intros τ1 τ2. induction τ1 in τ2 |- *.
    all: destruct τ2; cbn [cty_vars_equiv]; try tauto;
      intros H; destruct H as [H1 H2]; split; try congruence;
      try symmetry; eauto.
  - intros τ1 τ2 τ3. induction τ1 in τ2, τ3 |- *.
    all: destruct τ2, τ3; cbn [cty_vars_equiv]; try tauto;
      intros Hxy Hyz; destruct Hxy as [Hxy1 Hxy2];
      destruct Hyz as [Hyz1 Hyz2]; split; try congruence;
      try etransitivity; eauto.
Qed.

#[global] Instance cty_vars_equiv_preorder : PreOrder cty_vars_equiv.
Proof.
  split.
  - intro τ. reflexivity.
  - intros τ1 τ2 τ3 H12 H23. transitivity τ2; assumption.
Qed.

#[global] Instance vars_equiv_context_ty_equivalence :
  Equivalence (@vars_equiv context_ty vars_equiv_context_ty).
Proof.
  apply cty_vars_equiv_equivalence.
Qed.

#[global] Instance vars_equiv_context_ty_preorder :
  PreOrder (@vars_equiv context_ty vars_equiv_context_ty).
Proof.
  apply cty_vars_equiv_preorder.
Qed.

Lemma cty_vars_equiv_erase τ1 τ2 :
  τ1 ≡τv τ2 ->
  erase_ty τ1 = erase_ty τ2.
Proof.
  induction τ1 in τ2 |- *; destruct τ2; cbn [cty_vars_equiv erase_ty];
    try tauto; intros H; destruct H as [H1 H2]; subst; eauto;
    rewrite ?(IHτ1_1 _ H1), ?(IHτ1_2 _ H2); reflexivity.
Qed.

Lemma cty_vars_equiv_open k x τ1 τ2 :
  τ1 ≡τv τ2 ->
  {k ~> x} τ1 ≡τv {k ~> x} τ2.
Proof.
  induction τ1 in k, τ2 |- *; destruct τ2;
    cbn [cty_vars_equiv cty_open open_one open_cty_atom_inst];
    try tauto; intros H; destruct H as [H1 H2]; split; try congruence;
    try (rewrite !qual_open_atom_vars, H2; reflexivity);
    try (apply IHτ1_1; exact H1);
    try (apply IHτ1_2; exact H2).
Qed.

Lemma cty_vars_equiv_shift_from k τ1 τ2 :
  τ1 ≡τv τ2 ->
  cty_shift k τ1 ≡τv cty_shift k τ2.
Proof.
  induction τ1 in k, τ2 |- *; destruct τ2;
    cbn [cty_vars_equiv cty_shift]; try tauto; intros H;
    destruct H as [H1 H2].
  - split; [congruence |].
    rewrite !qual_shift_from_vars, H2. reflexivity.
  - split; [congruence |].
    rewrite !qual_shift_from_vars, H2. reflexivity.
  - split; [apply IHτ1_1 | apply IHτ1_2]; assumption.
  - split; [apply IHτ1_1 | apply IHτ1_2]; assumption.
  - split; [apply IHτ1_1 | apply IHτ1_2]; assumption.
  - split; [apply IHτ1_1 | apply IHτ1_2]; assumption.
  - split; [apply IHτ1_1 | apply IHτ1_2]; assumption.
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

Lemma erase_ctx_dom_subset Γ :
  dom (erase_ctx Γ) ⊆ ctx_dom Γ.
Proof.
  induction Γ as [|x τ|Γ1 IH1 Γ2 IH2|Γ1 IH1 Γ2 IH2|Γ1 IH1 Γ2 IH2]; simpl.
  - rewrite dom_empty_L. set_solver.
  - intros y Hy.
    apply elem_of_dom in Hy as [v Hy].
    apply elem_of_singleton.
    pose proof (lookup_singleton_Some (M:=gmap atom) x y (erase_ty τ) v) as Hsingle.
    apply Hsingle in Hy as [Hxy _].
    symmetry. exact Hxy.
  - intros y Hy. set_unfold.
    destruct Hy as [Hy | Hy].
    + pose proof (IH1 y Hy). set_solver.
    + pose proof (IH2 y Hy). set_solver.
  - intros y Hy. set_unfold.
    destruct Hy as [Hy | Hy].
    + pose proof (IH1 y Hy). set_solver.
    + pose proof (IH2 y Hy). set_solver.
  - intros y Hy. pose proof (IH1 y Hy). set_solver.
Qed.

Lemma ctx_dom_subset_stale Γ :
  ctx_dom Γ ⊆ ctx_stale Γ.
Proof.
  induction Γ; simpl; set_solver.
Qed.

