(** * ContextTypeLanguage.Syntax

    Core context-type syntax and syntax-only structural lemmas. *)

From Stdlib Require Import Arith.Wf_nat Classes.RelationClasses.
From ContextQualifier Require Export Qualifier.
From ContextBase Require Import BaseTactics.

(** Scopes live next to the syntax they print.  The legacy
    [ContextTypeLanguage.Notation] file re-exports these definitions for
    compatibility, but new files should get the notation by importing the
    corresponding syntax layer directly. *)
Declare Scope cty_scope.
Declare Scope ctx_scope.
Declare Scope lvar_scope.
Delimit Scope cty_scope with cty.
Delimit Scope ctx_scope with ctx.
Delimit Scope lvar_scope with lvar.

Notation "'#ₗ' k" := (LVBound k)
  (at level 5, format "#ₗ k").

Notation "'$ₗ' x" := (LVFree x)
  (at level 5, format "$ₗ x").

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

Bind Scope cty_scope with context_ty.
Bind Scope ctx_scope with ctx.
Bind Scope lvar_scope with logic_var.

Notation "'#ₗ' k" := (LVBound k)
  (at level 5, only parsing) : ctx_scope.

Notation "'$ₗ' x" := (LVFree x)
  (at level 5, only parsing) : ctx_scope.

Notation "'Emp'" := CtxEmpty
  (at level 0, format "Emp") : ctx_scope.

Notation "x '∷' τ" := (CtxBind x τ)
  (at level 60, τ at level 200, no associativity,
   format "x  ∷  τ") : ctx_scope.
Notation "Γ1 ',,' Γ2" := (CtxComma Γ1 Γ2)
  (at level 61, left associativity,
   format "Γ1  ,,  Γ2") : ctx_scope.
Notation "Γ1 '∗' Γ2" := (CtxStar Γ1 Γ2)
  (at level 40, left associativity,
   format "Γ1  ∗  Γ2") : ctx_scope.
Notation "Γ1 '⊕' Γ2" := (CtxSum Γ1 Γ2)
  (at level 70, right associativity,
   format "Γ1  ⊕  Γ2") : ctx_scope.

Notation "τ1 '⊓' τ2" := (CTInter τ1 τ2)
  (at level 40, no associativity,
   format "τ1  ⊓  τ2") : cty_scope.
Notation "τ1 '⊔' τ2" := (CTUnion τ1 τ2)
  (at level 50, no associativity,
   format "τ1  ⊔  τ2") : cty_scope.
Notation "τ1 '⊕' τ2" := (CTSum τ1 τ2)
  (at level 70, right associativity,
   format "τ1  ⊕  τ2") : cty_scope.
Notation "τx '→' τ" := (CTArrow τx τ)
  (at level 99, right associativity,
   format "τx  →  τ") : cty_scope.
Notation "τx '-∗' τ" := (CTWand τx τ)
  (at level 60, right associativity,
   format "τx  -∗  τ") : cty_scope.

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

Notation "'FV' '(' τ ')'" := (fv_cty τ)
  (at level 10, only printing,
   format "FV ( τ )") : cty_scope.

Notation "'FV' '(' D ')'" := (lvars_fv D)
  (at level 10, only printing,
   format "FV ( D )") : lvar_scope.

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

Notation "'FV' '(' Γ ')'" := (ctx_fv Γ)
  (at level 10, only printing,
   format "FV ( Γ )") : ctx_scope.

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

Notation "'{' k '~>' x '}' τ" := (cty_open k x τ)
  (at level 20, k constr, only printing,
   format "{ k ~> x } τ") : cty_scope.
Notation "τ '^^' x" := (cty_open 0 x τ)
  (at level 20, only printing) : cty_scope.

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
Arguments shift_cty_inst /.

Notation "'↑{' k '}' τ" := (cty_shift k τ)
  (at level 20, k constr, only printing,
   format "↑{ k }  τ") : cty_scope.
Notation "τ '↑'" := (cty_shift 0 τ)
  (at level 20, only printing,
   format "τ  ↑") : cty_scope.

Fixpoint context_ty_msubst_store
    (σ : gmap atom value) (τ : context_ty) : context_ty :=
  match τ with
  | CTOver b φ => CTOver b (qual_msubst_store σ φ)
  | CTUnder b φ => CTUnder b (qual_msubst_store σ φ)
  | CTInter τ1 τ2 =>
      CTInter (context_ty_msubst_store σ τ1) (context_ty_msubst_store σ τ2)
  | CTUnion τ1 τ2 =>
      CTUnion (context_ty_msubst_store σ τ1) (context_ty_msubst_store σ τ2)
  | CTSum τ1 τ2 =>
      CTSum (context_ty_msubst_store σ τ1) (context_ty_msubst_store σ τ2)
  | CTArrow τx τ =>
      CTArrow (context_ty_msubst_store σ τx) (context_ty_msubst_store σ τ)
  | CTWand τx τ =>
      CTWand (context_ty_msubst_store σ τx) (context_ty_msubst_store σ τ)
  end.

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

#[global] Instance erase_cty_inst : Erase context_ty ty := erase_ty.
#[global] Instance erase_ctx_inst : Erase ctx (gmap atom ty) := erase_ctx.
Arguments erase_cty_inst /.
Arguments erase_ctx_inst /.

Notation "'⌊' τ '⌋'" := (erase_ty τ)
  (at level 20, only printing,
   format "⌊ τ ⌋") : cty_scope.

Notation "'⌊' Γ '⌋'" := (erase_ctx Γ)
  (at level 20, only printing,
   format "⌊ Γ ⌋") : ctx_scope.

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

Definition lift_ctx (Γ : gmap atom ty) : ctx :=
  map_fold (fun x s acc => CtxComma (CtxBind x (lift_ty s)) acc) CtxEmpty Γ.

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

Fixpoint lvar_value_keys (v : value) : lvset :=
  match v with
  | vconst _ => ∅
  | vfvar x => {[LVFree x]}
  | vbvar k => {[LVBound k]}
  | vlam _ e => tm_lvars e
  | vfix _ vf => lvar_value_keys vf
  end.

Definition denote_lvar_value (σ : LStore (V := value)) (v : value) : option value :=
  match v with
  | vbvar k => (σ : gmap logic_var value) !! LVBound k
  | vfvar x => (σ : gmap logic_var value) !! LVFree x
  | vconst c => Some (vconst c)
  | vlam T e => Some (vlam T e)
  | vfix T vf => Some (vfix T vf)
  end.

Definition mk_q_eq (v1 v2 : value) : type_qualifier :=
  tqual (lvar_value_keys v1 ∪ lvar_value_keys v2)
    (fun σ => denote_lvar_value (lso_store σ) v1 =
              denote_lvar_value (lso_store σ) v2).

(** Default well-founded orders used by context-type fixed points.  This is
    the HAT-style construction: each base type chooses a measure into [nat],
    and recursive calls are required to decrease under that measure. *)
Definition constant_measure_for_base (b : base_ty) (c : constant) : nat :=
  match c with
  | cnat n => n
  | cbool false => 0
  | cbool true => 1
  | clist l => foldl Nat.add 0 l
  end.

Definition constant_lt_for_base (b : base_ty) : constant -> constant -> Prop :=
  ltof _ (constant_measure_for_base b).

Lemma constant_lt_for_base_wf b :
  well_founded (constant_lt_for_base b).
Proof.
  unfold constant_lt_for_base.
  apply well_founded_ltof.
Qed.

Notation " c1 '≺[' b ']' c2 " :=
  (constant_lt_for_base b c1 c2) (at level 20, b at next level).

Definition mk_q_lt_base (b : base_ty) (v1 v2 : value) : type_qualifier :=
  tqual (lvar_value_keys v1 ∪ lvar_value_keys v2)
    (fun σ =>
       exists c1 c2,
         denote_lvar_value (lso_store σ) v1 = Some (vconst c1) /\
         denote_lvar_value (lso_store σ) v2 = Some (vconst c2) /\
         c1 ≺[b] c2).

Definition over_ty (b : base_ty) (φ : type_qualifier) : context_ty :=
  CTOver b φ.

Definition under_ty (b : base_ty) (φ : type_qualifier) : context_ty :=
  CTUnder b φ.

Notation "'{:' b '|' φ '}'" := (over_ty b φ)
  (at level 0, b at level 200, φ at level 200,
   format "{: b  |  φ }") : cty_scope.
Notation "'[:' b '|' φ ']'" := (under_ty b φ)
  (at level 0, b at level 200, φ at level 200,
   format "[: b  |  φ ]") : cty_scope.

Definition precise_ty (b : base_ty) (φ : type_qualifier) : context_ty :=
  CTInter (over_ty b φ) (under_ty b φ).

Definition primop_ty
    (arg_b : base_ty) (arg_φ : type_qualifier)
    (ret_b : base_ty) (ret_φ : type_qualifier) : context_ty :=
  CTArrow (over_ty arg_b arg_φ) (precise_ty ret_b ret_φ).

Definition fix_rec_call_ty
    (b : base_ty) (x : atom) (τx τ : context_ty) : context_ty :=
  CTArrow
    (CTInter τx (over_ty b (mk_q_lt_base b (vbvar 0) (vfvar x))))
    τ.

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

Definition bool_qual (b : bool) : type_qualifier :=
  mk_q_eq (vbvar 0) (vconst (cbool b)).

Definition bool_precise_ty (b : bool) : context_ty :=
  precise_ty TBool (bool_qual b).

Definition const_precise_ty (c : constant) : context_ty :=
  precise_ty (base_ty_of_const c) (mk_q_eq (vbvar 0) (vconst c)).

Notation "'b0:c=' c" := (mk_q_eq (vbvar 0) (vconst c))
  (at level 5, format "b0:c= c").
