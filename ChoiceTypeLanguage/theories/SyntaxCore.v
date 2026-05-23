(** * ChoiceTypeLanguage.SyntaxCore

    Core syntax and structural functions for choice types and contexts. *)

From ChoiceTypeLanguage Require Export Renaming.

Inductive choice_ty : Type :=
  | CTOver  (b : base_ty) (φ : type_qualifier)
  | CTUnder (b : base_ty) (φ : type_qualifier)
  | CTInter (τ1 τ2 : choice_ty)
  | CTUnion (τ1 τ2 : choice_ty)
  | CTSum   (τ1 τ2 : choice_ty)
  | CTArrow (τx τ : choice_ty)
  | CTWand  (τx τ : choice_ty).

Inductive ctx : Type :=
  | CtxEmpty
  | CtxBind  (x : atom) (τ : choice_ty)
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

Definition logic_var_at_depth (d : nat) (v : logic_var) : option logic_var :=
  match v with
  | LVFree x => Some (LVFree x)
  | LVBound n =>
      if decide (d <= n) then Some (LVBound (n - d)) else None
  end.

Definition lvars_at_depth (d : nat) (D : lvset) : lvset :=
  set_fold (fun v acc =>
    match logic_var_at_depth d v with
    | Some u => {[u]} ∪ acc
    | None => acc
    end) ∅ D.

Fixpoint choice_ty_lvars_at (d : nat) (τ : choice_ty) : lvset :=
  match τ with
  | CTOver _ φ | CTUnder _ φ => lvars_at_depth (S d) (qual_vars φ)
  | CTInter τ1 τ2
  | CTUnion τ1 τ2
  | CTSum τ1 τ2 => choice_ty_lvars_at d τ1 ∪ choice_ty_lvars_at d τ2
  | CTArrow τx τ
  | CTWand τx τ => choice_ty_lvars_at d τx ∪ choice_ty_lvars_at (S d) τ
  end.

Definition choice_ty_lvars (τ : choice_ty) : lvset :=
  choice_ty_lvars_at 0 τ.

Definition choice_ty_open_lvars (k : nat) (x : atom) (τ : choice_ty) : lvset :=
  lvars_open k x (choice_ty_lvars τ).

Definition choice_ty_shift_lvars (τ : choice_ty) : lvset :=
  lvars_shift_from 0 (choice_ty_lvars τ).

Definition fv_cty (τ : choice_ty) : aset :=
  lvars_fv (choice_ty_lvars τ).

Definition bv_cty (τ : choice_ty) : gset nat :=
  lvars_bv (choice_ty_lvars τ).

Fixpoint cty_depth (τ : choice_ty) : nat :=
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

#[global] Instance stale_cty_inst : Stale choice_ty := fv_cty.
#[global] Instance stale_ctx_inst : Stale ctx := ctx_stale.
Arguments stale_cty_inst /.
Arguments stale_ctx_inst /.

Fixpoint cty_open (k : nat) (x : atom) (τ : choice_ty) : choice_ty :=
  match τ with
  | CTOver b φ => CTOver b (qual_open_atom (S k) x φ)
  | CTUnder b φ => CTUnder b (qual_open_atom (S k) x φ)
  | CTInter τ1 τ2 => CTInter (cty_open k x τ1) (cty_open k x τ2)
  | CTUnion τ1 τ2 => CTUnion (cty_open k x τ1) (cty_open k x τ2)
  | CTSum τ1 τ2 => CTSum (cty_open k x τ1) (cty_open k x τ2)
  | CTArrow τx τ => CTArrow (cty_open k x τx) (cty_open (S k) x τ)
  | CTWand τx τ => CTWand (cty_open k x τx) (cty_open (S k) x τ)
  end.

#[global] Instance open_cty_atom_inst : Open atom choice_ty := cty_open.
Arguments open_cty_atom_inst /.

(** [cty_shift] is not a basic opening operation.  It is the binder-depth
    renaming needed by type denotation when moving a type under an additional
    semantic result/value binder. *)
Fixpoint cty_shift (k : nat) (τ : choice_ty) : choice_ty :=
  match τ with
  | CTOver b φ => CTOver b (qual_shift_from (S k) φ)
  | CTUnder b φ => CTUnder b (qual_shift_from (S k) φ)
  | CTInter τ1 τ2 => CTInter (cty_shift k τ1) (cty_shift k τ2)
  | CTUnion τ1 τ2 => CTUnion (cty_shift k τ1) (cty_shift k τ2)
  | CTSum τ1 τ2 => CTSum (cty_shift k τ1) (cty_shift k τ2)
  | CTArrow τx τ => CTArrow (cty_shift k τx) (cty_shift (S k) τ)
  | CTWand τx τ => CTWand (cty_shift k τx) (cty_shift (S k) τ)
  end.

#[global] Instance shift_cty_inst : Shift choice_ty := cty_shift.

Fixpoint erase_ty (τ : choice_ty) : ty :=
  match τ with
  | CTOver b _ => TBase b
  | CTUnder b _ => TBase b
  | CTInter τ1 _ => erase_ty τ1
  | CTUnion τ1 _ => erase_ty τ1
  | CTSum τ1 _ => erase_ty τ1
  | CTArrow τx τ => erase_ty τx →ₜ erase_ty τ
  | CTWand τx τ => erase_ty τx →ₜ erase_ty τ
  end.

Fixpoint lift_ty (s : ty) : choice_ty :=
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

Coercion lift_ty : ty >-> choice_ty.
