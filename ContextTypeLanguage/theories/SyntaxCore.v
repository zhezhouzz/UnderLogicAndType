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
  | CTWand  (τx τ : context_ty)
  | CTPersist (τ : context_ty).

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
Notation "'□' τ" := (CTPersist τ)
  (at level 30, right associativity,
   format "□ τ") : cty_scope.

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
  | CTPersist τ => context_ty_lvars_at d τ
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

Notation "'⇑ₗ' D" := (lvars_shift_from 0 D)
  (at level 20, format "⇑ₗ  D") : lvar_scope.

Fixpoint cty_depth (τ : context_ty) : nat :=
  match τ with
  | CTOver _ _ | CTUnder _ _ => 1
  | CTInter τ1 τ2
  | CTUnion τ1 τ2
  | CTSum τ1 τ2
  | CTArrow τ1 τ2
  | CTWand τ1 τ2 => S (Nat.max (cty_depth τ1) (cty_depth τ2))
  | CTPersist τ => S (cty_depth τ)
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
  | CTPersist τ => CTPersist (cty_open k x τ)
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
  | CTPersist τ => CTPersist (cty_shift k τ)
  end.

#[global] Instance shift_cty_inst : Shift context_ty := cty_shift.
Arguments shift_cty_inst /.

Notation "'↑{' k '}' τ" := (cty_shift k τ)
  (at level 20, k constr,
   format "↑{ k }  τ") : cty_scope.
Notation "τ '↑'" := (cty_shift 0 τ)
  (at level 20,
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
  | CTPersist τ => CTPersist (context_ty_msubst_store σ τ)
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
  | CTPersist τ => erase_ty τ
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
  (at level 20,
   format "⌊ τ ⌋") : cty_scope.

Notation "'⌊' Γ '⌋'" := (erase_ctx Γ)
  (at level 20,
   format "⌊ Γ ⌋") : ctx_scope.


(** Context lifting. *)
Definition lift_ctx (Γ : gmap atom ty) : ctx :=
  map_fold (fun x s acc => CtxComma (CtxBind x (lift_ty s)) acc) CtxEmpty Γ.

Coercion lift_ty : ty >-> context_ty.

(** * ContextTypeLanguage.Syntax

    Lvar support computations for context syntax. *)


(** Variables-equivalence classes live with syntax. *)
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
  | CTPersist τ1, CTPersist τ2 => cty_vars_equiv τ1 τ2
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
    all: destruct τ2; cbn [cty_vars_equiv]; try tauto.
    all: try (intros H; destruct H as [H1 H2]; split; try congruence;
      try symmetry; eauto).
    intros H. eauto.
  - intros τ1 τ2 τ3. induction τ1 in τ2, τ3 |- *.
    all: destruct τ2, τ3; cbn [cty_vars_equiv]; try tauto.
    all: try (intros Hxy Hyz; destruct Hxy as [Hxy1 Hxy2];
      destruct Hyz as [Hyz1 Hyz2]; split; try congruence;
      try etransitivity; eauto).
    intros Hxy Hyz. eauto.
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


(** Paper-facing context-type constructors. *)
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
  match b, c with
  | TUnit, cunit => 0
  | TUnit, cbool false => 0
  | TUnit, cbool true => 1
  | TUnit, cnat n => n
  | TNat, cunit => 0
  | TNat, cnat n => n
  | TNat, cbool false => 0
  | TNat, cbool true => 1
  | TBool, cunit => 0
  | TBool, cbool false => 0
  | TBool, cbool true => 1
  | TBool, cnat n => n
  end.

Definition constant_lt_for_base (b : base_ty) : constant -> constant -> Prop :=
  ltof _ (constant_measure_for_base b).

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


Definition bool_qual (b : bool) : type_qualifier :=
  mk_q_eq (vbvar 0) (vconst (cbool b)).

Definition bool_precise_ty (b : bool) : context_ty :=
  precise_ty TBool (bool_qual b).

Definition const_precise_ty (c : constant) : context_ty :=
  precise_ty (base_ty_of_const c) (mk_q_eq (vbvar 0) (vconst c)).

Notation "'b0:c=' c" := (mk_q_eq (vbvar 0) (vconst c))
  (at level 5, format "b0:c= c").
