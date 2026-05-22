(** * ChoiceType.TypeDenotation.Definitions

    Definition-level infrastructure for choice-type denotations.

    This file intentionally contains the syntax sugar and semantic atoms used
    by the type denotation, but not their proof API.  In particular, typed
    binders and expression continuations live here so that [DenotationType.v]
    can stay focused on the recursive interpretation of choice types. *)

From Stdlib Require Import Logic.FunctionalExtensionality.
From LocallyNameless Require Import Tactics.
From CoreLang Require Import Instantiation InstantiationProps BasicTypingProps
  Sugar.
From ChoiceLogic Require Import FormulaDerived.
From ChoiceType Require Export TypeDenotation.Env.
From ChoiceType Require Import BasicStore BasicTyping LocallyNamelessProps.

Local Notation FQ := FormulaQ.

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

Class Shift A := shift_at : nat → A → A.

Notation "'↑[' k ']' x" := (shift_at k x)
  (at level 20, k at level 9, x at level 20,
   format "↑[ k ]  x").

Definition expr_total_with_store (X : aset) (e : tm)
    (ρ : Store) (m : WfWorld) : Prop :=
  (∀ σ, (m : World) σ → store_closed (store_restrict (ρ ∪ σ) X)) ∧
  ∀ σ, (m : World) σ →
    ∃ vx, subst_map (store_restrict (ρ ∪ σ) X) e →* tret vx.

Fixpoint value_lvars_at (d : nat) (v : value) : lvset :=
  match v with
  | vconst _ => ∅
  | vfvar x => {[LVFree x]}
  | vbvar k =>
      match logic_var_at_depth d (LVBound k) with
      | Some u => {[u]}
      | None => ∅
      end
  | vlam _ e => tm_lvars_at (S d) e
  | vfix _ vf => value_lvars_at (S d) vf
  end
with tm_lvars_at (d : nat) (e : tm) : lvset :=
  match e with
  | tret v => value_lvars_at d v
  | tlete e1 e2 => tm_lvars_at d e1 ∪ tm_lvars_at (S d) e2
  | tprim _ v => value_lvars_at d v
  | tapp v1 v2 => value_lvars_at d v1 ∪ value_lvars_at d v2
  | tmatch v et ef =>
      value_lvars_at d v ∪ tm_lvars_at d et ∪ tm_lvars_at d ef
  end.

Definition value_lvars (v : value) : lvset := value_lvars_at 0 v.
Definition tm_lvars (e : tm) : lvset := tm_lvars_at 0 e.

Fixpoint choice_ty_lvars_at (d : nat) (τ : choice_ty) : lvset :=
  match τ with
  | CTOver _ φ => lvars_at_depth (S d) (qual_vars φ)
  | CTUnder _ φ => lvars_at_depth (S d) (qual_vars φ)
  | CTInter τ1 τ2 => choice_ty_lvars_at d τ1 ∪ choice_ty_lvars_at d τ2
  | CTUnion τ1 τ2 => choice_ty_lvars_at d τ1 ∪ choice_ty_lvars_at d τ2
  | CTSum τ1 τ2 => choice_ty_lvars_at d τ1 ∪ choice_ty_lvars_at d τ2
  | CTArrow τx τ => choice_ty_lvars_at d τx ∪ choice_ty_lvars_at (S d) τ
  | CTWand τx τ => choice_ty_lvars_at d τx ∪ choice_ty_lvars_at (S d) τ
  end.

Definition choice_ty_lvars (τ : choice_ty) : lvset :=
  choice_ty_lvars_at 0 τ.

Definition logic_var_shift_from (k : nat) (v : logic_var) : logic_var :=
  match v with
  | LVFree x => LVFree x
  | LVBound n => if decide (k <= n) then LVBound (S n) else LVBound n
  end.

#[global] Instance shift_logic_var_inst : Shift logic_var :=
  logic_var_shift_from.

Definition lvars_shift_from (k : nat) (D : lvset) : lvset :=
  set_map (shift_at k) D.

#[global] Instance shift_lvars_inst : Shift lvset :=
  lvars_shift_from.

Definition lty_env_shift_from (k : nat) (Σ : lty_env) : lty_env :=
  kmap (shift_at k) Σ.

#[global] Instance shift_lty_env_inst : Shift lty_env :=
  lty_env_shift_from.

#[global] Instance shift_tm_inst : Shift tm := tm_shift.
#[global] Instance shift_value_inst : Shift value := value_shift.

Definition beta_drop_shift_from (k : nat) (β : gmap nat value) : gmap nat value :=
  map_fold (fun n v acc =>
    if decide (n < k) then <[n := v]> acc
    else if decide (n = k) then acc
    else <[Nat.pred n := v]> acc) ∅ β.

Definition qual_shift_from (k : nat) (q : type_qualifier) : type_qualifier :=
  match q with
  | qual D p =>
      qual (↑[k] D)
        (fun β σ ρ => p (beta_drop_shift_from k β) σ ρ)
  end.

#[global] Instance shift_qual_inst : Shift type_qualifier :=
  qual_shift_from.

(** [cty_shift k τ] places [τ] underneath one more semantic value binder.
    Refinement types protect their own result binder, hence the qualifier is
    shifted at [S k], mirroring [cty_open]. *)
Fixpoint cty_shift (k : nat) (τ : choice_ty) : choice_ty :=
  match τ with
  | CTOver b φ => CTOver b (↑[S k] φ)
  | CTUnder b φ => CTUnder b (↑[S k] φ)
  | CTInter τ1 τ2 => CTInter (cty_shift k τ1) (cty_shift k τ2)
  | CTUnion τ1 τ2 => CTUnion (cty_shift k τ1) (cty_shift k τ2)
  | CTSum τ1 τ2 => CTSum (cty_shift k τ1) (cty_shift k τ2)
  | CTArrow τx τ => CTArrow (cty_shift k τx) (cty_shift (S k) τ)
  | CTWand τx τ => CTWand (cty_shift k τx) (cty_shift (S k) τ)
  end.

#[global] Instance shift_choice_ty_inst : Shift choice_ty := cty_shift.

Definition closed_resource_lvar
    (Σ : lty_env) (η : gmap nat atom) (m : WfWorld) : Prop :=
  world_closed_on (lvars_to_atoms η (dom Σ)) m.

Definition expr_total_lvar
    (Σ : lty_env) (e : tm) (η : gmap nat atom)
    (ρ : Store) (m : WfWorld) : Prop :=
  expr_total_with_store (lvars_to_atoms η (dom Σ ∪ tm_lvars e))
    (open_tm_env η e) ρ m.

Definition lty_env_open_lvars (η : gmap nat atom) (Σ : lty_env) : lty_env :=
  map_fold (fun v T acc => <[logic_var_open_env η v := T]> acc) ∅ Σ.

Definition basic_qualifier_lvar_body (D : lvset) (q : type_qualifier) : Prop :=
  qual_vars q ⊆ lvars_shift D ∪ {[LVBound 0]}.

Inductive basic_choice_ty_lvar : lvset → choice_ty → Prop :=
  | BasicL_CTOver D b φ :
      basic_qualifier_lvar_body D φ →
      basic_choice_ty_lvar D (CTOver b φ)
  | BasicL_CTUnder D b φ :
      basic_qualifier_lvar_body D φ →
      basic_choice_ty_lvar D (CTUnder b φ)
  | BasicL_CTInter D τ1 τ2 :
      basic_choice_ty_lvar D τ1 →
      basic_choice_ty_lvar D τ2 →
      basic_choice_ty_lvar D (CTInter τ1 τ2)
  | BasicL_CTUnion D τ1 τ2 :
      basic_choice_ty_lvar D τ1 →
      basic_choice_ty_lvar D τ2 →
      basic_choice_ty_lvar D (CTUnion τ1 τ2)
  | BasicL_CTSum D τ1 τ2 :
      basic_choice_ty_lvar D τ1 →
      basic_choice_ty_lvar D τ2 →
      basic_choice_ty_lvar D (CTSum τ1 τ2)
  | BasicL_CTArrow D τx τ :
      basic_choice_ty_lvar D τx →
      basic_choice_ty_lvar (lvars_shift D ∪ {[LVBound 0]}) τ →
      basic_choice_ty_lvar D (CTArrow τx τ)
  | BasicL_CTWand D τx τ :
      basic_choice_ty_lvar D τx →
      basic_choice_ty_lvar (lvars_shift D ∪ {[LVBound 0]}) τ →
      basic_choice_ty_lvar D (CTWand τx τ).

Inductive basic_value_lvar : lty_env → value → ty → Prop :=
  | BasicLV_Const Γ c :
      basic_value_lvar Γ (vconst c) (TBase (base_ty_of_const c))
  | BasicLV_FVar Γ x T :
      Γ !! LVFree x = Some T →
      basic_value_lvar Γ (vfvar x) T
  | BasicLV_BVar Γ k T :
      Γ !! LVBound k = Some T →
      basic_value_lvar Γ (vbvar k) T
  | BasicLV_Lam Γ Tx e T :
      (∀ x, x ∉ lty_env_atom_dom Γ →
        basic_typing_lvar (<[LVFree x := Tx]> Γ) (e ^^ x) T) →
      basic_value_lvar Γ (vlam Tx e) (Tx →ₜ T)
  | BasicLV_Fix Γ sx T vf (L : aset) :
      (∀ x, x ∉ L →
        basic_value_lvar (<[LVFree x := sx]> Γ) (vf ^^ x)
          ((sx →ₜ T) →ₜ T)) →
      basic_value_lvar Γ (vfix (sx →ₜ T) vf) (sx →ₜ T)
with basic_typing_lvar : lty_env → tm → ty → Prop :=
  | BasicLT_Ret Γ v T :
      basic_value_lvar Γ v T →
      basic_typing_lvar Γ (tret v) T
  | BasicLT_Let Γ e1 e2 T1 T2 :
      basic_typing_lvar Γ e1 T1 →
      (∀ x, x ∉ lty_env_atom_dom Γ →
        basic_typing_lvar (<[LVFree x := T1]> Γ) (e2 ^^ x) T2) →
      basic_typing_lvar Γ (tlete e1 e2) T2
  | BasicLT_Prim Γ op v arg_b ret_b :
      prim_op_type op = (arg_b, ret_b) →
      basic_value_lvar Γ v (TBase arg_b) →
      basic_typing_lvar Γ (tprim op v) (TBase ret_b)
  | BasicLT_App Γ v1 v2 Tx T :
      basic_value_lvar Γ v1 (Tx →ₜ T) →
      basic_value_lvar Γ v2 Tx →
      basic_typing_lvar Γ (tapp v1 v2) T
  | BasicLT_Match Γ v et ef T :
      basic_value_lvar Γ v TBool →
      basic_typing_lvar Γ et T →
      basic_typing_lvar Γ ef T →
      basic_typing_lvar Γ (tmatch v et ef) T.

Definition denot_obligation_parts
    (Σ : lty_env) (τ : choice_ty) (e : tm)
    (η : gmap nat atom) (ρ : Store) (m : WfWorld) : Prop :=
  let Γ := lty_env_open_lvars η Σ in
  let τη := open_cty_env η τ in
  let eη := open_tm_env η e in
  basic_choice_ty_lvar (dom Γ) τη ∧
  basic_typing_lvar Γ eη (erase_ty τη) ∧
  closed_resource_lvar Σ η m ∧
  expr_total_lvar Σ e η ρ m.

Definition FDenotObligationIn (Σ : lty_env) (τ : choice_ty) (e : tm) : FQ :=
  FStoreResourceAtom (dom Σ)
    (denot_obligation_parts Σ τ e).

Definition FClosedResourceIn (Σ : lty_env) : FQ :=
  FStoreResourceAtom (dom Σ)
    (fun η _ m => closed_resource_lvar Σ η m).

Definition typed_lty_env_bind (Σ : lty_env) (T : ty) : lty_env :=
  <[LVBound 0 := T]> (↑[0] Σ).

Definition FForallTypedBody
    (Σ : lty_env) (T : ty) (Q : lty_env -> FQ) : FQ :=
  let Σx := typed_lty_env_bind Σ T in
  FImpl (FClosedResourceIn Σx) (Q Σx).

Definition FForallTypedBind
    (Σ : lty_env) (T : ty) (Q : lty_env -> FQ) : FQ :=
  FForall (FForallTypedBody Σ T Q).

Definition FExprContBody
    (Σ : lty_env) (T : ty) (e : tm) (Q : lty_env -> FQ) : FQ :=
  FForallTypedBody Σ T (fun Σx =>
    FImpl
      (FExprResultAtLvar (dom Σx) (↑[0] e) (LVBound 0))
      (Q Σx)).

Definition FExprContIn
    (Σ : lty_env) (T : ty) (e : tm) (Q : lty_env -> FQ) : FQ :=
  FForall (FExprContBody Σ T e Q).
