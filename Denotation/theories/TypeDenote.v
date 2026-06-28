(** * Denotation.TypeDenote *)

From Denotation Require Import Notation.

Section TypeDenote.

Definition ty_guard_formula
    (Σ : lty_env) (τ : context_ty) (e : tm) : FormulaT :=
  (FWfTy[Σ; τ] ∧
    (FWorld[Σ] ∧
      (FHasType[Σ ⊢ e ⋮ (⌊τ⌋)%cty] ∧ FTotal[e])))%formula.

Definition ty_static_guard_formula
    (Σ : lty_env) (τ : context_ty) (e : tm) : FormulaT :=
  (FWfTy[Σ; τ] ∧
    (FWorld[Σ] ∧ FHasType[Σ ⊢ e ⋮ (⌊τ⌋)%cty]))%formula.

Notation "'guard[' Σ ']' τ" :=
  (ty_guard_formula Σ τ)
  (at level 20, Σ at level 200, τ at level 200,
   format "guard[ Σ ]  τ").

Notation "'guard[' Σ ']' τ e" :=
  (ty_guard_formula Σ τ e)
  (at level 20, Σ at level 200, τ at level 200, e at level 20,
   format "guard[ Σ ]  τ  e").

Notation "'guard[' Σ ';' τ ';' e ']'" :=
  (ty_guard_formula Σ τ e)
  (at level 20, Σ at level 200, τ at level 200, e at level 200,
   format "guard[ Σ ;  τ ;  e ]").

Notation "'static_guard[' Σ ']' τ" :=
  (ty_static_guard_formula Σ τ)
  (at level 20, Σ at level 200, τ at level 200,
   format "static_guard[ Σ ]  τ").

Notation "'static_guard[' Σ ']' τ e" :=
  (ty_static_guard_formula Σ τ e)
  (at level 20, Σ at level 200, τ at level 200, e at level 20,
   format "static_guard[ Σ ]  τ  e").

Notation "'static_guard[' Σ ';' τ ';' e ']'" :=
  (ty_static_guard_formula Σ τ e)
  (at level 20, Σ at level 200, τ at level 200, e at level 200,
   format "static_guard[ Σ ;  τ ;  e ]").

Lemma fiberwise_joinable_on_ty_static_guard_formula X Σ τ e :
  fiberwise_joinable_on X (ty_static_guard_formula Σ τ e).
Proof.
  unfold ty_static_guard_formula.
  apply fiberwise_joinable_on_and.
  - apply fiberwise_joinable_on_context_ty_wf_formula.
  - apply fiberwise_joinable_on_and.
    + apply fiberwise_joinable_on_basic_world_formula.
    + apply fiberwise_joinable_on_expr_basic_typing_formula.
Qed.

Lemma fiberwise_joinable_on_ty_guard_formula X Σ τ e :
  fiberwise_joinable_on X (ty_guard_formula Σ τ e).
Proof.
  unfold ty_guard_formula.
  apply fiberwise_joinable_on_and.
  - apply fiberwise_joinable_on_context_ty_wf_formula.
  - apply fiberwise_joinable_on_and.
    + apply fiberwise_joinable_on_basic_world_formula.
    + apply fiberwise_joinable_on_and.
      * apply fiberwise_joinable_on_expr_basic_typing_formula.
      * apply fiberwise_joinable_on_expr_total_formula.
Qed.

Lemma fiberwise_joinable_ty_static_guard_formula Σ τ e :
  fiberwise_joinable (ty_static_guard_formula Σ τ e).
Proof. intros X. apply fiberwise_joinable_on_ty_static_guard_formula. Qed.

Lemma fiberwise_joinable_ty_guard_formula Σ τ e :
  fiberwise_joinable (ty_guard_formula Σ τ e).
Proof. intros X. apply fiberwise_joinable_on_ty_guard_formula. Qed.

Definition result_basic_typing_formula (b : base_ty) : FormulaT :=
  FHasType[(∅ ▷ TBase b)%lvar ⊢ (ret # 0)%core ⋮ TBase b].

Definition over_result_body (b : base_ty) (φ : type_qualifier) : FormulaT :=
  (over (@atom φ ∧ result_basic_typing_formula b))%formula.

Definition under_result_body (b : base_ty) (φ : type_qualifier) : FormulaT :=
  (under (@atom φ ∧ result_basic_typing_formula b))%formula.

Lemma formula_fv_result_basic_typing_formula b :
  formula_fv (result_basic_typing_formula b) = ∅.
Proof.
  unfold result_basic_typing_formula.
  rewrite formula_fv_expr_basic_typing_formula.
  rewrite typed_lty_env_bind_dom, dom_empty_L.
  rewrite lvars_fv_union, lvars_shift_from_fv,
    lvars_fv_empty, lvars_fv_singleton_bound.
  set_solver.
Qed.

Definition arrow_value_denote_gas_with
    (denote : nat -> lty_env -> context_ty -> tm -> FormulaT)
    (gas : nat) (Σ : lty_env) (τx τr : context_ty) (ef : tm) :
    FormulaT :=
  let Σx := (Σ ▷ (⌊τx⌋)%cty)%lvar in
  (∀.
    denote gas Σx (τx ↑)%cty (ret # 0)%core →
    denote gas Σx τr ((ef ↑)%core ·ₜ # 0))%formula.

Definition wand_value_denote_gas_with
    (denote : nat -> lty_env -> context_ty -> tm -> FormulaT)
    (gas : nat) (Σ : lty_env) (τx τr : context_ty) (ef : tm) :
    FormulaT :=
  let Σx := (Σ ▷ (⌊τx⌋)%cty)%lvar in
  (denote gas Σx (τx ↑)%cty (ret # 0)%core -∗[1]
   denote gas Σx τr ((ef ↑)%core ·ₜ # 0))%formula.

Fixpoint ty_denote_gas
    (gas : nat) (Σ : lty_env) (τ : context_ty) (e : tm)
    {struct gas} : FormulaT :=
  let Σg := relevant_env Σ τ e in
  (guard[Σg; τ; e] ∧
    (match gas with
    | 0 => ⊤
    | S gas' =>
      match τ with
      | CTOver b φ =>
          (∀.
            FResult[(⇑ₗ (dom Σg))%lvar ⊢ (e ↑)%core ⇓ #ₗ 0] →
            fib (qual_vars φ ∖ {[LVBound 0]}) |>
              over (@atom φ ∧
                FHasType[(∅ ▷ TBase b)%lvar ⊢ (ret # 0)%core ⋮ TBase b]))%formula
      | CTUnder b φ =>
          (∀.
            FResult[(⇑ₗ (dom Σg))%lvar ⊢ (e ↑)%core ⇓ #ₗ 0] →
            fib (qual_vars φ ∖ {[LVBound 0]}) |>
              under (@atom φ ∧
                FHasType[(∅ ▷ TBase b)%lvar ⊢ (ret # 0)%core ⋮ TBase b]))%formula
      | CTInter τ1 τ2 =>
          (ty_denote_gas gas' Σ τ1 e ∧
           ty_denote_gas gas' Σ τ2 e)%formula
      | CTUnion τ1 τ2 =>
          (ty_denote_gas gas' Σ τ1 e ∨
           ty_denote_gas gas' Σ τ2 e)%formula
      | CTSum τ1 τ2 =>
          let Σr := (Σg ▷ (⌊τ1⌋)%cty)%lvar in
          (∀.
            FResult[(⇑ₗ (dom Σg))%lvar ⊢ (e ↑)%core ⇓ #ₗ 0] →
            ty_denote_gas gas' Σr (τ1 ↑)%cty (ret # 0)%core ⊕
            ty_denote_gas gas' Σr (τ2 ↑)%cty (ret # 0)%core)%formula
      | CTArrow τx τr =>
          let Σf := (Σg ▷ (⌊(τx → τr)%cty⌋)%cty)%lvar in
          (∀.
            FResult[(⇑ₗ (dom Σg))%lvar ⊢ (e ↑)%core ⇓ #ₗ 0] →
            arrow_value_denote_gas_with ty_denote_gas gas' Σf
              (τx ↑)%cty (↑{1} τr)%cty (ret # 0)%core)%formula
      | CTWand τx τr =>
          let Σf := (Σg ▷ (⌊(τx -∗ τr)%cty⌋)%cty)%lvar in
          (∀.
            FResult[(⇑ₗ (dom Σg))%lvar ⊢ (e ↑)%core ⇓ #ₗ 0] →
            wand_value_denote_gas_with ty_denote_gas gas' Σf
              (τx ↑)%cty (↑{1} τr)%cty (ret # 0)%core)%formula
      | CTPersist τ1 =>
          let Σr := (Σg ▷ (⌊(□ τ1)%cty⌋)%cty)%lvar in
          (∀.
            FResult[(⇑ₗ (dom Σg))%lvar ⊢ (e ↑)%core ⇓ #ₗ 0] →
            □ (ty_denote_gas gas' Σr (τ1 ↑)%cty (ret # 0)%core))%formula
    end
    end))%formula.

Definition arrow_value_denote_gas :=
  arrow_value_denote_gas_with ty_denote_gas.

Definition wand_value_denote_gas :=
  wand_value_denote_gas_with ty_denote_gas.

Definition ty_denote
    (Δ : gmap atom ty) (τ : context_ty) (e : tm) : FormulaT :=
  ty_denote_gas (cty_depth τ) (atom_env_to_lty_env Δ) τ e.

Notation "'⟦ty' τ '⟧[' Σ ',' gas ']'" :=
  (ty_denote_gas gas Σ τ)
  (at level 20, τ at level 200, Σ at level 200, gas at level 9,
   only parsing).

Notation "'⟦ty' τ '⟧[' Σ ',' gas ']' e" :=
  (ty_denote_gas gas Σ τ e)
  (at level 20, τ at level 200, Σ at level 200,
   gas at level 9, e at level 20,
   only parsing).

Notation "'⟦ty' τ '⟧[' Δ ']'" :=
  (ty_denote Δ τ)
  (at level 20, τ at level 200, Δ at level 200,
   only parsing).

Notation "'⟦ty' τ '⟧[' Δ ']' e" :=
  (ty_denote Δ τ e)
  (at level 20, τ at level 200, Δ at level 200, e at level 20,
   only parsing).

Notation "'TyDenote[' Δ ';' τ ';' e ']'" :=
  (ty_denote Δ τ e)
  (at level 20, Δ at level 200, τ at level 200, e at level 200,
   format "TyDenote[ Δ ;  τ ;  e ]").

Notation "'⟦ty⟧[' Σ ',' gas ']' τ" :=
  (ty_denote_gas gas Σ τ)
  (at level 20, Σ at level 200, gas at level 9, τ at level 200,
   format "⟦ty⟧[ Σ ,  gas ]  τ").

Notation "'⟦ty⟧[' Σ ',' gas ']' τ e" :=
  (ty_denote_gas gas Σ τ e)
  (at level 20, Σ at level 200, gas at level 9,
   τ at level 200, e at level 20,
   format "⟦ty⟧[ Σ ,  gas ]  τ  e").

Notation "'⟦ty⟧[' Δ ']' τ" :=
  (ty_denote Δ τ)
  (at level 20, Δ at level 200, τ at level 200,
   format "⟦ty⟧[ Δ ]  τ").

Notation "'⟦ty⟧[' Δ ']' τ e" :=
  (ty_denote Δ τ e)
  (at level 20, Δ at level 200, τ at level 200, e at level 20,
   format "⟦ty⟧[ Δ ]  τ  e").

End TypeDenote.

Notation "'TyDenote[' Δ ';' τ ';' e ']'" :=
  (ty_denote Δ τ e)
  (at level 20, Δ at level 200, τ at level 200, e at level 200,
   format "TyDenote[ Δ ;  τ ;  e ]").
