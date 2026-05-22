(** * ChoiceTyping.TLetReduction

    Thin type-denotation reduction interface for the [tlet] soundness case.

    The old proof body was written against the pre-refactor denotation API
    ([FExprContIn Σ e Q], [FResultBasicWorld], and two-env type denotations).
    Keep the intended theorem statements available so [Soundness] can be
    checked while the new tlet proof route is reviewed. *)

From CoreLang Require Import Instantiation InstantiationProps BasicTypingProps.
From ChoiceLogic Require Export FormulaDerived FormulaWorldExtension.
From ChoiceTyping Require Export TLetExprCont RegularDenotation.
From ChoiceTyping Require Import Naming SoundnessCommon ResultWorldClosed
  ResultWorldExtension.
From ChoiceType Require Import BasicStore DenotationNotation.

Import Tactics.

Lemma denot_ty_tlet_reduction_on
    (Δ : gmap atom ty) (T1 : ty) (e1 e2 : tm)
    (m mx : WfWorld) Fx (x : atom) :
  result_extends e1 x m Fx mx ->
  Δ ⊢ₑ e1 ⋮ T1 ->
  world_dom (m : World) = dom Δ ->
  world_closed_on (dom Δ) m ->
  expr_total_on (tlete e1 e2) m ->
  x ∉ dom Δ ->
  ∀ τ2,
    basic_choice_ty (dom Δ) τ2 ->
    Δ ⊢ₑ tlete e1 e2 ⋮ erase_ty τ2 ->
    mx ⊨ denot_ty_on (<[x:=T1]> Δ) τ2 (e2 ^^ x)
    <->
    m ⊨ denot_ty_on Δ τ2 (tlete e1 e2).
Proof.
Admitted.

Lemma denot_ty_tlet_reduction_ctx_on_ext (τ2 : choice_ty): forall
    (Σ : gmap atom ty) (Γ : ctx) (τ1: choice_ty) e1 e2
    (m mx : WfWorld) Fx x,
  result_extends e1 x m Fx mx ->
  denot_ty_regular_in_ctx_under Σ Γ τ2 ->
  erase_ctx_under Σ Γ ⊢ₑ e1 ⋮ erase_ty τ1 ->
  erase_ctx_under Σ Γ ⊢ₑ tlete e1 e2 ⋮ erase_ty τ2 ->
  world_dom (m : World) = dom (erase_ctx_under Σ Γ) ->
  world_closed_on (dom (erase_ctx_under Σ Γ)) m ->
  expr_total_on (tlete e1 e2) m ->
  x ∉ dom (erase_ctx_under Σ Γ) ∪ fv_cty τ2 ->
  mx ⊨ denot_ty_on (erase_ctx_under Σ (CtxComma Γ (CtxBind x τ1)))
      τ2 (e2 ^^ x)
  <->
  m ⊨ denot_ty_on (erase_ctx_under Σ Γ) τ2 (tlete e1 e2).
Proof.
Admitted.

Lemma denot_ty_tlet_reduction_in_ctx_ext (τ2 : choice_ty): forall
    (Σ : gmap atom ty) (Γ : ctx) (τ1: choice_ty) e1 e2
    (m mx : WfWorld) Fx x,
  result_extends e1 x m Fx mx ->
  denot_ty_regular_in_ctx_under Σ Γ τ2 ->
  erase_ctx_under Σ Γ ⊢ₑ e1 ⋮ erase_ty τ1 ->
  erase_ctx_under Σ Γ ⊢ₑ tlete e1 e2 ⋮ erase_ty τ2 ->
  world_dom (m : World) = dom (erase_ctx_under Σ Γ) ->
  m ⊨ denot_ctx_in_env Σ Γ ->
  expr_total_on (tlete e1 e2) m ->
  x ∉ dom (erase_ctx_under Σ Γ) ∪ fv_cty τ2 ->
  mx ⊨ denot_ty_in_ctx_under Σ (CtxComma Γ (CtxBind x τ1)) τ2 (e2 ^^ x)
  <->
  m ⊨ denot_ty_in_ctx_under Σ Γ τ2 (tlete e1 e2).
Proof.
Admitted.
