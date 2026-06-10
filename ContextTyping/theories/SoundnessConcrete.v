(** * ContextTyping.SoundnessConcrete

    Instantiation of the parameterized soundness theorem with the concrete
    graph-based primitive-operation context. *)

From CoreLang Require Import BasicTyping.
From ContextLogic Require Import FormulaSemantics.
From Denotation Require Import Context.
From ContextTyping Require Import Typing Soundness PrimOpConcreteContext.

Theorem concrete_Fundamental Σ Γ e τ :
  has_context_type concrete_Φ Σ Γ e τ ->
  ctx_denote_under Σ Γ ⊫ ty_denote_under Σ Γ τ e.
Proof.
  apply (Fundamental concrete_Φ concrete_Φ_wf).
Qed.

Theorem concrete_denotational_soundness e τ :
  has_context_type concrete_Φ ∅ CtxEmpty e τ ->
  forall x,
    exists mres : WfWorldT,
      closed_result_world_of e x mres /\
      mres ⊨ ty_denote ({[x := erase_ty τ]} : gmap atom ty) τ
        (tret (vfvar x)).
Proof.
  apply (denotational_soundness concrete_Φ concrete_Φ_wf).
Qed.
