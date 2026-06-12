(** * ContextTyping.SoundnessFix

    Fix proof support for the direct Fundamental theorem.  The outer Arrow
    proof mirrors [SoundnessLam]; the opened-result helper is where the
    well-founded induction over the current argument constant lives. *)

From Stdlib Require Import Lia.
From CoreLang Require Import BasicTyping BasicTypingProps InstantiationProps
  SmallStep StrongNormalization.
From ContextStore Require Import Store.
From ContextAlgebra Require Import ResourceInterface ResourceExtension.
From ContextBasicDenotation Require Import StoreTyping TermExtension TermTLet Qualifier
  BasicTypingFormula RelevantEnv.
From Denotation Require Import Context
  TypeEquivCore
  TypeEquivTerm
  TypeEquiv
  ConstDenote.
From ContextTyping Require Import Typing SoundnessLam.

Local Notation LStoreOnT := (LStoreOn (V := value)) (only parsing).

Local Ltac fix_base_build_union :=
  first
    [ assumption
    | apply elem_of_union_l; fix_base_build_union
    | apply elem_of_union_r; fix_base_build_union ].

Local Ltac fix_base_singleton_side :=
  cbn [fv_tm fv_value] in *;
  repeat match goal with
  | H : ?a ∈ {[?b]} |- _ =>
      apply elem_of_singleton in H; subst
  end;
  repeat match goal with
  | |- ?a ∈ {[?a]} => apply elem_of_singleton; reflexivity
  end.

Lemma ty_denote_lt_arg_fiber
    gas (Δ : lty_env) b x y (m : WfWorldT) :
  x <> y ->
  lty_env_closed Δ ->
  m ⊨ ty_denote_gas (S gas) Δ
        (over_ty b (mk_q_lt_base b (vbvar 0) (vfvar y)))
        (tret (vfvar x)) ->
  forall σ, (m : WorldT) σ ->
    exists cx cy,
      σ !! x = Some (vconst cx) /\
      σ !! y = Some (vconst cy) /\
      constant_lt_for_base b cx cy.
Proof.
Admitted.
