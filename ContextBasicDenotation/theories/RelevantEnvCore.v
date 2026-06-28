(** * BasicDenotation.RelevantEnv

    Syntactic relevant-environment support for denotation guards.

    These definitions do not depend on the recursive context-type denotation:
    they only restrict an lvar-keyed type environment to the lvars mentioned by
    a context type and a term. *)

From ContextBasicDenotation Require Import Notation StoreTyping TermSyntax TermOpen
  BasicTypingFormula.
From ContextBase Require Import BaseTactics.

Section RelevantEnv.

Local Notation "m ⊨ φ" := (res_models m φ)
  (at level 70, format "m  ⊨  φ").

Definition lty_env_restrict_lvars (Σ : lty_env) (D : lvset) : lty_env :=
  storeA_restrict Σ D.

Notation "'context_tm_support' τ e" :=
  (context_ty_lvars τ ∪ tm_lvars e)
  (at level 10, τ at next level, e at next level, only parsing).

Definition relevant_lvars (τ : context_ty) (e : tm) : lvset :=
  context_ty_lvars τ ∪ tm_lvars e.

Definition relevant_env (Σ : lty_env) (τ : context_ty) (e : tm)
    : lty_env :=
  lty_env_restrict_lvars Σ (context_ty_lvars τ ∪ tm_lvars e).


End RelevantEnv.

Notation "'rlv[' τ ']'" :=
  (relevant_lvars τ)
  (at level 20, τ at level 200,
   format "rlv[ τ ]").

Notation "'rlv[' τ ']' e" :=
  (relevant_lvars τ e)
  (at level 20, τ at level 200, e at level 20,
   format "rlv[ τ ]  e").

Notation "'rel[' Σ '|' τ ']'" :=
  (relevant_env Σ τ)
  (at level 20, Σ at level 200, τ at level 200,
   format "rel[ Σ  |  τ ]").

Notation "'rel[' Σ '|' τ ']' e" :=
  (relevant_env Σ τ e)
  (at level 20, Σ at level 200, τ at level 200, e at level 20,
   format "rel[ Σ  |  τ ]  e").
