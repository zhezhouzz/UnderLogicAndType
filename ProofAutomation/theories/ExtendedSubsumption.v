(** * Case-study semantic subtyping checkpoints

    This file is intentionally proof-automation facing.  Case-study
    refinements should be exposed as ordinary [sub_type_under] lemmas:

      Γ |- τ1 <: τ2

    They can then be consumed by the existing [EXT_Sub] rule.  Avoid
    term-specific subsumption facts here; if a fact only holds for one
    particular program body, it is not a subtype lemma. *)

From stdpp Require Import gmap.
From CoreLang Require Import Syntax.
From ContextTypeLanguage Require Import Syntax.
From Denotation Require Import Context.
From ContextTyping Require Import Typing.
From ProofAutomation Require Export ExtendedTyping.

Open Scope core_scope.
Open Scope case_scope.
Open Scope cty_scope.
Open Scope ctx_scope.

Definition extended_semantic_subtype
    (Σ : gmap atom ty) (Γ : ctx) (τsrc τtgt : context_ty) : Prop :=
  sub_type_under Σ Γ τsrc τtgt.

Definition qualifier_entails (q1 q2 : type_qualifier) : Prop :=
  forall s : LStoreOn (qual_vars q1 ∪ qual_vars q2),
    qual_prop q1 (lstore_on_restrict (qual_vars q1) s ltac:(set_solver)) ->
    qual_prop q2 (lstore_on_restrict (qual_vars q2) s ltac:(set_solver)).

Lemma subtype_over_closed_by_qualifier
    Σ Γ b q1 q2 :
  qual_dom q1 ## ctx_dom Γ ->
  qual_dom q2 ## ctx_dom Γ ->
  qualifier_entails q1 q2 ->
  extended_semantic_subtype Σ Γ
    ({: b | q1 }) ({: b | q2 }).
Proof. Admitted.

Lemma subtype_under_closed_by_qualifier
    Σ Γ b q1 q2 :
  qual_dom q1 ## ctx_dom Γ ->
  qual_dom q2 ## ctx_dom Γ ->
  qualifier_entails q2 q1 ->
  extended_semantic_subtype Σ Γ
    ([: b | q1 ]) ([: b | q2 ]).
Proof. Admitted.

Lemma subtype_vacuous_of_unmodelable_ctx
    Σ Γ τ1 τ2 :
  wf_ctx_under Σ Γ ->
  wf_context_ty_at 0 (dom (erase_ctx Γ)) τ1 ->
  wf_context_ty_at 0 (dom (erase_ctx Γ)) τ2 ->
  erase_ty τ1 = erase_ty τ2 ->
  entails (ctx_denote_under Σ Γ) FFalse ->
  extended_semantic_subtype Σ Γ τ1 τ2.
Proof. Admitted.

Lemma qual_and_idempotent (q : type_qualifier) :
  qual_and q q = q.
Proof. Admitted.

Lemma extended_semantic_subtype_trans
    Σ Γ τ1 τ2 τ3 :
  extended_semantic_subtype Σ Γ τ1 τ2 ->
  extended_semantic_subtype Σ Γ τ2 τ3 ->
  extended_semantic_subtype Σ Γ τ1 τ3.
Proof. Admitted.

Lemma extended_semantic_subtype_inter_left
    Σ Γ τ1 τ2 :
  extended_semantic_subtype Σ Γ (τ1 ⊓ τ2) τ1.
Proof. Admitted.

Lemma extended_semantic_subtype_inter_right
    Σ Γ τ1 τ2 :
  extended_semantic_subtype Σ Γ (τ1 ⊓ τ2) τ2.
Proof. Admitted.

Lemma extended_semantic_subtype_inter_comm
    Σ Γ τ1 τ2 :
  extended_semantic_subtype Σ Γ (τ1 ⊓ τ2) (τ2 ⊓ τ1).
Proof. Admitted.

Lemma subtype_inter_over_under_to_over_part
    Σ Γ b q_over q_under :
  extended_semantic_subtype Σ Γ
    (({: b | q_over }) ⊓ ([: b | q_under ]))
    ({: b | q_over }).
Proof. Admitted.

Lemma subtype_inter_over_under_to_under_and
    Σ Γ b q_over q_under :
  extended_semantic_subtype Σ Γ
    (({: b | q_over }) ⊓ ([: b | q_under ]))
    ([: b | qual_and q_over q_under ]).
Proof. Admitted.

Lemma subtype_inter_over_under_to_over
    Σ Γ b q_over q_under q_tgt :
  extended_semantic_subtype Σ Γ
    ({: b | q_over }) ({: b | q_tgt }) ->
  extended_semantic_subtype Σ Γ
    (({: b | q_over }) ⊓ ([: b | q_under ]))
    ({: b | q_tgt }).
Proof. Admitted.

Lemma subtype_inter_over_under_to_under
    Σ Γ b q_over q_under q_tgt :
  extended_semantic_subtype Σ Γ
    ([: b | qual_and q_over q_under ]) ([: b | q_tgt ]) ->
  extended_semantic_subtype Σ Γ
    (({: b | q_over }) ⊓ ([: b | q_under ]))
    ([: b | q_tgt ]).
Proof. Admitted.

(** ** Figure 5.1 placeholder discipline

    Counterexample discipline:

    - Some tempting facts are false as [τsrc <: τtgt] rules.  For example,
      [O[Bool] <: {: Bool | false}] is false: a function that always returns
      [true] inhabits the source but not the target.
    - Whole-function shortcuts such as the May/May source type subsuming the
      paper target type are false.  The valid checkpoints are local,
      context-dependent operator/result subtypings.
    - The under-approximate examples rely on coverage produced by the concrete
      operator or branch result being typed.  Do not promote an arbitrary
      same-erasure function type to an under refinement. *)
