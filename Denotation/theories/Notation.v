(** * Denotation.Notation

    Common imports and value-specialized notations for top-level denotation
    proofs. *)

From LocallyNameless Require Export Classes Tactics.
From CoreLang Require Export Syntax Sugar BasicTypingProps.
From ContextAlgebra Require Export ResourceInterface ResourceCompat ResourceExtension.
From ContextLogic Require Export FormulaSemantics.
From ContextTypeLanguage Require Export Notation.
From ContextBasicDenotation Require Import Notation.
From ContextBasicDenotation Require Export StoreTyping TermTLet Qualifier BasicTypingFormula.
From ContextLogic Require Export FormulaSemantics FormulaConnectives FormulaWorldExtension.

Notation FormulaT := (Formula (V := value)) (only parsing).
Notation StoreT := (Store (V := value)) (only parsing).
Notation LStoreT := (LStore (V := value)) (only parsing).
Notation WorldT := (World (V := value)) (only parsing).
Notation LWorldT := (LWorld (V := value)) (only parsing).
Notation WfWorldT := (WfWorld (V := value)) (only parsing).
Notation FiberExtensionT := (fiber_extension (V := value)) (only parsing).
Notation LogicQualifierT := (logic_qualifier (V := value)) (only parsing).

Notation "m ⊨ φ" := (res_models m φ)
  (at level 70, format "m  ⊨  φ").

Notation "φ ⊫ ψ" := (entails φ ψ)
  (at level 85, ψ at level 84, no associativity).
