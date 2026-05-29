(** * ContextBasicDenotation.Notation

    Shared value-specialized surface for the basic denotation layer.

    This file is intentionally notation-only: semantic predicates still live in
    their domain files.  It only centralizes the aliases every proof file was
    repeating by hand. *)

From Stdlib Require Export Logic.ClassicalDescription Logic.ClassicalEpsilon.
From CoreLang Require Export BasicTyping BasicTypingProps Instantiation
  InstantiationProps LocallyNamelessProps OperationalProps SmallStep Sugar.
From ContextAlgebra Require Export ResourceInterface ResourceCompat ResourceCore ResourceExtension.
From ContextLogic Require Export FormulaSemantics.
From ContextTypeLanguage Require Export Interface.

Notation StoreT := (Store (V := value)) (only parsing).
Notation LStoreT := (LStore (V := value)) (only parsing).
Notation WorldT := (World (V := value)) (only parsing).
Notation LWorldT := (LWorld (V := value)) (only parsing).
Notation WfWorldT := (WfWorld (V := value)) (only parsing).
Notation FiberExtensionT := (fiber_extension (V := value)) (only parsing).
Notation LogicQualifierT := (logic_qualifier (V := value)) (only parsing).
Notation lstore_bound_part := (@lstore_bound_part value) (only parsing).
