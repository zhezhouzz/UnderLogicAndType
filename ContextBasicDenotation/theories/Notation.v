(** * ContextBasicDenotation.Notation

    Shared value-specialized surface for the basic denotation layer.

    This file is intentionally notation-only: semantic predicates still live in
    their domain files.  It only centralizes the aliases every proof file was
    repeating by hand. *)

From Stdlib Require Export Logic.ClassicalDescription Logic.ClassicalEpsilon.
From CoreLang Require Export SyntaxNotation BasicTyping BasicTypingProps Instantiation
  InstantiationProps LocallyNamelessProps OperationalProps SmallStep Sugar.
From ContextAlgebra Require Export ResourceInterface ResourceCompat ResourceCore ResourceExtension.
From ContextLogic Require Export FormulaNotation FormulaSemantics.
From ContextTypeLanguage Require Export WF.

Notation StoreT := (Store (V := value)) (only parsing).
Notation LStoreT := (LStore (V := value)) (only parsing).
Notation WorldT := (World (V := value)) (only parsing).
Notation LWorldT := (LWorld (V := value)) (only parsing).
Notation WfWorldT := (WfWorld (V := value)) (only parsing).
Notation FiberExtensionT := (fiber_extension (V := value)) (only parsing).
Notation lstore_bound_part := (@lstore_bound_part value) (only parsing).

Notation "e '·ₜ' v" := (tapp_tm e v)
  (at level 40, left associativity,
   format "e  ·ₜ  v").

Notation "'↑{' k '}' v" := (value_shift k v)
  (at level 20, k constr, only printing,
   format "↑{ k }  v") : core_scope.
Notation "'↑{' k '}' e" := (tm_shift k e)
  (at level 20, k constr, only printing,
   format "↑{ k }  e") : core_scope.
Notation "v '↑'" := (value_shift 0 v)
  (at level 20, only printing,
   format "v  ↑") : core_scope.
Notation "e '↑'" := (tm_shift 0 e)
  (at level 20, only printing,
   format "e  ↑") : core_scope.

Global Notation open_tm_env :=
  (fun η e => map_fold (fun k x acc => open_tm k (vfvar x) acc) e η)
  (only parsing).
