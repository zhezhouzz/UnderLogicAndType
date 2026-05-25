(** * Compatibility entry point for tlet forall-extension lemmas

    The proof content that used to live here has been moved to its natural
    layers:

    - store projection glue: [ChoicePrelude.Store]
    - projected one-point extensions: [ChoiceAlgebra.Resource]
    - forall full-world views and transport: [ChoiceLogic.FormulaForall]

    Keep this file as a thin import target while higher-level denotation files
    are migrated to import the lower layers directly. *)

From ChoicePrelude Require Export Store.
From ChoiceAlgebra Require Export Resource.
From ChoiceLogic Require Export FormulaForall.
