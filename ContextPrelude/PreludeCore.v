(** * ContextPrelude.PreludeCore

    Compatibility re-export.  The actual base layer lives in [ContextBase] so
    CoreLang can depend on atom/set/map infrastructure without importing the
    heavier ContextPrelude store interface. *)

From ContextBase Require Export Prelude.
