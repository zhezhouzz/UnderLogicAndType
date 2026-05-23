(** * ChoicePrelude.PreludeCore

    Compatibility re-export.  The actual base layer lives in [ChoiceBase] so
    CoreLang can depend on atom/set/map infrastructure without importing the
    heavier ChoicePrelude store interface. *)

From ChoiceBase Require Export Prelude.
