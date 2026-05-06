(** * ChoiceType.InstantiationProps

    Choice types intentionally do not instantiate the CoreLang
    variable-to-value substitution classes.  Type qualifiers may open
    locally-nameless binders to atoms, and future transport lemmas should be
    stated as atom rename/swap facts rather than value substitution facts.

    This file remains as a small compatibility prelude for modules that import
    the old proof-layer entry point. *)

From ChoiceType Require Export LocallyNamelessProps LocallyNamelessInstances.
