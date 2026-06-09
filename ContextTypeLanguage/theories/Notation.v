(** * ContextTypeLanguage.Notation

    Compatibility re-export for older files that imported all context-type
    surface syntax through one module.

    New code should prefer importing the defining layer directly:
    [Syntax] for context/type notation and paper-facing type constructors,
    [TypeOpen] for finite-map opening notation/tactics, [LtyEnv] for
    lvar-environment notation, and [WF] for formation helpers. *)

From CoreLang Require Export SyntaxNotation.
From ContextTypeLanguage Require Export WF.
