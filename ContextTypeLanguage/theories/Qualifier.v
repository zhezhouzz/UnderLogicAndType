(** * ContextTypeLanguage.Qualifier

    Compatibility re-export for the unified store-level qualifier.

    The repository now has a single qualifier syntax and semantics in
    [ContextQualifier].  Type-language files continue to import this module so
    existing dependency order and names stay stable, but no second qualifier
    record is defined here. *)

From ContextQualifier Require Export Qualifier.
