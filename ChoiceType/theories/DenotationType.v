(** * ChoiceType.DenotationType

    Compatibility export for the refactored type-denotation layer.

    The definitions now live under [ChoiceType.TypeDenotation]:

    - [TypeDenotation.Definitions] contains the semantic atoms and syntax sugar
      such as typed forall, expression continuations, and denotation
      obligations.
    - [TypeDenotation.Lemmas] contains their proof-facing API.
    - [TypeDenotation.Denotation] contains the recursive choice-type
      denotation and the small public wrappers.

    The previous monolithic implementation has been preserved as
    [DenotationType.legacy.v], which is intentionally not listed in
    [_CoqProject]. *)

From ChoiceType Require Export TypeDenotation.Denotation.
