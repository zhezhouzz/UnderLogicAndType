(** * ChoiceTyping.ResultWorldExprCont

    Compatibility export for expression-result continuation facts.

    The actual lemmas live in [ChoiceType.TypeDenotation.Formula], because
    they are properties of the [FExprResultAt] formula atom rather than typing
    facts. *)

From ChoiceType Require Export TypeDenotation.Formula.
