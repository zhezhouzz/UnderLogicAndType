(** * ChoiceTyping.TLetReductionSupport

    Public support prelude for the [tlet] reduction proof.  The actual helper
    lemmas are split by responsibility so recompilation stays more localized. *)

From ChoiceTyping Require Export TLetReductionFuelSupport
  TLetReductionRenameSupport TLetReductionEnvIrrel.

