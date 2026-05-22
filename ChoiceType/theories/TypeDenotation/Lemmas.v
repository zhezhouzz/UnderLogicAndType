(** * ChoiceType.TypeDenotation.Lemmas

    Compatibility export for the proof-facing type-denotation API.  The actual
    lemmas are split by layer so future proof work can import only the level it
    needs. *)

From ChoiceType Require Export
  TypeDenotation.LemmasSyntax
  TypeDenotation.LemmasEnv
  TypeDenotation.LemmasFormula
  TypeDenotation.LemmasObligation.
