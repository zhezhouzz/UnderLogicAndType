From ChoiceLogic Require Export
  LogicQualifier
  FormulaSyntax
  Formula
  FormulaTactics
  FormulaDerived
  FormulaWorldExtension
  ChoiceLogicProps
  FormulaNotation.

(** * Public logic interface

    External developments should import this file instead of depending on the
    internal split between qualifier syntax, formula syntax, and models.  The
    current interface exposes the new store-free semantics and the dependent
    lworld qualifier input. *)
