(** * ChoiceType.Prelude

    Imports for the choice-type layer.  Brings in both:
      - [CoreLang] (syntax, small-step, basic typing)
      - [UnderLogicAndType] (substitution, resource, choice logic)

    The algebra and logic layers are already instantiated with the global
    [atom] variables and CoreLang [value]s. *)

From CoreLang Require Export Prelude Syntax BasicTyping SmallStep.
From ChoiceLogic Require Export Prelude LogicQualifier Formula ChoiceLogicProps.

(** ChoiceType formulas use logic qualifiers as atoms. *)
Notation FormulaQ := Formula (only parsing).
