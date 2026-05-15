(** * ChoiceType.Prelude

    Imports for the choice-type layer.  Brings in both:
      - [CoreLang] (syntax, small-step, basic typing)
      - [UnderLogicAndType] (substitution, resource, choice logic)

    This layer instantiates the algebra/logic store values with CoreLang
    [value]s. *)

From CoreLang Require Export Prelude Syntax BasicTyping SmallStep.

From ChoiceLogic Require Export Prelude LogicQualifier Formula FormulaTactics ChoiceLogicProps.

(** Fix the abstract algebra/logic value parameter to CoreLang values in the
    choice-type layer. *)
Notation Store := (gmap atom value) (only parsing).
Notation World := (World (V := value)) (only parsing).
Notation WfWorld := (WfWorld (V := value)) (only parsing).
Notation logic_qualifier := (logic_qualifier (V := value)) (only parsing).
Notation Formula := (@FormulaSyntax.Formula value) (only parsing).

(** ChoiceType formulas use logic qualifiers as atoms. *)
Notation FormulaQ := (@FormulaSyntax.Formula value) (only parsing).
