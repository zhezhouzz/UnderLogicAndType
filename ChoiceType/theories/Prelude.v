(** * ChoiceType.Prelude

    Imports for the choice-type layer.  Brings in both:
      - [CoreLang] (syntax, small-step, basic typing)
      - [UnderLogicAndType] (substitution, resource, choice logic)

    The instantiation note below explains how the abstract [Var]/[Value]
    parameters of [UnderLogicAndType] are resolved to CoreLang's concrete
    [atom]/[value] types. *)

From CoreLang Require Export Prelude Syntax BasicTyping SmallStep.
From ChoiceLogic Require Export
  Prelude Substitution Resource Formula ChoiceLogicProps.

(** ** Instantiation of UnderLogicAndType's abstract parameters

    [UnderLogicAndType] is parameterized by:
      [Var]   : countable type of program variables  →  [atom]   (= positive)
      [Value] : type of runtime values               →  [value]  (CoreLang.Syntax)

    These instances are resolved automatically since:
      - [Countable atom]      : from CoreLang.Prelude
      - [EqDecision value]    : from CoreLang.Syntax
      - [Inhabited value]     : from CoreLang.Syntax (via [value_inhabited])

    All [Section] variables in UnderLogicAndType are universally
    quantified; at usage sites we specialise them with
    [@... atom _ _ value] or let unification fill them in. *)

(** Convenience abbreviations used throughout ChoiceType. *)
Notation SubstT  := (gmap atom value) (only parsing).
Notation WorldT  := (@World atom _ _ value) (only parsing).
(** [Formula] only discharges [Var], [EqDecision Var], [Countable Var] from the
    ChoiceLogic section — [Value] is not part of [Formula]'s own type. *)
Notation FormulaQ A := (@Formula atom _ _ A) (only parsing).
