(** * ChoicePrelude.Prelude

    Shared concrete aliases for the Rocq development instantiated with the
    global [atom] variables and CoreLang [value]s.  This file sits between the
    abstract algebra/core-language layers and the logic/type layers, so later
    files can reuse the same names instead of redefining them locally. *)

From ChoiceAlgebra Require Export Prelude Store Resource.
From CoreLang Require Export Syntax.

Notation StoreT := (gmap atom value) (only parsing).
Notation RawWorldT := (@World atom _ _ value) (only parsing).
Notation WorldT := (@WfWorld atom _ _ value) (only parsing).
