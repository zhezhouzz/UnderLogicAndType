(** * ContextLogic.FormulaNotation

    Custom-entry notation for Context Logic formulas.  The constructors stay
    available; this file provides a readable object-language surface. *)

From CoreLang Require Export Prelude.
From ContextLogic Require Export FormulaSyntax.

Declare Scope formula_scope.
Delimit Scope formula_scope with formula.
Bind Scope formula_scope with Formula.

Declare Custom Entry form.

Notation "'⊤'" := FTrue : formula_scope.
Notation "'⊥'" := FFalse : formula_scope.
Notation "'@atom' q" := (FAtom q)
  (at level 10, q at level 9) : formula_scope.
Notation "'pure' P" := (FPure P)
  (at level 10, P at level 9) : formula_scope.
Notation "'res' D '|' P" := (FResourceAtom D P)
  (at level 10, D at level 9, P at level 9) : formula_scope.
Notation "'over' φ" := (FOver φ)
  (at level 30, φ at level 30) : formula_scope.
Notation "'under' φ" := (FUnder φ)
  (at level 30, φ at level 30) : formula_scope.
Notation "'fib' D '|>' φ" := (FFibVars D φ)
  (at level 30, D at level 9, φ at level 30) : formula_scope.
Notation "φ ∗ ψ" := (FStar φ ψ)
  (at level 40, left associativity) : formula_scope.
Notation "φ '-∗[' d ']' ψ" := (FBWand d φ ψ)
  (at level 55, d at level 9, right associativity) : formula_scope.
Notation "φ ∧ ψ" := (FAnd φ ψ)
  (at level 80, right associativity) : formula_scope.
Notation "φ ∨ ψ" := (FOr φ ψ)
  (at level 85, right associativity) : formula_scope.
Notation "φ ⊕ ψ" := (FPlus φ ψ)
  (at level 70, right associativity) : formula_scope.
Notation "φ → ψ" := (FImpl φ ψ)
  (at level 99, right associativity) : formula_scope.
Notation "'∀.' φ" := (FForall φ)
  (at level 100, φ at level 200) : formula_scope.
Notation "'{' k '~>' x '}' φ" := (formula_open k x φ)
  (at level 20, k constr,
   format "{ k  ~>  x }  φ") : formula_scope.
Notation "φ '^^' x" := (formula_open 0 x φ)
  (at level 20, x constr,
   format "φ  ^^  x") : formula_scope.
Notation "'{η' η '}' φ" := (formula_open_env η φ)
  (at level 20, η at level 200,
   format "{η  η }  φ") : formula_scope.

Notation "<{ φ }>" := φ (φ custom form at level 99).
Notation "( φ )" := φ (in custom form, φ at level 99, only parsing).
Notation "φ" := φ
  (in custom form at level 0, φ constr at level 0, only parsing).
Notation "'$' '(' φ ')'" := φ
  (in custom form at level 0, φ constr at level 200, only parsing).

Notation "'⊤'" := FTrue (in custom form at level 0, only parsing).
Notation "'⊥'" := FFalse (in custom form at level 0, only parsing).
Notation "'@atom' q" := (FAtom q)
  (in custom form at level 10, q constr at level 9, only parsing).
Notation "'@pure' P" := (FPure P)
  (in custom form at level 10, P constr at level 9, only parsing).
Notation "'@res' D '|' P" := (FResourceAtom D P)
  (in custom form at level 10, D constr at level 9,
   P constr at level 9, only parsing).

Notation "'over' φ" := (FOver φ)
  (in custom form at level 30, φ custom form at level 30, only parsing).
Notation "'under' φ" := (FUnder φ)
  (in custom form at level 30, φ custom form at level 30, only parsing).
Notation "'fib' D '|>' φ" := (FFibVars D φ)
  (in custom form at level 30, D constr at level 9,
   φ custom form at level 30, only parsing).

Notation "φ ∗ ψ" := (FStar φ ψ)
  (in custom form at level 40, left associativity, only parsing).
Notation "φ '-∗[' d ']' ψ" := (FBWand d φ ψ)
  (in custom form at level 55, d constr at level 9,
   right associativity, only parsing).
Notation "φ ∧ ψ" := (FAnd φ ψ)
  (in custom form at level 60, right associativity, only parsing).
Notation "φ ∨ ψ" := (FOr φ ψ)
  (in custom form at level 65, right associativity, only parsing).
Notation "φ ⊕ ψ" := (FPlus φ ψ)
  (in custom form at level 70, right associativity, only parsing).
Notation "φ → ψ" := (FImpl φ ψ)
  (in custom form at level 80, right associativity, only parsing).

Notation "'∀.' φ" := (FForall φ)
  (in custom form at level 90, φ custom form at level 90, only parsing).
Notation "'{η' η '}' φ" := (formula_open_env η φ)
  (in custom form at level 20, η constr at level 200,
   φ custom form at level 20, only parsing).
