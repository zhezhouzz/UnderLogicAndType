# TLet Proof Status

This note records the current boundary of the `tlet` proof work after the
cleanup of obsolete result-equivalence routes.

## Current Main Route

The active proof path is:

1. `ChoiceTyping/theories/LetResultWorld.v` defines the exact operational
   result world `let_result_world_on e x m`.
2. `ChoiceTyping/theories/ResultWorldExprContFamily.v` connects result worlds with
   `FExprContIn`.
3. `ChoiceTyping/theories/TLetDenotation.v` uses that bridge in
   `FExprCont_tlet_reduction`, then lifts the result through
   `denot_ty_fuel_tlet_reduction_formula`.
4. `denot_tlet_total_semantic` is the statement currently used by
   `ChoiceTyping/theories/Soundness.v`.

The intended principle is that the intermediate coordinate `x` is introduced
by `let_result_world_on e1 x m` before the final result coordinate `ν` is
introduced by `FExprContIn`.  This is the point where the proof tracks the
`input -> x -> ν` pairing.

## Stable Building Blocks

In `ChoiceTyping/theories/LetResultWorld.v`:

- `let_result_world_on_member`
- `let_result_world_on_elim`
- `let_result_world_on_dom`
- `let_result_world_on_restrict`
- `let_result_world_on_restrict_input`
- `let_result_world_on_le`
- `let_result_world_on_tlete_decompose`

In `ChoiceTyping/theories/ResultWorldExprContFamily.v`:

- `FExprContIn_to_let_result_world_on_exact_domain`
- `let_result_world_on_to_FExprContIn_exact_domain`
- `FExprContIn_iff_let_result_world_on_exact_domain`

In `ChoiceTyping/theories/TLetDenotation.v`:

- `FExprCont_tlet_reduction`
- `denot_ty_fuel_tlet_reduction_formula`
- `denot_ty_tlet_reduction_formula`
- `denot_ty_total_tlet_reduction`
- `denot_tlet_total_semantic`

## Remaining Admitted Pieces

The current tlet route still depends on admitted or partially admitted pieces:

- `denot_ty_fuel_tlet_reduction_formula_on_arrow_case`
- `denot_ty_fuel_tlet_reduction_formula_on_wand_case`
- `denot_ty_fuel_tlet_reduction_formula_on`
- `expr_total_tlet_reduction`
- `denot_ty_regular_tlet_context_iff`

The older expression-result bridge files, graph route, and the thin
`TLetExprResult.v` wrapper have been removed.

## Removed Routes

The following old modules were deleted because they were no longer part of the
current tlet proof path:

- `ChoiceTyping/theories/ExprResultEquiv.v`
- `ChoiceTyping/theories/TLetExprResult.v`
- `ChoiceTyping/theories/TLetGraph.v`
- `ChoiceTyping/theories/TLetResultBridge.v`

The older long-premise tlet plumbing lemmas were also removed or replaced by
the current continuation-based route.
