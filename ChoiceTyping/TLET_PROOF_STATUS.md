# TLet Proof Status

This note records the current boundary of the `tlet` proof work after moving
the main route away from concrete `let_result_world_on` entrypoints.

## Current Main Route

The active proof path is extension-style:

1. `ChoiceTyping/theories/ResultWorldExtension.v` defines `result_extends` and
   `result_extends_on`, the proof-facing representation of adding the result
   coordinate.
2. `ChoiceTyping/theories/TLetTotal.v` provides the extension-facing context
   update `tlet_body_ctx_from_result_world`.
3. `ChoiceTyping/theories/TLetExprCont.v` states `FExprCont_tlet_reduction`
   directly over `result_extends`.
4. `ChoiceTyping/theories/TLetReduction.v` states the type-denotation tlet
   reduction directly over `result_extends`.
5. `ChoiceTyping/theories/TLetReductionTotal.v` and
   `ChoiceTyping/theories/TLetDenotation.v` use the extension route.

The concrete model in `LetResultWorld.v` remains only as a bottom-level sanity
bridge for the operational construction, not as the public proof entrypoint.

## Stable Building Blocks

In `ChoiceTyping/theories/ResultWorldExtension.v`:

- `result_extends`
- `result_extends_on`
- `result_extends_exists`
- `result_extends_on_exists`
- `result_extends_on_member`
- `result_extends_on_elim`
- `result_extends_on_forall_extension_commute`

In `ChoiceTyping/theories/TLetDenotation.v`:

- `denot_ty_total_tlet_reduction`
- `denot_tlet_total_semantic`

## Remaining Admitted Pieces

The current tlet route still depends on admitted or partially admitted pieces:

- `tlet_body_ctx_from_result_world`
- `expr_total_on_tlete_elim_body_ext`
- `FExprCont_tlet_reduction`
- `denot_ty_tlet_reduction_on_ext_core`
- `expr_total_tlet_reduction`
- `denot_ty_total_tlet_reduction`

The older concrete result-world public wrappers have been removed from the
main tlet files.

## Removed Routes

The following old modules were deleted because they were no longer part of the
current tlet proof path:

- `ChoiceTyping/theories/ExprResultEquiv.v`
- `ChoiceTyping/theories/TLetExprResult.v`
- `ChoiceTyping/theories/TLetGraph.v`
- `ChoiceTyping/theories/TLetResultBridge.v`

The older long-premise tlet plumbing lemmas were also removed or replaced by
the current continuation-based route.
