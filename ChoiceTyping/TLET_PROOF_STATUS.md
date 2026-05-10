# TLet Proof Status

This note records the current boundary of the `tlet` proof work.  The typing
case is not complete.  The stable part is the operational/result-world layer;
the blocked part is the generic transport from expression-result equivalence to
arbitrary `denot_ty_on`.

## Proved building blocks

### Result-world construction

In `ChoiceTyping/theories/LetResultWorld.v`:

- `let_result_world_on_member`
- `let_result_world_on_elim`
- `let_result_world_on_restrict`
- `let_result_world_on_restrict_old`
- `let_result_world_on_restrict_input`
- `let_result_world_on_restrict_input_le`
- `let_result_world_on_restrict_domain`
- `let_result_world_on_le`
- `let_result_world_on_tlete_decompose`

These lemmas describe the exact world produced by adding a fresh result
coordinate for an expression.  The most important one is
`let_result_world_on_tlete_decompose`: nested result worlds for `e1` and
`e2 ^^ x` restrict back to the result world for `tlete e1 e2`.

### Generic bridge between `FExprResultOn` and result worlds

In `ChoiceTyping/theories/ResultWorldBridge.v`:

- `FExprResultOn_iff_let_result_world_on`
- `let_result_world_on_models_FExprResultOn`
- `fresh_forall_expr_result_to_let_result_world_renamed`
- `fresh_forall_expr_result_to_let_result_world`
- `expr_result_equiv_in_world_refl`
- `expr_result_equiv_future_refl`
- `let_result_world_on_expr_result_equiv_in_world`
- `FExprResultOn_transport_by_result_world_equiv`

These lemmas connect the formula-level result atom with the exact operational
result world.  This is the cleanest part of the current tlet infrastructure.

### Tlet expression-result/fiber facts

In `ChoiceTyping/theories/TLetExprResult.v`:

- `fib_vars_obligation_step_commute`
- `expr_result_store_from_body_xfiber`
- `expr_result_in_world_tlete_xfiber_sound`
- `expr_result_in_world_tlete_xfiber_complete`
- `expr_result_in_world_tlete_from_body_xfiber`
- `expr_result_in_world_tlete_from_body_projection_fiber`
- `fib_vars_obligation_tlete_from_body_foldr_base`
- `fib_vars_obligation_tlete_from_body_foldr`
- `fib_vars_obligation_tlete_from_body_normalized`
- `fib_vars_obligation_tlete_from_body_result_world`
- `FExprResultOn_tlete_from_body_result_world`

These lemmas show how the body-side result formula for `e2 ^^ x` can be lifted
through the `x` fiber into the whole-let result formula for `tlete e1 e2`.

One generic fiber lemma remains admitted here:

- `fib_vars_obligation_insert_fresh_to_fib`

It should eventually move to the general `fib_vars` library.

### High-risk expression-result bridge

In `ChoiceTyping/theories/TLetResultBridge.v`:

- `nested_tlet_result_world_source_transport`
- `nested_tlet_result_world_target_transport`
- `nested_body_result_world_models_FExprResultOn`
- `expr_result_model_bridge_tlete`

This is the furthest completed point.  It proves the expression/resource-level
bridge needed by the tlet case, including the exact pairing of input variables,
the intermediate result coordinate `x`, and the final result coordinate `ν`.
This still does not prove the typing rule.

### Operational totality/regularity helpers

In `ChoiceTyping/theories/TLetTotal.v`:

- `expr_total_on_tlete_from_open`
- `expr_result_value_tlete_from_body_projection`
- `expr_result_value_tlete_from_body_store`
- several regularity helpers for closed/lc results and typed results

The representative lemma
`denot_ty_on_let_result_representative` is still admitted and belongs to the
blocked denotation-transport layer.

## Where the tlet proof currently stops

The proof reaches this expression-result bridge:

```coq
expr_result_model_bridge
  (X ∪ {[x]}) (e2 ^^ x)
  X (tlete e1 e2)
  (let_result_world_on X e1 x m ...)
  m
```

Intuitively, this says: if the target world models the exact result atom for the
whole let, then there is a source/body result world that models the exact result
atom for the opened body, and the relevant continuation scopes are transported
between the worlds.

This validates the operational/fiber idea for `tlet`: the `X -> x -> ν` pairing
is preserved by the result-world construction.

## Current blocker

The next intended lemma is in `ChoiceTyping/theories/TLetDenotation.v`:

```coq
denot_ty_on_expr_result_model_bridge_fresh_bind
```

The current statement is too weak.  It assumes only:

```coq
expr_result_model_bridge Xsrc esrc Xtgt etgt msrc mtgt
```

But `expr_result_model_bridge` transports formulas only on the explicit source
and target expression scopes.  An arbitrary `denot_ty_on` may also mention:

- `dom Σ`
- `fv_cty τ`
- `fv_tm esrc`
- `fv_tm etgt`

So the transport theorem needs additional scope/agreement assumptions, for
example:

```coq
dom (<[x := Tx]> Σ) ⊆ Xsrc
dom Σ ⊆ Xtgt
fv_tm esrc ⊆ Xsrc
fv_tm etgt ⊆ Xtgt
```

or an equivalent packaged invariant.  Without these assumptions, the proof
cannot safely turn the expression-result bridge into a theorem about arbitrary
type denotations.

## Incomplete top-level tlet statements

The following are intentionally not complete evidence for the tlet case:

- `denot_tlet_semantic_at_world`
- `denot_ty_on_expr_result_model_bridge_fresh_bind`
- `denot_ty_on_let_result_body_to_let`
- `denot_tlet_formula_at_world_given_bind_total`
- `denot_tlet_formula_at_world_total`
- `denot_tlet_expr_total_at_world_given_bind`
- `denot_tlet_total_at_world_given_bind`
- `denot_tlet_total_at_world`
- `denot_tlet_semantic`

Some of these have `Qed`, but they depend on admitted transport lemmas.  They
should be treated as proof plumbing, not as completed theorems.

## Suggested next step

Repair `denot_ty_on_expr_result_model_bridge_fresh_bind` by adding explicit
scope/agreement premises, then prove it by induction on `τ` or by a more
general formula-locality/transport theorem.  Once that bridge is real, the
existing result-world work should be enough to reconnect the `tlet` typing case.
