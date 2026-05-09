# Expression Result Semantics

When proving soundness cases that mention Core evaluation, avoid making the
Choice Logic formula layer carry all operational structure.

## Current pattern

Keep the direct expression-result relation as a Rocq-level predicate:

```coq
expr_result_in_world ρ e ν w
```

When the proof is about one concrete store, use the smaller pointwise view:

```coq
expr_result_in_store ρ e ν σ
```

Then lift it to worlds only at the boundary.  This avoids repeatedly
destructing `∀ σ, w σ -> ...` while doing operational `let` decomposition.

Then let the logic atom wrapper be only a shallow embedding:

```coq
expr_logic_qual e ν := lqual (stale e ∪ {[ν]}) ...
FExprResult e ν := FAtom (expr_logic_qual e ν)
```

This makes operational lemmas usable before entering formula proof plumbing.
For `tlete`, use:

- `expr_result_in_store_let_elim`
- `expr_result_in_store_let_intro`
- `expr_result_in_world_let_elim`
- `expr_result_in_world_let_intro`
- `expr_result_in_store_ret_fvar_lookup`
- `expr_result_in_store_ret_fvar_trans`

These lemmas call the CoreLang reduction helpers (`reduction_lete`,
`reduction_lete_intro`) after pushing `msubst` through `tlete`.
The `ret_fvar` lemmas are useful when a proof introduces a fresh coordinate
for a let-bound result and then needs to reuse that coordinate as the result
representative for a body/context typing premise.

Keep input environments and output result stores separate.  In the exact
result semantics, an output store for coordinate `ν` is a singleton:

```coq
{[ν := v]}
```

It should not also be used as the input environment for evaluating `e1` or
`e2`.  For let, the useful store-level shape is:

```coq
subst_map ρ e1 →* tret vx
open_tm 0 vx (subst_map ρ e2) →* tret v
```

paired with output store `{[ν := v]}`.  If a world-level intro needs exactness,
state the projection as an iff over `res_restrict w {[ν]}`.  Keep
`body_tm (subst_map ρ e2)` as a separate regularity premise; it does not follow
from merely knowing the result set of `tlete`.

For over-approximation reasoning, do not try to prove a global reverse bridge
from `FExprResultOn X (tlete e1 e2) ν` to the body result formula.  That would
incorrectly turn a union over all intermediate `vx` into obligations for every
branch.  Use the pointwise decomposition instead:

```coq
expr_result_in_store_tlete_to_body_open_atom
```

It says that a single concrete tlet result can be decomposed into some
intermediate `vx`, then re-expressed as a result of `(e2 ^^ x)` under
`<[x := vx]> ρ`.

Be careful with world-level bridges that erase the input projection.  A lemma
that turns a let-result world over `X` directly into
`expr_result_in_world ∅ (tlete e1 e2) ...` is usually too strong when `X` is
nonempty: the expression still needs the fixed `X` projection as its input
environment.  Prefer store-level pointwise lemmas, or world lemmas parameterized
by the relevant projection store.

Prefer the closed-value version of the substitution fact.  For a returned
variable, proving

```coq
m{σ} (tret (vfvar x)) = tret v
```

only needs `σ !! x = Some v` and `stale v = ∅`; it does not need the whole
store `σ` to be closed.  Use `msubst_ret_fvar_lookup_closed_value` before
falling back to the stronger `msubst_ret_fvar_lookup_closed`.

For the closedness premise on an actual reduction result, use
`basic_steps_result_closed`: preservation turns `e ->* tret v` into a typing
derivation for `tret v`, and empty-context value regularity closes `v`.

When the expression has first been multi-substituted by a store, use
`msubst_basic_typing_tm`.  It tracks the context side with `env_delete σ Γ`:
after substituting every coordinate in `σ`, those coordinates are removed from
the basic typing environment.  If the substituted store covers all variables
used by the expression, the remaining context can usually be shown empty or
irrelevant by the usual fv-in-context lemmas.

## Fiber/set-fold proof plumbing

When lifting an exact result atom through `fib_vars`, avoid leaving implicit
arguments to a large `eapply` if the lemma has many ordinary hypotheses before
the final semantic obligation.  First assert the small set facts, then
instantiate the store/world arguments explicitly.  This prevents Coq from
treating the semantic obligation as an earlier domain-equality subgoal.

When unfolding `fib_vars`, remember that stdpp's `set_fold` exposes a composed
term:

```coq
(foldr fib_vars_acc_step ... ∘ elements) X
```

Run `cbn [compose]` before rewriting with the normal-form lemma:

```coq
unfold fib_vars, fib_vars_acc, set_fold in H.
cbn [compose] in H.
rewrite foldr_fib_vars_acc_fst in H.
```

This is usually cleaner than creating one-off lemmas for each atom shape.

For the common empty-restriction side condition, use:

```coq
store_restrict_empty_set : store_restrict s ∅ = ∅
```

Do not re-prove this locally with a raw `map_eq` in a polymorphic typing proof:
the `gmap`/`Store` instances can become ambiguous outside `ChoicePrelude.Store`.

When a `fib_vars` model on a let-result world must imply that the base world
covers the whole input domain `X`, extract it from scopedness:

```coq
pose proof (res_models_with_store_fuel_scoped _ _ _ _ Hmodel) as Hscope.
```

Then unfold the let-result world domain and use the freshness of the generated
let coordinate `x` to discard the extra `{[x]}` case.

## Important FAtom detail

`FAtom` is upward closed and `logic_qualifier_denote` restricts both the
explicit store and the world to the qualifier domain.  Therefore, destructing

```coq
m ⊨ FExprResult e ν
```

should be unpacked through the fiber layer, not by old global wrappers that
erase the input projection.  In particular, avoid lemmas that turn
`FExprResultOn X e ν` into `expr_result_in_world ∅ e ν ...`; this loses the
store fixed by `fib_vars X`, and is wrong as soon as `X` is nonempty.

Use `fib_vars_models_elim` / `fib_vars_models_intro` to expose the projection
store, then use `FAtom_expr_logic_qual_on_exact` /
`FAtom_expr_logic_qual_on_intro` at the atom layer.  If a proof needs to change
the input domain, construct an explicit fiber/projection witness or prove a
domain-specific lemma; do not rely on arbitrary grow/shrink wrappers.

## Naming wrappers around shallow atoms

When a proof renames a formula atom produced from a shallow qualifier, avoid
normalizing the wrapper stack in the large proof.  Put the normal form in a
small lemma instead.  The useful pattern is:

- prove a `logic_qualifier_denote` lemma for the raw atom, such as
  `logic_qualifier_denote_lift_open_swap_fresh`;
- lift it once to `res_models`, such as
  `res_models_lift_open_rename_fresh`;
- for basic world atoms, do the same with
  `res_models_basic_world_formula_rename_insert_fresh`.

This prevents goals from getting stuck behind nested matches from
`lqual_dom`, `lqual_swap`, and `lift_type_qualifier_to_logic`.  If a scope
goal still exposes those wrappers, unfold only the wrapper definitions needed
for the domain and use a named set equality, rather than asking `set_solver` to
discover the normal form through the match.

For `FExists`/`FForall` wrappers such as `FLetResult_models_elim`, keep the
formula body in a local `set` and use `change` to align both sides to

```coq
res_models_with_store_fuel ... ρ m (formula_rename_atom x y body)
```

before applying `res_models_with_store_fuel_irrel`.  If one side has already
simplified the renamed conjunction and the other has not, `change` is usually
more reliable than another round of unfolding.

## Fiber folds need with-store equivalence

Do not prove atom transport only for `res_models`, because `fib_vars` interprets
its body under an explicit store extended by the current projection.  The right
level is:

```coq
formula_store_equiv φ ψ :=
  forall ρ m, res_models_with_store ρ m φ <-> res_models_with_store ρ m ψ
```

Then prove congruence lemmas for `FAnd`, `FOver`, `FUnder`, and `FFib` before
lifting through `fib_vars`.  The same-set fold case can be proved by unfolding
`set_fold` to `foldr` over `elements`; the harder alpha case
`{x} ∪ X` renamed to `{y} ∪ X` is a separate fiber-commutativity/alpha lemma,
not a property of the shallow atom.

## Design lesson

Do not introduce formula-level bridges such as
`FLetResult -> FExprResult (tlete ...)` unless the statement has been checked
against `FAtom`'s upward-closed semantics.  For let, the operational link
between the intermediate result and the body is store-dependent, so it is safer
to prove the operational relation at the Rocq predicate level first.

## Unsubstituted free-variable returns are impossible exact results

Under the current exact result semantics, `expr_result_store` requires the
result value to be closed:

```coq
stale v = ∅
```

Therefore lemmas whose premise contains

```coq
expr_result_in_store ∅ (tret (vfvar x)) ν σ
```

are usually vacuous.  The proof pattern is:

1. destruct the exact result with `expr_result_store_elim`;
2. simplify `subst_map ∅ (tret (vfvar x))`;
3. use `value_steps_self` to show the result value must be `vfvar x`;
4. simplify `stale (vfvar x)` and finish by set reasoning.

For world-level versions, first use `world_wf` to pick a store from the
nonempty world, project it to `{ν}`, and apply `expr_result_in_world_sound`.
This pattern proved the old `ret_fvar` pullback/trans lemmas without adding
new semantic assumptions.
