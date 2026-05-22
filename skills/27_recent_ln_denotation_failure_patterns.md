# Recent LN Denotation Failure Patterns

This note records concrete mistakes from the recent TypeDenotation/tlet proof
work.  Read it before continuing LN helper proofs, especially in
`ChoiceType/theories/TypeDenotation/*`.

The goal is not to remember one proof script, but to avoid repeating the same
classes of errors: choosing the wrong lemma level, forgetting existing helpers,
fighting overloaded notation in the wrong proof, and unfolding too much in
high-level denotation proofs.

## Start every helper by searching the local API

Before inventing a lemma, search for the exact concept and its nearby variants.

Use targeted searches such as:

```sh
rg -n "open_cty_env|cty_open|qual_open|formula_open|typed_lty_env_bind" ChoiceType/theories -S
rg -n "lvars_fv|lvars_bv|lvars_shift|dom .*shift|lookup_kmap" ChoiceType/theories ChoicePrelude -S
rg -n "FExprContIn|FForallTypedBind|FDenotObligationIn|formula_store_equiv" ChoiceType/theories/TypeDenotation -S
```

Then read the definitions and the closest existing lemma before patching.
Several recent slowdowns came from forgetting helpers that were already present
or nearly present, such as:

- `FExprResultAtLvar_fv`
- `FExprResultOn_lvars_fv`
- `lvars_fv_difference_subset`
- `lty_env_open_one_dom`
- `logic_var_shift_inj`
- `lookup_kmap`, `lookup_kmap_Some`, `lookup_insert_is_Some'`
- `formula_fv_FStoreResourceAtom_lvars`
- `formula_fv_FTypeQualifier`

If the closest lemma is too specialized, generalize it cleanly rather than
building another one-off theorem for the current proof state.

## Diagnose the layer before proving

For each stuck goal, classify it before trying tactics:

- Pure syntax: variables, lvar sets, term/type/qualifier open/shift/fv/lc.
- Environment map-fold: `lty_env_open_one`, `lty_env_open_lvars`,
  `open_cty_env`, domain and lookup facts.
- Formula syntax: `formula_open`, `formula_fv`, wrappers such as
  `FForallTypedBind` and `FExprContIn`.
- Formula semantics: `res_models_with_store`, fibers, over/under, resource
  splitting, store restriction.
- Denotation recursion: gas-indexed induction and typed binder cases.

Do not solve a lower-layer problem by unfolding a higher-layer denotation.
For example, if `formula_open_denot_ty_lvar_gas` is blocked by
`open_cty_env_open_cty`, prove or redesign the `open_cty_env`/qualifier helper
first; do not expand the whole denotation body and patch around it locally.

## Check notation expansion deliberately

Many failures came from overloaded notation not unfolding to the shape expected
by a rewrite lemma:

- `↑[k] Σ` is `shift_at k Σ`, which for `lty_env` is `lty_env_shift_from k`.
- `lty_env_shift` is the older all-bound-variable shift using
  `logic_var_shift`.  It agrees with `↑[0]` only at depth 0, but it is not the
  same name.
- `{k ~> x} Σ` is `lty_env_open_one k x Σ`, while `{k ~> x} τ` is
  `cty_open k x τ`.
- `dom (<[...]> ...)` and lookup goals may hide gmap annotations that prevent
  rewrite from matching.

When a rewrite unexpectedly fails, do a small local check instead of guessing:

```coq
cbn [shift_at shift_lty_env_inst lty_env_shift_from] in *.
change (...) with (...) in *.
Check lookup_kmap.
Check dom_kmap_L.
```

Use `rocq repl` briefly if necessary, but close it.  Do not leave many REPL or
compile processes open.

## Prefer pointwise map proofs when rewrite fights annotations

For `gmap` domain/lookup goals, rewriting with `dom_kmap_L`,
`dom_insert_L`, or `lookup_insert_ne` can fail because the goal contains
overloaded notation or type annotations.  In that case switch to pointwise
proofs instead of spending many attempts on the same rewrite.

Robust patterns:

```coq
apply set_eq. intros x.
rewrite !lvars_fv_elem.
split; intros Hx.
```

For domain membership:

```coq
apply elem_of_dom in Hx as [T Hlookup].
apply elem_of_dom. exists T.
```

For shifted maps:

```coq
apply lookup_kmap_Some in Hlookup as [v [Hv Hlookup]];
  [| prove_injective ].
```

For inserted maps when only existence matters:

```coq
apply elem_of_dom in Hx as Hsome.
rewrite lookup_insert_is_Some' in Hsome.
```

Do not keep repeated local `change` hacks in a large proof.  If the same
normalization is needed twice, extract a named lemma such as
`typed_lty_env_bind_lvars_fv_dom`.

## Watch constructor and binder names

Do not rely on Rocq-generated names after `destruct τ`; recent failures came
from assuming the qualifier was named `t`.

Prefer explicit destruct patterns:

```coq
destruct τ as [b φ|b φ|τ1 τ2|τ1 τ2|τ1 τ2|τx τ|τx τ].
```

For induction over gas plus arbitrary environments, avoid reusing names already
bound by the theorem statement:

```coq
revert Σ τ e.
induction gas as [|gas IH]; intros Σ τ e.
```

## Keep recursive denotation proofs stronger than the public wrapper

When proving facts about `denot_ty_on`, first prove the lvar/gas version if
the recursive cases introduce `typed_lty_env_bind` or shifted types.

Good shape:

```coq
Lemma denot_ty_lvar_gas_fv_subset gas Σ τ e :
  formula_fv (denot_ty_lvar_gas gas Σ τ e) ⊆
    lvars_fv (dom Σ) ∪ fv_cty τ.
```

Then specialize to atom environments:

```coq
unfold denot_ty_on, denot_ty_lvar.
rewrite atom_env_to_lty_env_dom, lvars_fv_of_atoms.
```

Do not try to prove the atom-env wrapper directly if arrow/wand recursive
calls use lvar environments.

## Normalize shift/fv before set solving

In arrow/wand cases, recursive calls often mention `↑[0] τx` and
`typed_lty_env_bind Σ T`.  Before `set_solver`, rewrite the normal forms:

```coq
rewrite typed_lty_env_bind_lvars_fv_dom in *.
change (↑[0] τx) with (cty_shift 0 τx) in *.
rewrite cty_shift_fv in *.
```

If the rewrite is useful in more than one proof, promote it to a helper and
avoid repeating the `change`.

## Qualifier and formula equality level

When a qualifier or formula atom proof reaches a function or `Prop` field,
pause and choose the right equality:

- Pure variable-set claims should remain ordinary equality/subset lemmas.
- Predicate-field claims may use `functional_extensionality` and
  `propositional_extensionality`.
- If Leibniz equality becomes noisy, use `qual_equiv`, `formula_store_equiv`,
  or another setoid relation with `Proper` instances.

Do not keep unfolding `qual_open_atom`, `FTypeQualifier`, `FStoreResourceAtom`,
or fiber semantics inside a denotation theorem.  Extract wrapper-level
normalization and transport lemmas.

## Avoid over-specific helper statements

If a helper statement mentions a particular tlet-arrow target, a particular
proof-state variable, or has a long unrelated precondition list, stop and
generalize.

Prefer helpers classified by syntax:

- `forall` normalization
- `impl` / `wand` congruence
- atom wrapper open/fv law
- typed-forall open/fv law
- continuation open/fv law
- environment bind/shift/open commute

Then compose these in the high-level proof.

## Session discipline

Compile bottom-up after each helper group:

```sh
make ChoiceType/theories/TypeDenotation/Env.vo
make ChoiceType/theories/TypeDenotation/Lemmas.vo
make ChoiceType/theories/TypeDenotation/Denotation.vo
```

Scan remaining review points explicitly:

```sh
rg -n "Admitted\.|\\badmit\\b|Axiom" ChoiceType/theories/TypeDenotation -S
```

Send `ntfy` low-priority checkpoints after completing a helper group and
high-priority notifications when blocked, pausing, or waiting for user
guidance.
