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

## Important FAtom detail

`FAtom` is upward closed and `logic_qualifier_denote` restricts both the
explicit store and the world to the qualifier domain.  Therefore, destructing

```coq
m ⊨ FExprResult e ν
```

does **not** produce `expr_result_in_world ∅ e ν m`.  It produces a witness
world `w` such that:

```coq
expr_result_in_world
  (store_restrict ∅ (stale e ∪ {[ν]}))
  e ν
  (res_restrict w (stale e ∪ {[ν]}))
∧ w ⊑ m
```

Use `FExprResult_models_elim` / `FExprResult_models_intro` instead of manually
unfolding this shape.

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
