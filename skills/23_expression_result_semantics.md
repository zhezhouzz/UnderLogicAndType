# Expression Result Semantics

When proving soundness cases that mention Core evaluation, avoid making the
Choice Logic formula layer carry all operational structure.

## Current pattern

Keep the direct expression-result relation as a Rocq-level predicate:

```coq
expr_result_in_world ρ e ν w
```

Then let the logic atom wrapper be only a shallow embedding:

```coq
expr_logic_qual e ν := lqual (stale e ∪ {[ν]}) ...
FExprResult e ν := FAtom (expr_logic_qual e ν)
```

This makes operational lemmas usable before entering formula proof plumbing.
For `tlete`, use:

- `expr_result_in_world_let_elim`
- `expr_result_in_world_let_intro`

These lemmas call the CoreLang reduction helpers (`reduction_lete`,
`reduction_lete_intro`) after pushing `msubst` through `tlete`.

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

## Design lesson

Do not introduce formula-level bridges such as
`FLetResult -> FExprResult (tlete ...)` unless the statement has been checked
against `FAtom`'s upward-closed semantics.  For let, the operational link
between the intermediate result and the body is store-dependent, so it is safer
to prove the operational relation at the Rocq predicate level first.
