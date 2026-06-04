# Denotation Extensional Equality And Setoid Normalization

This note records the current proof-engineering policy for the LN
TypeDenote route.  It should be read before proving or refactoring
`Denotation/theories/*`, tlet denotation helpers, or formula normalization
lemmas that mention qualifiers, logic atoms, fibers, forall, or expression
result atoms.

## Prefer the right equality level

Do not force Leibniz equality through semantic function fields when a cleaner
extensional equality or setoid relation is the real invariant.

Acceptable tools:

- `functional_extensionality` for function fields.
- `propositional_extensionality` for `Prop`-valued predicates.
- Setoid relations such as `qual_equiv`, `lqual_equiv`,
  formula-store equivalence, extension-function equivalence, or other
  extensional equivalences when Leibniz equality makes normalization brittle.
- `Equivalence` and `Proper` instances so future proofs can use
  `setoid_rewrite` instead of unfolding predicates by hand.

Use Leibniz equality for pure syntax, finite sets, maps, and wrappers whose
fields are definitionally stable.  Use extensional equality when a definition
contains a Rocq-level predicate, continuation, extension function, or shallow
atom interpretation.

## Qualifiers

`type_qualifier` contains both an lvar set and a semantic predicate.  For
lemmas about `qual_vars`, `qual_dom`, `qual_bvars`, and LN open/shift of the
variable set, prove ordinary syntax lemmas.

For lemmas that compare the predicate field after opening, shifting, swapping,
or restricting stores, prefer one of these shapes:

```coq
q1 ≡q q2
```

or, if actual Leibniz equality is convenient and extensional axioms solve the
predicate field cleanly, prove equality using `functional_extensionality` and
`propositional_extensionality`.

Do not write large one-off proofs that repeatedly unfold `qual_open_atom`,
`store_restrict`, and `map_restrict` inside TypeDenote theorems.  Extract
the qualifier normalization as a named lemma first.

## Formula and atom wrappers

For formula wrappers around shallow atoms, keep two APIs when useful:

- A syntactic/open law for `formula_open`, `formula_fv`, and lvar domains.
- A semantic transport law at the `res_models_with_store` level.

The with-store level is often the right one because `FFibVars` interprets its
body under an explicit projection store.  Avoid proving only a plain
`res_models` transport if the wrapper can occur under fibers.

Useful relation shape:

```coq
formula_store_equiv φ ψ :=
  forall ρ m,
    res_models_with_store ρ m φ <->
    res_models_with_store ρ m ψ.
```

Add congruence lemmas for connectives and wrappers (`FAnd`, `FImpl`, `FWand`,
`FOver`, `FUnder`, `FFibVars`, `FForall`, `expr_result_formula`,
`expr_basic_typing_formula`, `basic_world_formula`) instead of unfolding the
whole formula in every proof.

## Formula atoms and denotation guards

Do not repeatedly unfold the shallow atom encodings from
`ContextBasicDenotation` in main proofs.  The current denotation no longer has
typed-forall or denotation-obligation syntax sugar; use the component formulas
directly and hide repetitive opening/fv facts behind named lemmas.

Preferred API shape:

- Projection lemmas:

```coq
res_models m (basic_world_formula Σ) -> ...
```

- Intro/transport lemmas:

```coq
res_models m (expr_result_formula e x) ->
... ->
res_models m (expr_basic_typing_formula Σ e U)
```

- Syntax/fv/open normalization lemmas:

```coq
formula_open k x (expr_result_formula e z) = ...
formula_fv (ty_denote_gas gas Σ τ e) ⊆ ...
```

When a forall introduces a bound value, the guard is an ordinary implication
inside `FForall`.  Main denotation proofs should call helper lemmas for the
guard and use forall transport lemmas, not reconstruct the guard by unfolding
the whole recursive denotation.

## Bottom-up proof order

For tlet and TypeDenote proofs, prove from the smallest reusable layer
upward:

1. Pure LN syntax: open/shift/fv/lc for variables, terms, qualifiers, choice
   types, lvar sets, and lty environments.
2. Map-fold normalization: `open_env`, `open_lvars`, environment shift/open
   commutation, and domain/fv lemmas.
3. Atom wrapper normalization: formula open/fv and same-store transport.
4. BasicDenotation atom APIs: result, total, basic typing, and basic world.
5. Gas-indexed denotation lemmas, such as fv subset, open normalization, and
   environment agreement.
6. Main semantic proofs such as cont and tlet.

If a high-level proof gets stuck behind a raw unfolding, stop and extract the
missing helper at the lower layer.  Temporary admits are acceptable only as
named review points with a precise statement.

## LN proof discipline

For standard LN facts, continue proving downward instead of asking for
permission each time.  Examples include:

- `open_lc` / `open_rec_lc`
- open/open composition
- open/shift commutation
- `fv` preservation or subset under open/shift
- map-fold versions of the same facts for environments

Use the standard pattern:

- prove syntax facts over variables/sets first;
- lift to terms/types/qualifiers by induction;
- lift to environments with lookup/domain or fold lemmas;
- only then use them in denotation formulas.

When typeclass notation such as `↑[k]` or `{k ~> x}` blocks rewriting, do not
leave repeated `change`s in large proofs.  Either make a small normalization
tactic or prove a named pointwise/domain lemma.  For `gmap` goals, pointwise
proofs via `elem_of_dom`, `lookup_kmap`, and `lookup_insert_is_Some'` are often
more robust than rewriting through overloaded notation.

## Avoid repeating old-route mistakes

The current route is independent of the legacy denotation proofs.  It is fine
to read legacy files for proof ideas, but do not depend on old-route bridge
lemmas unless the user explicitly asks for a bridge.

Before proving a high-level helper, check whether it is actually a generic
syntax/semantic normalization fact.  Avoid overly specific helpers such as a
lemma specialized to one tlet-arrow formula shape when a generic
`forall`/`impl`/`atom`/`typed-forall` lemma would compose cleanly.

If a candidate lemma has many unrelated preconditions or mentions a very
specific proof state, it is probably the wrong abstraction.  Refactor it into
smaller commute, penetration, projection, or transport lemmas.

## Notifications while working

During long proof sessions, send a low-priority `ntfy` checkpoint after each
completed checklist item and a high-priority notification when blocked,
pausing, or waiting for user guidance.  Do not silently skip notifications
because a shell helper is missing; use direct `ntfy pub -p low|high zhe-codex
...`.
