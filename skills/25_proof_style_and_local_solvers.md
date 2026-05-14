# Proof Style And Local Solvers

This note records the preferred proof-script style for the current
formalization.  The goal is not to maximize automation blindly, but to make
proofs robust under harmless refactors such as hypothesis renaming, small
definition reshaping, or moving helper lemmas between files.

## Prefer bounded automation for trivial plumbing

Use `eauto 6` as the default small automation budget.

Good targets:

```coq
Proof. intros; eauto 6. Qed.
Proof. constructor; eauto 6. Qed.
Proof. split; eauto 6. Qed.
```

When a proof is just:

```coq
intros H1 H2. exact H1.
```

prefer:

```coq
intros; eauto 6.
```

This is more robust when hypothesis names change.  The same applies to many
`reflexivity`, `assumption`, and tiny constructor goals, unless a definitional
equality is the whole point of the lemma.

If a local hint database exists, use the bounded form:

```coq
eauto 6 with basic_typing.
eauto 6 with store.
eauto 6 with resource.
```

Avoid unbounded `eauto` in large semantic goals.  If a previous proof was slow
because automation searched through denotation/resource definitions, keep the
explicit proof and add a warning comment:

```coq
(* Keep this explicit: broad eauto here used to search through denotation
   atoms and made TLetReduction.v recompile slowly. *)
```

## Split automation by layer

Do not build one global tactic that unfolds the whole development.  Each layer
should have its own solver and hint database.

Recommended layers:

- `my_set_solver`: finite-set, freshness, `dom`, and `lookup = None` side
  conditions.
- `store_solver`: store restriction, store swap/rename, store domain, store
  compatibility.
- `resource_solver`: resource restriction, world domain, fibers, swaps,
  resource order, product/sum witnesses.
- `logic_solver`: formula intro/elim, atom sugar, connective equivalence,
  monotonicity/transport lemmas.
- `ln_solver`: locally-nameless `open`, `fv`, `lc`, stale sets, cofinite
  witnesses, measure preservation.
- `basic_solver`: basic typing, erasure contexts, regularity lemmas, primitive
  typing facts, context-domain bookkeeping.

A good solver shape is:

```coq
Ltac basic_solver :=
  repeat basic_regular;
  repeat basic_norm;
  eauto 6 with basic_typing;
  try my_set_solver.
```

The important part is that each tactic normalizes only its own layer, then
finishes with bounded `eauto 6`.  Do not add `Hint Unfold denot_ty_fuel` or
other large definitions to a global hint database.

## Normalize instead of writing repeated `change`

Repeated `change (...) with (...)` is a smell.  It is fine while debugging, but
if the same conversion appears more than once, abstract it.

Prefer small normalizers:

```coq
Ltac store_norm :=
  cbn [store_restrict map_restrict store_swap store_rename_atom] in *;
  rewrite ?store_restrict_restrict in *.

Ltac resource_norm :=
  cbn [world_dom res_restrict] in *;
  rewrite ?res_restrict_idemp in * by eauto 6.
```

Keep normalizers narrow.  A tactic that unfolds every formula and every
resource definition will be unpredictable and can slow the build.  It is better
to have several small tactics than one large one.

For overloaded wrapper classes, prefer a tiny local normalizer instead of
scattered `change`s.  For example, the denotation layer uses `IntoLVars` for
atom sets, logic-variable sets, atom typing environments, and logic-variable
typing environments.  A local tactic can normalize only those wrappers:

```coq
Ltac denot_lvars_norm :=
  repeat match goal with
  | |- context[into_lvars ?X] =>
      let T := type of X in
      lazymatch T with
      | lvset => change (into_lvars X) with X
      | aset => change (into_lvars X) with (lvars_of_atoms X)
      end
  end.
```

Use this style only for definitional wrapper cleanup.  Do not put semantic
rewrites or large unfolds into such a tactic.

If a normalization is semantic rather than definitional, make it a lemma first.
For example, prefer:

```coq
rewrite store_restrict_restrict.
```

over repeating:

```coq
change (store_restrict (store_restrict σ X) Y) with ...
```

## Avoid one-use `assert`

Use `assert` when the intermediate fact is named, reused, or clarifies a proof
boundary.  Do not use it only to immediately feed another hypothesis.

Prefer direct specialization:

```coq
specialize (H x Hx).
eapply lemma in H; eauto 6.
```

or direct application:

```coq
eapply lemma; eauto 6.
```

over:

```coq
assert (Hx' : P x).
{ ... }
pose proof (lemma _ Hx') as Hlem.
```

When a proof really needs a shared intermediate state, keep the `assert`, but
name it by the semantic fact it represents rather than by a local proof step.

## Use set solving as the final step

`set_solver` is excellent, but large denotation goals often contain opaque
shallow-embedded predicates.  First expose only the set-shaped facts, then call
the solver.

Typical order:

```coq
cbn [formula_fv stale stale_logic_qualifier lqual_dom] in *.
rewrite ?lvars_fv_union, ?lvars_fv_of_atoms in *.
eauto 6; try set_solver.
```

If `set_solver` is mixed with automation, let the non-set automation clear the
simple proof obligations first:

```coq
eauto 6; try set_solver.
```

When `set_solver` is slow, extract the recurring side condition into a lemma and
add it to the appropriate solver.  This is especially useful for:

- `dom (<[x := T]> Γ)`
- `fv_* ({0 ~> x} t)`
- `lvars_fv (D ∪ E)`
- `world_dom (res_restrict m X)`

Also reduce the proof context before calling automation.  Many slow proof
commands are not slow because the target set fact is hard, but because the
context contains large semantic hypotheses such as full denotations, typing
derivations, and world predicates.  If a side condition needs only a few fv/dom
facts, specialize or pose those small facts first, then clear the bulky ones:

```coq
pose proof (basic_typing_contains_fv_tm _ _ _ Hty) as Hfv.
clear Hty Hmodel Hdenot Hworld.
set_solver.
```

For one-off freshness arguments, prefer destructing `not_elem_of_union` over
sending a huge union goal to `set_solver`:

```coq
rewrite !not_elem_of_union in Hfresh.
destruct Hfresh as [[[Hfresh_L Hfresh_dom] Hfresh_x] Hfresh_e].
```

This is especially helpful when the freshness proof is passed as an argument to
a large lemma or a `rewrite`:

```coq
(* Avoid: this runs set_solver in the full semantic context. *)
rewrite (big_lemma ... ltac:(set_solver)).

(* Prefer: isolate the small fact first. *)
assert (Hν : ν ∉ D ∪ {[x]} ∪ fv_tm e) by set_solver.
rewrite (big_lemma ... Hν).
```

## Basic typing solver pattern

Basic typing side conditions should be solved by regularity plus bounded
automation, not by manually destructing every typing derivation in every proof.

The intended pattern:

1. Use regularity lemmas to pull out basic typing, well-formed context/type, and
   domain facts from richer typing hypotheses.
2. Normalize erased contexts and inserted binders.
3. Finish with `eauto 6 with basic_typing` and `my_set_solver`.

Example skeleton:

```coq
Ltac basic_regular :=
  repeat match goal with
  | H : choice_typing _ _ _ _ |- _ =>
      pose proof (choice_typing_regular _ _ _ _ H); clear H
  | H : _ ⊢ₑ _ ⋮ _ |- _ =>
      pose proof (basic_typing_regular _ _ _ H)
  end.

Ltac basic_solver :=
  basic_regular;
  cbn [erase_ctx erase_ty ctx_dom] in *;
  eauto 6 with basic_typing;
  try my_set_solver.
```

Keep this tactic local to the typing layer unless it becomes stable enough to
export.

When a proof file has a recurring but very local family of regularity facts,
start with a file-local tactic rather than exporting a global solver.  For
example, a tlet proof can use:

```coq
Local Ltac tlet_regular :=
  eauto 6 using basic_typing_contains_fv_tm, typing_tm_lc,
    world_store_closed_on_world_closed_on.
```

This documents the proof pattern without adding broad global hints.  Promote it
to a shared solver only after multiple files use the same shape.

## CoqHammer usage

`hauto` is useful for small first-order proof plumbing:

```coq
Proof. unfold formula_equiv, entails. hauto. Qed.
Proof. unfold sub_type. hauto. Qed.
```

Use it after the important semantic rewrite or local unfold has already exposed
the simple shape.  Do not put `hauto` inside broad solvers such as
`my_set_solver`, `store_solver`, or `resource_solver`; those tactics run in many
places and Hammer can quietly increase compile time.

If `hauto` fails, do not keep increasing search blindly.  First unfold the
intended wrapper or apply the intended lemma explicitly.

## Watch import and loading cost

Rocq compile time is not only proof checking.  `Require Import/Export` loads
compiled `.vo` objects into the current environment: constants, proof terms,
universe constraints, notations, hints, typeclass instances, and exported
dependencies.  A tiny wrapper file can still be slow if it exports a large
prelude.

Use these rules when optimizing build time:

- Prefer `Require Import` for ordinary proof-support files.  Reserve
  `Require Export` for intentional API/prelude boundaries.
- Register typeclass instances in the file that proves the underlying theorem
  whenever possible.  A tiny `*Instances.v` wrapper often reloads a large proof
  layer just to run a few `Instance` commands; move those instances next to the
  lemmas unless doing so creates a real dependency cycle.
- Avoid very small wrapper files unless they control a useful public import
  surface.  Splitting a huge file helps proof checking, but too many small files
  can make loading dominate.
- File-size guidance is pragmatic: keep ordinary files around 1000 lines, but
  allow up to about 1500 lines when merging wrappers/instances materially
  reduces loading cost.  Do not preserve a tiny file solely to satisfy the line
  limit if it makes every downstream compile pay another import.
- Keep heavyweight hints out of `core`; put them in named hint databases and
  call them explicitly with `eauto 6 with ...`.
- When a short file has high seconds-per-kloc, first check whether the cost is
  mostly its imports.  If `coqc -time` reports only the initial `From ...`
  command as hot, proof-script edits inside the file will not help much.
- Be careful with `Require Export` chains in `SoundnessHelpers`-style wrapper
  files.  They can make every downstream file pay for dependencies it never
  uses directly.

Useful measurement pattern:

```sh
coqc -time path/to/File.v > /tmp/file_time.log
perl -ne 'if (/\] ([0-9.]+) secs/) { print "$1 $_" if $1 > 0.12 }' \
  /tmp/file_time.log | sort -nr | head
```

If the hot command is a `set_solver`, `hauto`, or broad `eauto`, reduce the
context or extract the recurring set/resource fact.  If the hot command is an
import, inspect the dependency surface instead of micro-optimizing local
proofs.

## Preserve explicit scripts at known hot spots

Some proof locations should remain explicit.  A real example is the over/under
case in `TLetReduction.v`: a broad

```coq
eapply FExprCont_tlet_reduction; eauto; try set_solver.
```

made the file compile very slowly.  The fix was to pass the key arguments and
hypotheses explicitly.  In these cases, keep the explicit script and leave a
comment explaining why bounded automation is intentionally avoided.

The rule is:

- use `eauto 6` for robust small proof plumbing;
- use layer solvers for normalized side conditions;
- keep explicit scripts where semantic search space is large or previously
  caused a compile-time regression.
