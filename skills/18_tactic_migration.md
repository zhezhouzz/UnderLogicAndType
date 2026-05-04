# Tactic Migration And Use Patterns

This repo uses a deliberately small tactic layer adapted from HATs and
UnderType. Do not copy whole tactic files unless a concrete proof forces it.
Prefer focused, observable tactics that help with locally-nameless proofs,
finite-set side conditions, and repeated induction hypotheses.

## Quick Selection Guide

Use `my_set_solver` when the goal is about `fv_*`, `stale`, `dom`, freshness, or
`lookup = None`, especially if the goal contains:

- `dom (<[_:=_]> _)`
- `_ !! _ = None`
- `∅ ∪ _` or `_ ∪ ∅`
- `stale _ = ∅`
- repeated unions around a fresh atom

Use plain `set_solver` for tiny pure set goals. Use `set_solver!!` only for pure
side conditions when `set_solver` is slow; it prunes hypotheses aggressively.

Use `auto_exists_L` when proving a cofinite/body-style goal such as:

```coq
exists L, forall x, x ∉ L -> ...
```

The usual continuation is:

```coq
auto_exists_L; intros x Hx; repeat specialize_with x.
```

Use `auto_pose_fv x; repeat specialize_with x` when the proof already has
cofinite hypotheses and you need one fresh atom to feed all of them.

Use `var_dec_solver` inside structural inductions over syntax after simplifying
open/close/substitution. It handles many branches of `decide (x = y)` and
`decide (i < j)`. If the branch has exactly one visible `decide`, an explicit
`destruct (decide ...); my_set_solver` can be clearer and more robust.

Use `var_dec_simpl` or `var_dec_set_solver` when a script should tolerate the
case where no decidable branch remains. These are better prefixes than a direct
`var_dec_solver` call:

```coq
var_dec_set_solver.
```

Use `auto_apply` or `auto_eapply` when a mutual induction hypothesis has the
same conclusion head as the goal. If several IHs have similar conclusions, name
and apply the intended one explicitly.

Use `econstructor_L` when a constructor has an explicit `aset` avoidance
parameter. Use `econstructor_L_specialized` when the next subgoal should be a
fresh-variable premise:

```coq
econstructor_L_specialized; ln_simpl; my_set_solver.
```

## Useful Tactic Groups

Hypothesis traversal:

- `do_hyps tac`: run `tac H` on each hypothesis.
- `select! pat tac`: run `tac H` on hypotheses matching `pat`, and fail if none
  exist.
- `fold_hyps acc tac`: fold over hypotheses; mainly used by `collect_stales`.

Fresh/cofinite:

- `collect_stales tt`: collect the union of visible `stale` sets.
- `auto_exists_L`: instantiate a cofinite witness with collected stale sets.
- `auto_pose_fv x`: define `x := fresh_for collected_stales`.
- `specialize_with x`: specialize `forall y, y ∉ L -> ...` using `x`.

Set/map normalizers:

- `my_set_simpl`: normalize `∅ ∪ _`, `_ ∪ ∅`, `stale _ = ∅`, and
  `lookup = None`.
- `my_map_simpl`: normalize map domains and empty map unions.
- `my_set_solver`: run the normalizers and then fall back to pruned set solving.
- `smart_ln_simpl`: run `simpl`, binder cleanup, and `my_set_solver` together.

Application helpers:

- `auto_apply`/`auto_eapply`: apply the first matching hypothesis.
- `apply_eq`/`eapply_eq`: apply a hypothesis while generating equality
  subgoals for dependent arguments.

## Failure Modes And Repairs

If `collect_stales` fails, the context probably has no useful `Stale` object.
Either introduce the syntax object first, or write the avoidance set manually:

```coq
exists (L ∪ fv_tm e ∪ {[x]}).
```

If `my_set_solver` is slow, try its pieces manually:

```coq
my_map_simpl; my_set_simpl.
```

Then inspect the remaining goal. Do not blindly replace every `set_solver` with
`my_set_solver`; use it where normalization helps.

If `set_solver!!` solved a side condition before but now fails, try
`set_solver!` or plain `set_solver`. The aggressive pruning can remove a
hypothesis that a rewritten goal later needs.

If `auto_apply` applies the wrong hypothesis, replace it with an explicit
`apply`/`eapply`. This is common in mutual inductions with both value and term
IHs in scope.

If `var_dec_solver` fails with "Failed to progress", it probably reached a goal
where no recognized `decide` or contradiction remains. Use an explicit
destruct for the relevant equality test, then finish with `my_set_solver`.

If `econstructor_L` leaves unexpected evars, the constructor probably has more
non-`Prop` arguments than just the avoidance set. Instantiate those arguments
manually and use `auto_specialization` only for the fresh-variable premise.

## Proof Script Patterns

Body preservation under substitution:

```coq
intros [L Hbody] Hlc.
exists (L ∪ {[x]}). intros y Hy.
rewrite <- subst_open_var_tm by my_set_solver.
apply subst_lc_tm; auto.
apply Hbody. my_set_solver.
```

Fresh variable for a cofinite IH:

```coq
auto_pose_fv x.
repeat specialize_with x.
```

Small LN induction branch:

```coq
smart_ln_simpl.
try solve [f_equal; eauto; my_set_solver].
try var_dec_set_solver.
```

Typing proof with inserted binder:

```coq
rewrite dom_insert in H.
my_set_solver.
```

Constructor with cofinite set:

```coq
econstructor_L; auto_specialization.
```

## Migration Boundaries

Do not migrate heavy saturation tactics (`dup_hyp!`, `block_hyp`, global
forward-reasoning loops) until a concrete proof needs them. They obscure proof
state and can diverge.

Do not copy list-context tactics such as `empty_eq_app_exfalso` blindly. This
repo's type contexts are tree-shaped, so those scripts are usually the wrong
abstraction even when the fresh-variable idea is useful.

Avoid broad global `Hint Extern` rules for these tactics. Prefer explicit local
invocation so proof search remains predictable.
