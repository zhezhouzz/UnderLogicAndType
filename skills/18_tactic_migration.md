# Tactic Migration Patterns

When migrating tactics from HATs or UnderType into this repo, prefer a small
stable kernel over copying whole tactic files.

## Useful first-wave tactics

- Hypothesis traversal: `revert_all`, `get_hyps`, `do_hyps`, `select!`,
  `fold_hyps`. These are mainly needed so fresh-variable tactics can scan the
  proof context.
- Set/map normalization: `set_solver!`, `set_solver!!`, `fast_set_solver!!`,
  `my_set_simpl`, `my_map_simpl`, `my_set_solver`. Use these when plain
  `set_solver` is slow or when goals contain `dom (<[_:=_]> _)`,
  `lookup = None`, `∅ ∪ _`, `_ ∪ ∅`, or `stale _ = ∅`.
- Cofinite/LN fresh helpers: `collect_stales`, `auto_exists_L`,
  `auto_pose_fv`, `specialize_with`. These match the common script shape:
  choose a fresh atom outside all visible stale/fv sets, specialize every
  cofinite hypothesis with it, then finish side conditions by `my_set_solver`.
- Binder/decidable cleanup: `var_dec_solver` is useful for open/close/subst
  proofs with many `decide (x = y)` or `decide (k < n)` branches.
- IH application: `auto_apply`/`auto_eapply` are helpful in mutual induction,
  but keep scripts readable and avoid using them when an explicit IH name is
  clearer.

## Patterns that worked

- Normalize before solving:

  ```coq
  my_map_simpl; my_set_simpl; try fast_set_solver!!; try set_solver.
  ```

- In cofinite proofs:

  ```coq
  auto_exists_L; intros x Hx; repeat specialize_with x.
  ```

- For stubborn set rewrites in hypotheses, prefer `setoid_rewrite` inside the
  normalizer instead of ad hoc `change` steps in individual examples.

## Patterns to avoid initially

- Do not migrate heavy saturation tactics (`dup_hyp!`, `block_hyp`, global
  forward-reasoning loops) until a concrete proof needs them. They obscure proof
  state and can diverge.
- Do not copy list-context tactics such as `empty_eq_app_exfalso` blindly. This
  repo's type contexts are tree-shaped, so those scripts are usually the wrong
  abstraction even when the fresh-variable idea is useful.
- Avoid broad global `Hint Extern` rules for these tactics. Prefer explicit
  local invocation so proof search remains predictable.
