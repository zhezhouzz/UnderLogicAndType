# Typing Naming Refactor

Typing proofs tend to accumulate repeated freshness, erased-context domain, and
open/substitution side conditions.  Before proving through them by hand, look
for a reusable naming invariant.

Useful patterns from this refactor:

- Package fresh representatives as a record, e.g. `tlet_fresh_name`, instead of
  repeatedly destructing `fresh_for_not_in`.  Keep projection lemmas for common
  side conditions such as `x ∉ X`, `x ∉ fv_tm e`, and `x ∉ fv_cty τ`.
- Normalize erased context binders through helpers:
  `erase_ctx_under_comma_bind_dom_nf` and
  `erase_ctx_under_comma_bind_env_fresh`.
- Use `erase_ctx_under_dom_basic` whenever a proof manually unfolds
  `erase_ctx_under` and rewrites `basic_ctx_erase_dom`.
- Use `denot_ctx_in_env_world_covers_erased` and
  `denot_ctx_in_env_store_restrict_env_delete_empty` instead of rebuilding the
  same formula-scoping/world-domain/store-restrict argument.
- For body opening after recording an evaluated result, use
  `msubst_open_body_result` and the two directional step bridges:
  `steps_msubst_open_body_result` and `steps_open_body_to_msubst_result`.

Be careful with direction:

- If the goal has
  `subst_map (<[x := vx]> (store_restrict σ X)) (e ^^ x) →* ...`, use
  `steps_open_body_to_msubst_result`.
- If the goal has
  `open_tm 0 vx (subst_map (store_restrict σ X) e) →* ...`, use
  `steps_msubst_open_body_result`.

Avoid broad `eauto` on these bridges when the context contains both
`closed_env` and `stale vx = ∅`; it may try to solve the value-closed premise
with the environment-closed hypothesis.  Prefer explicit bullets for the six
side conditions.
