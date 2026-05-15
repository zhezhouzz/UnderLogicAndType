# Operational Reduction Helper Lemmas

When proving reductions for CoreLang derived forms, first look for the
high-level lemmas in `CoreLang/theories/OperationalProps.v` before expanding
`Steps_step` by hand.

Useful helpers:

- `steps_R` turns a one-step reduction into a multi-step reduction.
- `steps_trans` composes multi-step reductions.
- `reduction_lete_intro` proves a let reduction from:
  - `body_tm e2`
  - `e1 →* tret vx`
  - `open_tm 0 vx e2 →* tret v`
- `reduction_lete_msubst_intro` is the same pattern after a CoreLang
  multi-substitution has already been pushed over the whole let:
  - `body_tm (msubst σ e2)`
  - `msubst σ e1 →* tret vx`
  - `open_tm 0 vx (msubst σ e2) →* tret v`
- `reduction_match_true_intro` and `reduction_match_false_intro` prove
  boolean-match reductions from the chosen branch reduction.
- `reduction_beta_intro` and `reduction_fix_intro` do the same for function
  application.
- `reduction_prim_intro` proves a primitive redex result directly from
  `prim_step op c c'`.
- `reduction_prim_const` is the inversion direction: every result of
  `tprim op (vconst c)` comes from some `prim_step op c c'`.
- `reduction_prim_fvar_msubst_const` packages the common semantic case where a
  substituted argument variable is known to be a constant:

  ```coq
  closed_env σ ->
  σ !! x = Some (vconst c) ->
  m{σ} (tprim op (vfvar x)) ->* tret v ->
  exists c', prim_step op c c' /\ v = vconst c'.
  ```

  Use this in primitive-operation soundness instead of unfolding both
  multi-substitution and `steps_inv` in the same proof.

Pattern for derived choice forms:

1. Prove the let body is a `body_tm` once, instead of proving specialized
   `lc_tm (tlete (tret ...) ...)` facts.
2. For final-result lemmas, state the goal as `derived →* tret v`; this fits
   `reduction_lete_intro` directly.
3. After opening the let body, use `open_rec_lc_tm` to erase openings through
   already-closed branches.
4. Use the appropriate match intro lemma for the chosen boolean branch.

Primitive-operation proof pattern:

1. Use a basic-world/store typing lemma to show the argument coordinate maps
   to a closed constant of the primitive's argument base type.
2. Rewrite the substituted primitive with
   `msubst_prim_fvar_lookup_closed`, or use
   `reduction_prim_fvar_msubst_const` directly if the goal is a result
   inversion.
3. Use `prim_step_result_has_type` when the proof needs the result constant's
   erased/basic type.

Example shape:

```coq
Lemma derived_left_result et ef v :
  lc_tm et ->
  lc_tm ef ->
  et ->* tret v ->
  derived_choice et ef ->* tret v.
Proof.
  intros Het Hef Hsteps.
  unfold derived_choice.
  eapply reduction_lete_intro.
  - apply body_of_choice_body; eauto.
  - apply generator_reaches_left.
  - change (tmatch vtrue (open_tm 0 vtrue et) (open_tm 0 vtrue ef) ->* tret v).
    rewrite (open_rec_lc_tm et Het 0 vtrue).
    rewrite (open_rec_lc_tm ef Hef 0 vtrue).
    eapply reduction_match_true_intro; eauto.
Qed.
```

For structural lemmas whose conclusion is `derived →* branch_term` rather
than `derived →* tret v`, the result-focused `reduction_lete_intro` is not
directly applicable.  Either prove a result version for downstream use, or use
`steps_R` plus a small amount of manual stepping.
