# Skill: Strict Positivity in Inductive Types

## Current status

The old branch-list `tmatch` design was removed.  CoreLang now has a fixed
boolean match:

```coq
tmatch v etrue efalse
```

So `lc_tm` and typing no longer need `branch_lc`, `constructor_tys`, `Forall`,
or indexed branch tables.

## General rule

Rocq requires inductive definitions to be strictly positive: the inductive
being defined must not occur to the left of an arrow inside a parameter to
another inductive predicate.

If a future definition needs subderivations for elements of a list, prefer a
direct premise such as:

```coq
forall x, x ∈ xs -> P x
```

rather than putting the recursive judgment inside a `Forall` lambda in an
inductive constructor.
