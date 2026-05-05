# ChoiceType Instantiation Migration

This migration brings part of the UnderType/HATs refinement-type and context
locally-nameless infrastructure into the current ChoiceType split.

## Files

- `ChoiceType/theories/QualifierProps.v`
  - proof-oriented qualifier lemmas moved out of `Qualifier.v`.
- `ChoiceType/theories/LocallyNamelessProps.v`
  - structural substitution facts for `choice_ty`;
  - context substitution and close operations;
  - context domain/fv lemmas.
- `ChoiceType/theories/InstantiationProps.v`
  - multi-substitution instances reusing `CoreLang.InstantiationProps`.

## Important Design Boundaries

### Shallow Qualifiers

`type_qualifier` is shallowly embedded as a Rocq proposition.  Its `close`
operation has a reasonable bridge definition:

```coq
qual_close_atom x k (qual B d p)
```

adds `k` to the bound-variable set, removes `x` from the atom domain, and feeds
the bound value back into the store when evaluating `p`.  Equality lemmas such
as open-close should be added carefully, likely as semantic/spec lemmas first,
because proposition functions may only be equal extensionally.

### Tree Contexts

Our `ctx_fv` includes binder atoms:

```coq
ctx_fv (CtxBind x τ) = {[x]} ∪ fv_cty τ
```

Therefore the standard UnderType/listctx lemma

```coq
fv ({x := v} Γ) ⊆ fv Γ ∖ {[x]} ∪ fv v
```

is false for `ctx`.  Substituting inside the type annotation does not remove
the binder atom `x` from `ctx_fv`.

Use these instead:

- `ctx_dom_subst_one`
- `ctx_dom_subst_map`
- `ctx_fv_subst_subset`
- `ctx_fv_subst_closed_subset`

Do not register `FvOfSubst ctx` unless `ctx_fv` is changed or a different
free-variable notion excluding binders is introduced.

## Multi-Substitution Instances

Registered safely:

- `MsubstFresh type_qualifier`
- `MsubstFresh choice_ty`
- `MsubstFresh ctx`
- `MsubstFv type_qualifier`
- `MsubstFv choice_ty`

Not registered:

- `MsubstFv ctx`, for the reason above.
- `MsubstOpen`/`MsubstIntro` for ChoiceType atom-open binders.  The generic
  CoreLang classes are value-open; ChoiceType should get separate atom-open
  classes if/when proofs need them.
