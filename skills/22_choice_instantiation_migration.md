# ChoiceType Instantiation Migration

This migration brings part of the UnderType/HATs refinement-type and context
locally-nameless infrastructure into the current ChoiceType split.

## Files

- `ChoiceType/theories/QualifierProps.v`
  - proof-oriented qualifier lemmas moved out of `Qualifier.v`.
- `ChoiceType/theories/LocallyNamelessProps.v`
  - structural substitution facts for `choice_ty`.
- `ChoiceType/theories/InstantiationProps.v`
  - multi-substitution instances reusing `CoreLang.InstantiationProps`;
  - atom-open multi-substitution classes and instances for ChoiceType syntax.

## Important Design Boundaries

### Shallow Qualifiers

`type_qualifier` is shallowly embedded as a Rocq proposition.  It currently has
atom-open and value-substitution operations, but no close operation.  Do not
migrate close/open-close lemmas from UnderType for qualifiers unless the
qualifier representation changes or a real close operation becomes part of the
design.

Some equality lemmas over qualifiers may need functional extensionality because
the proposition field is a Rocq function.

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

For now, contexts are intentionally kept out of the substitution and
multi-substitution typeclass hierarchy.  Do not define/register `SubstV ctx`,
`SubstM ctx`, `MsubstFresh ctx`, or `FvOfSubst ctx` unless `ctx_fv` is changed
or a different free-variable notion excluding binders is introduced.

## Multi-Substitution Instances

Registered safely:

- `MsubstFresh type_qualifier`
- `MsubstFresh choice_ty`
- `MsubstFv type_qualifier`
- `MsubstFv choice_ty`
- `SubstOpenAtom type_qualifier`
- `SubstOpenAtom choice_ty`
- `MsubstOpenAtom type_qualifier`
- `MsubstOpenAtom choice_ty`
- `MsubstOpenVarAtom type_qualifier`
- `MsubstOpenVarAtom choice_ty`

Not registered:

- Any context substitution/multi-substitution instances.
- `MsubstIntroAtom` instances.  The class is present as the intended boundary,
  but the useful env-extension statement needs substitution-commutation facts
  for shallow qualifiers.  Add those deliberately when a proof needs them.
