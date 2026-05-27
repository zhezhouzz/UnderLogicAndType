# ContextType Instantiation Migration

This is a historical migration note from the older monolithic ContextType era.
The current code is split across `ContextTypeLanguage`, `ContextBasicDenotation`,
`Denotation`, and `ContextTyping`; use this file only for substitution/LN
background, not as the current module map.

## Files

- `ContextTypeLanguage/theories/*`
  - current syntax, qualifier, environment, and LN/open/fv lemmas.
- `ContextBasicDenotation/theories/*`
  - current shallow logic atoms for totality, result, basic typing, and worlds.
- `Denotation/theories/*`
  - current recursive context-type denotation and direct TLet proof route.

## Important Design Boundaries

### Shallow Qualifiers

`type_qualifier` is now a dependent-domain qualifier over lstores.  It has LN
open/shift support, but no value-substitution operation.  Do not migrate
old open/substitution lemmas from UnderType unless a proof explicitly needs a
new operation in the current representation.

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
- `MsubstFresh context_ty`
- `MsubstFv type_qualifier`
- `MsubstFv context_ty`
- `SubstOpenAtom type_qualifier`
- `SubstOpenAtom context_ty`
- `MsubstOpenAtom type_qualifier`
- `MsubstOpenAtom context_ty`
- `MsubstOpenVarAtom type_qualifier`
- `MsubstOpenVarAtom context_ty`

Not registered:

- Any context substitution/multi-substitution instances.
- `MsubstIntroAtom` instances.  The class is present as the intended boundary,
  but the useful env-extension statement needs substitution-commutation facts
  for shallow qualifiers.  Add those deliberately when a proof needs them.
