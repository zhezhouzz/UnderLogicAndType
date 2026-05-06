# Partial Choice Algebra Remaining Work

This note records the unfinished proof work left on
`codex/partial-choice-algebra` before switching to the instantiation migration.

## Completed on the Branch

- `ChoiceAlgebra` operations now expose partial definedness:
  - `ca_times_def` is `world_compat`.
  - `ca_plus_def` is `raw_sum_defined`.
  - `ca_times` / `ca_plus` take explicit definedness proofs.
- `res_product_total` and `res_sum_total` were removed.
- The following algebra/resource facts are proved:
  - unit laws for product on the right,
  - commutativity of product and sum,
  - associativity of product and sum with explicit derived definedness witnesses,
  - sum monotonicity,
  - left projection order `w1 ⊑ res_product w1 w2 Hc`,
  - atom rename well-formedness for resources.
- `aset_rename` was corrected to match `store_rename_atom`:
  - if `x ∈ X`, rename `x` to `y`;
  - if `x ∉ X`, delete `y`.

## Remaining Admits

- `ChoiceAlgebra/theories/Resource.v`
  - `res_product_le_mono`.
    This should use the target compatibility proof `Hc' : world_compat w1' w2'`.
    A raw product monotonicity lemma without such a compatibility assumption is
    misleading for the partial operation and was removed.

- `ChoiceLogic/theories/ChoiceLogicProps.v`
  - `forall_mono` and `exists_mono`.
    These appear to need a semantic rename/entailment lemma, because the
    cofinite semantics checks `formula_rename_atom x y p`.
  - `star_wand_adjunction`.
    Recheck the statement against the current semantics before proving; the
    exact adjunction may need a different implication shape.

- `ChoiceLogic/theories/ANF.v`
  - Collapse lemmas are intentionally isolated from the main proof path.  They
    can remain admitted while the core algebra and typing work proceeds.

## Proof Lessons

- Keep partial operations partial.  Do not repair missing definedness by adding
  fallback worlds.
- Prefer moving store/map facts into `ChoicePrelude/Store.v` instead of proving
  them inline in resource proofs.
- When stdpp union associativity is overloaded, an explicit term such as
  `assoc_L (∪) s1 s2 s3` is more stable than bare `rewrite assoc_L`.
- Choice Logic uses explicit atom binders with cofinite semantics, not locally
  nameless binders.  For alpha-renaming/equivariance lemmas, use a
  nominal-style `swap`/finite-permutation operation rather than the existing
  covering `rename`.  Covering rename (`x ↦ y`, deleting or overwriting the old
  `y`) is useful for opening into a fresh representative, but it is not a
  bijection on arbitrary worlds and therefore should not be used to prove
  global preservation of `⊑`, product, sum, or fiber.  Swap is involutive and
  preserves resource structure.
- When a Logic proof repeats a block about transporting a one-coordinate
  extension through `res_swap`, stop and promote it to `Resource.v`.  The
  useful shape is a pair of domain/restriction lemmas, one for the direct
  direction and one for the canceling direction, e.g.
  `res_swap_extension_dom[_cancel]` and
  `res_swap_restrict_extension[_cancel]`.  This keeps quantifier cases focused
  on the cofinite argument instead of on set arithmetic.
- For fibers, distinguish real semantic content from proof-argument noise.
  `res_fiber_from_projection` contains a projection proof parameter, so goals
  that differ only in that proof should use
  `res_fiber_from_projection_proof_irrel`.  If the same goal also contains
  convertible swapped singleton domains such as
  `aset_swap x y {[atom_swap x y z]}`, add a small transport lemma in
  `Resource.v` instead of leaving a local `wfworld_ext/world_ext` block in
  `Formula.v`.
- In Choice Logic monotonicity proofs, the common pattern
  “rename entailment at a fresh atom, then adjust fuel” should go through
  `entails_rename_atom_fresh_fuel`.  This avoids four near-identical
  `pose proof ...; assert Hp_exact ...; rewrite formula_rename_preserves_measure`
  blocks in `forall_mono`/`exists_mono`.
