# Code Quality Refactor Workflow

Use this workflow when the repo has accumulated proof-engineering debt after
several design-route changes: stale plans, old bridge lemmas, wrapper files,
misleading names, slow proof scripts, duplicated set/store reasoning, or
notation/definition aliases that only exist for parsing.

The goal is not cosmetic churn.  The goal is to make future lemma search and
proof repair easier while preserving the current semantic route.

## Refactor Contract

- Preserve the current proved route first.  In this repo, that means the direct
  `Fundamental` route and the proved direct cases:
  `Var`, `Const`, `Sub`, `CtxSub`, `Let`, and `AppOp`.
- Keep semantic boundary lemmas even when they are single-use:
  `ty_denote_gas_tm_equiv`, result-alias/result-extension transport,
  `tlet_intro_denotation`, context intro/elimination boundaries, and induction
  package lemmas.
- Delete old-route glue when it is no longer imported by the current theorem:
  fiberwise Fundamental helpers, giant type-denotation msubst transports,
  double bridge obligations, stale compatibility wrappers, and smoke-only
  notation tests.
- Do not treat `Interface` filenames as public surfaces.  They are often
  specialization layers; clean unused wrappers inside them just like any other
  file.
- `set_solver` is allowed.  The cleanup target is handwritten concrete
  stdpp/store lemma chains, not use of `set_solver`.

## Required Passes

### 1. Establish the current route

Before deleting anything, identify the active proof path.

Commands:

```sh
rg -n "Theorem Fundamental|Lemma fundamental_|Admitted\\.|admit\\." ContextTyping Denotation
rg -n "denot_ty_in_ctx_under_fiber|context_typing_wf_erased|ContextTypeDenotationMsubst|_soundness_bridge" .
```

Record what is proved, what is intentionally admitted, and which names are
historical.  Do not optimize a stale route merely because it still compiles.

### 2. Build a lemma usage index

For each directory, count declarations and whole-token uses.  Classify each
zero/single-use lemma:

- **Keep**: semantic boundary, induction split, compile-time proof cache, solver
  support, or foundational syntax/typing/library fact.
- **Inline**: short wrapper, exact restatement, or one-off proof block whose
  statement is harder to search than the call site.
- **Delete**: no source use, old route only, notation smoke, stale plan support,
  duplicate synonym.
- **Lower**: generic set/store/map/open/fv reasoning currently trapped in a
  high-level Denotation/Typing file.

Do not count notation/export-only references as real semantic uses.

### 3. Remove old plans and stale reports

Delete TXT reports/plans after their useful content has been folded into a
living index or skill.  Keep one current index, such as `LemmaUsageIndex.txt`,
that records:

- current declaration counts;
- what was deleted;
- what was intentionally retained;
- known long proofs kept for compile-time reasons.

### 4. Clean wrappers and aliases

Search for parsing-only or historical aliases:

```sh
rg -n "Smoke|only parsing|Definition .*:=|Notation" README.md skills *.txt \
  CoreLang ContextTypeLanguage ContextLogic ContextAlgebra Denotation ContextTyping
```

Delete:

- smoke modules used only to test notation parsing;
- unused surface wrapper files;
- duplicate local/global notation declarations;
- aliases like `foo_ctx := foo (erase_ctx Γ)` when all real uses can be unfolded
  clearly.

Keep:

- local `StoreT`/`WorldT` notations that reduce section noise;
- active theorem-target shorthands, even if they are thin, when removing them
  would obscure the proof statements;
- user-facing notation that appears in statements or current proofs.

### 5. Strengthen solvers, then simplify proofs

When many proofs manually destruct stdpp/store facts, prefer solver support:

- add lvar/fv/context-domain normalization to set tactics;
- add store-restrict lookup/domain/twice normalization to store tactics;
- add small map lookup helpers for singleton/insert/union/restrict patterns.

Then revisit high-level proofs.  Replace repeated concrete chains with:

```coq
set_solver.
better_store_solver.
eauto 6 with core.
```

If a direct solver call makes compile time worse, keep the helper and add a
short comment saying it is retained as a proof-checking cache.

### 6. Long proof review

Audit proofs over roughly 200 lines.

Split only when the extracted lemma is meaningful:

- syntax-shaped transport, e.g. `FAnd` to `FAnd`, `FImpl` map, `FForall` map;
- store/resource projection facts;
- open/fv normalization packets;
- term-result equivalence package construction.

Do not extract a giant lemma with all the same long premises.  If the helper's
statement is harder to read than the original proof, use local assertion
packets instead.

### 7. File organization

Organize files by semantic layer, not by proof accident:

- syntax/open/fv facts stay in syntax/type-language files;
- store/restrict/map facts stay in Store;
- resource product/sum/fiber facts stay in Algebra;
- formula shape and `res_models` facts stay in Logic;
- term total/result/basic atoms stay in BasicDenotation;
- recursive type denotation and term-result-equivalence stay in Denotation;
- paper-level typing and Fundamental case dispatch stay in ContextTyping.

Wrapper files are acceptable only when they are real aggregators imported by
many files.  Delete wrappers that only re-export a deleted route or exist to
hold smoke examples.

### 8. Documentation cleanup

After code changes, update non-Rocq text:

- README file tables must match actual files in `_CoqProject`;
- build instructions must match the repo (`rocq makefile -f _CoqProject -o Makefile`);
- skills should distinguish current rules from historical notes;
- stale design reports should either be deleted or summarized in the current
  index/skill.

## Validation Checklist

Run focused builds after each batch, then full build:

```sh
make ContextAlgebra/theories/ContextAlgebra.vo
make ContextLogic/theories/LogicInterface.vo
make Denotation/theories/Context.vo
make ContextTyping/theories/Soundness.vo
make
```

Scan old-route names:

```sh
rg -n "denot_ty_in_ctx_under_fiber|context_typing_wf_erased|ContextTypeDenotationMsubst|_soundness_bridge|appop_intro_denotation_msubst" .
```

Expected result: old names appear only in cleanup records, not in active Rocq
source or README route descriptions.

## Lessons From This Branch

- Reverting to the direct `Fundamental` route made several fiberwise/msubst
  bridge layers obsolete; deleting them simplified both proof search and docs.
- `ty_denote_gas_tm_equiv` is a durable semantic abstraction.  Keep it: it
  replaced large case-specific TLet/result-alias proofs.
- Notation smoke modules are not worth keeping once notations are stable.
- `Interface` files were a poor proxy for public API; treat them as ordinary
  implementation files during cleanup.
- A single living index is more useful than many stale plan TXT files.
- Some thin aliases are useful theorem-language shorthands; others only hide
  definitions.  Decide by current proof role, not by syntactic thinness alone.
