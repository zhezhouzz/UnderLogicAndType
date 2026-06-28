# UnderLogicAndType Workflow Notes

This directory is intentionally small.  Current proof-engineering guidance
should stay concise and be updated when the workflow changes.

## Current Discipline

- Use a 50 second timeout for focused single-file checks.
- Use `rocq compile -time` for repeated or unclear proof-time failures.
- Stop after four timing/debugging loops and reassess the proof architecture.
- Normalize early at theorem/case boundaries:
  - erasure and context erasure;
  - relevant environments and relevant lvars;
  - locally nameless open/shift forms;
  - `formula_open` over type denotation;
  - `lty_env_open_one` over typed binder environments.
- Keep normalization equality-preserving.  Use dedicated solvers or helper
  lemmas for side conditions.
- Prefer semantic helper statements over helpers that expose raw syntax noise.
- Repeated set/store/freshness proof patterns should move downward into the
  relevant Store, Algebra, TypeLanguage, BasicDenotation, or Denotation layer.
- Avoid anonymous `admit`, and avoid long one-use `assert`/`pose` chains.
- Reviewer-facing metatheory should live next to the Rocq definitions it
  explains, not in temporary analysis reports.

## Notifications

For long checklist-style work, call `ntfy` directly. Do not use zsh
notification helper functions.

```bash
ntfy send --priority low zhe-codex "..."
ntfy send --priority high zhe-codex "..."
```
