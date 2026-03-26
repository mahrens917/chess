# Claude Agent Requirements

## Formal Proof Mandate
- Treat executable tests as smoke checks only; every rule, parser, or helper change must include Lean proofs or lemmas that precisely encode the intended chess invariant (move legality, result finalization, draw detection, parsing round-trips, etc.).
- Refuse to mark tasks complete until the accompanying theorems are written, type-checked, and linked from the touched modules.
- When existing code lacks proofs, prioritize backfilling formal statements before extending features.

## Documentation Requirements
- When adding or modifying FEN/SAN/PGN behavior, update the README "Notation Cheat Sheet" plus any usage notes so contributors can see the supported syntax at a glance.
- Cite the exact specification (FIDE Laws, PGN, SAN, FEN) that justifies each change and link the relevant Lean declarations inside PR descriptions.

## Workflow Expectations
- Run `lake build`, `lake test`, and `lake exe slowTests` (when changes touch SAN/PGN/perft) after adding proofs to ensure both code and theorems compile.
- Document each proof you add in the PR description and cite the Lean declarations that establish the required behavior.

## MCP Integration
- Reach for the `solve` MCP server as soon as a subgoal devolves into symbolic grind (arithmetic rewrites, case splits, etc.). Offload the goal snippet plus hypotheses, reuse the returned Lean derivation verbatim when possible, and cite `solve` in comments if it guided the final script so other contributors can replay the tactic-free proof. Defaulting to `solve` on algebra-heavy subgoals usually slashes token usage compared to inline back-and-forth.
- Do NOT disable tests, leave them broken until they are fixed, they should be visible!

## Test Isolation
- Tests must NEVER touch production resources. All test operations must be fully isolated:
  - **Files**: Use `tmp_path` or temporary directories — never read, write, truncate, or delete files in production paths (e.g., `logs/`, `data/`, `config/`).
  - **Redis**: Use mocks or a dedicated test Redis database — never publish, subscribe, or modify keys in the production Redis instance.
  - **Databases**: Use test fixtures or in-memory databases — never connect to or modify production databases.
  - **External services**: Mock all external API calls and network requests.
- The root cause of production log loss was tests calling `_clear_logs()` against the real `logs/` directory. Monkeypatch paths to `tmp_path` in any test that touches the filesystem.