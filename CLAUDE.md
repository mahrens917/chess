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
