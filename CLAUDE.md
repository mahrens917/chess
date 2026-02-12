# Chess Formalization Project

## Mission
Enshrine the complete rules of chess in Lean 4 with formal proofs, then exploit symmetries and structural invariants to systematically reduce the game-tree search space — working toward computing the theoretically perfect game.

### Three-phase strategy
1. **Rules in Lean** — encode every FIDE rule as a decidable predicate with a matching soundness/completeness proof.
2. **Search-space measurement** — quantify the game tree from first principles (positions, branching factor, depth bounds) and track it in `Chess/SearchSpace.lean`.
3. **Reduction & solve** — discover, prove, and compose symmetries (color, reflection, transposition), pruning invariants (draws, fortresses, alpha-beta), and decomposition lemmas (endgame tables, pawn structure classes) until the effective search space is computationally tractable.

## Claude Agent Requirements

### Formal Proof Mandate
- Treat executable tests as smoke checks only; every rule, parser, or helper change must include Lean proofs or lemmas that precisely encode the intended chess invariant (move legality, result finalization, draw detection, parsing round-trips, etc.).
- Refuse to mark tasks complete until the accompanying theorems are written, type-checked, and linked from the touched modules.
- When existing code lacks proofs, prioritize backfilling formal statements before extending features.
- Every search-space reduction must have a **soundness theorem** (doesn't change game-theoretic value) and a **factor theorem** (exact reduction factor provably correct) before it can be promoted from "conjectured" to "proven" in `SearchSpace.lean`.

### Documentation Requirements
- When adding or modifying FEN/SAN/PGN behavior, update the README "Notation Cheat Sheet" plus any usage notes so contributors can see the supported syntax at a glance.
- Cite the exact specification (FIDE Laws, PGN, SAN, FEN) that justifies each change and link the relevant Lean declarations inside PR descriptions.

### Workflow Expectations
- Run `lake build`, `lake test`, and `lake exe slowTests` (when changes touch SAN/PGN/perft) after adding proofs to ensure both code and theorems compile.
- Document each proof you add in the PR description and cite the Lean declarations that establish the required behavior.

### MCP Integration
- Reach for the `solve` MCP server as soon as a subgoal devolves into symbolic grind (arithmetic rewrites, case splits, etc.). Offload the goal snippet plus hypotheses, reuse the returned Lean derivation verbatim when possible, and cite `solve` in comments if it guided the final script so other contributors can replay the tactic-free proof. Defaulting to `solve` on algebra-heavy subgoals usually slashes token usage compared to inline back-and-forth.
- Do NOT disable tests, leave them broken until they are fixed, they should be visible!