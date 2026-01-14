# Acceptance Gate (“What Does 100% Mean Here?”)

This repo aims to be a **rules-complete** and **proof-carrying** chess library, with an optional
analysis layer.

Because “100% complete” is ambiguous, we define a mechanically checkable acceptance bar.

## Current Bar: Rules-Complete + Semantic-Equivalent (Reachable) + Baseline Analysis Correct

We consider the repo “complete” at this bar when:

1) **Rules engine is rules-complete**
- Move generator spec: `Chess/Spec.lean` (`allLegalMoves_iff_fideLegal`)
- Generator correctness vs encoded spec: `Chess/RulesComplete.lean`

2) **Semantic (FIDE-like) legality matches the generator for reachable states**
- Equivalence: `Chess/SemanticFideLegalEquivalenceReachable.lean`
  (`fideLegalSemantic_iff_mem_allLegalMoves_of_reachable`)

3) **Core computational properties are proven**
- Perft correctness: `Chess/PerftProofs.lean` (`perft_correct`)

4) **Baseline analysis implementation matches its minimax spec**
- Spec: `Chess/Analysis/MinimaxSpec.lean` (`minimaxValue`)
- Equivalence: `Chess/Analysis/Equivalence.lean` (`negamax_eq_minimaxValue`)

5) **Alpha-beta correctness slices are proven**
- Depth 1: `Chess/Analysis/AlphaBetaDepth1Proofs.lean` (`alphaBeta_depth1_eq_minimaxValue`)
- Depth 2: `Chess/Analysis/AlphaBetaDepth2Proofs.lean` (`alphaBeta_depth2_eq_minimaxValue`)

6) **The above is mechanically enforced**
- `Test/AcceptanceGate.lean` is imported by `Test/TestDriver.lean`, so `lake test` fails if any
  of the required theorems/modules stop compiling.

7) **Core invariants are enforced for generated moves**
- En passant rank validity is preserved by `playMove` for any `m ∈ allLegalMoves gs`
  (`Chess/StateInvariants.lean`: `hasValidEPRank_playMove_of_mem_allLegalMoves`).
- Generated moves never target a king square
  (`Chess/Rules.lean`: `mem_allLegalMoves_implies_not_king_destination`).

## How To Check

Fast (recommended):

```bash
LAKE_JOBS=1 lake build Chess.Proofs
LAKE_JOBS=1 lake test
```

Full (includes slow perft fixtures):

```bash
LAKE_JOBS=1 lake build
LAKE_JOBS=1 lake test
LAKE_JOBS=1 lake exe slowtest
```

## Not Included In This Bar (Yet)

- Alpha-beta (or other) optimizations with equivalence proofs.
- Fully formal round-trip theorems for FEN/SAN/PGN (see `PARSER_PROOF_BAR.md`).
- A semantic “dead position means no mate is reachable” theorem.
