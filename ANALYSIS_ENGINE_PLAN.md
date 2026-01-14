# Analysis / Engine Layer Plan

This repo currently focuses on correct move generation, rule enforcement, parsing, and proof scaffolding.

If you want a “100% complete chess analytical library” to include engine-grade analysis (search),
this document defines an incremental plan that keeps the existing executable rules as the reference
model and adds a provably-correct analysis layer on top.

## Scope Choices (pick one)

### A) Minimal “Analytical Library” (recommended first)
- Deterministic, depth-limited search
- Simple evaluation (material + piece-square tables)
- No time management, no transposition tables required

### B) Engine-Grade
- Iterative deepening + time management
- Transposition tables + repetition-aware draw logic
- Move ordering + quiescence search
- Refinement proofs for any optimized representations

## Core Deliverables (in order)

### 1) Define the spec
- Define a pure value function over `GameState`, e.g. `minimaxValue (depth : Nat) : GameState → Int`
- Define terminal handling: checkmate/stalemate/draw (use `finalizeResult` semantics)
- Define draw policy choices (claimable vs automatic) and pin it down in `ASSUMPTIONS_AND_SCOPE.md`

### 2) Implement a baseline search
- Implement a simple recursive search using `allLegalMoves` and `GameState.playMove`
- Keep it obviously-correct and “slow but simple”
- Add tests that compare small-depth node counts and PV legality

### 3) Prove functional correctness
- Prove “baseline search returns minimaxValue”
- Prove PV extraction returns a list of legal moves and each step is consistent with the chosen argmax/argmin

### 4) Optimize with proofs
Each optimization should come with a theorem that it refines the baseline search:
- Alpha-beta pruning equivalence to minimax
- Transposition table soundness (memoization does not change result)
- Repetition-aware pruning equivalence to draw semantics

Alpha-beta is currently implemented and partially proven:
- Implementation: `Chess/Analysis/AlphaBeta.lean`
- Slices: `Chess/Analysis/AlphaBetaDepth1Proofs.lean`, `Chess/Analysis/AlphaBetaDepth2Proofs.lean`
- Full roadmap: `ALPHABETA_FULL_CORRECTNESS_PLAN.md`

### 5) Performance representations (optional)
- Bitboards, incremental attack maps, Zobrist hashing, etc.
- Each needs a refinement theorem to the baseline board model (`Board` in `Chess/Core.lean`)

## Testing Requirements

- Add a new test suite file under `Test/` with:
  - PV legality checks
  - Small “known best move” fixtures (optional)
  - Regression checks for draw handling under repetition/50-move
- Keep `lake test` running everything deterministically.

## Proof/Module Layout

Recommended module grouping:
- `Chess/Analysis/Spec.lean` (minimax spec)
- `Chess/Analysis/Baseline.lean` (reference implementation)
- `Chess/Analysis/AlphaBeta.lean` (alpha-beta implementation; equivalence proof still pending)
- `Chess/Analysis/Proofs.lean` (equivalence theorems)
- `Test/AnalysisProofs.lean` (type-check “proof surface” is on-build)
