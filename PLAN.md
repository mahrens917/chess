# Chess Formalization Roadmap

This document tracks every open item on the path from the current Lean implementation toward a provably correct, fully formalized chess engine — and beyond, toward computing the perfect game.

## Phase 1 — Seal the Rule Layer (current)

Close every `sorry` and eliminate the lone axiom so the entire rule layer is provably correct.

| Item | File | Status |
|------|------|--------|
| `same_color_bishops_dead` | `DeadPositionProofs.lean:835` | **TODO** |
| `deadPosition_sound_aux` | `DeadPositionProofs.lean:855` | **TODO** |
| `parseSanToken_succeeds_on_moveToSAN` | `Parsing_SAN_Proofs.lean:886` | **TODO** |
| `parseSanToken_extracts_moveToSanBase` | `Parsing_SAN_Proofs.lean:895` | **TODO** |
| `moveFromSanToken_finds_move` | `Parsing_SAN_Proofs.lean:1337` | **TODO** |
| `moveFromSAN_moveToSAN_roundtrip` | `Parsing_SAN_Proofs.lean:651` | **TODO** |
| `parseSanToken_normalizes_castling` | `Parsing_SAN_Proofs.lean:1396` | **TODO** |
| `moveToSAN_unique_full` | `PerftProofs.lean:53` | **TODO** |
| `allLegalMoves_nodup` (axiom → theorem) | `PerftProofs.lean:87` | **TODO** |

### Dependency order
1. `allLegalMoves_nodup` — used by perft completeness
2. `moveToSAN_unique_full` — depends on move generator structure
3. SAN round-trip proofs — depend on `moveToSAN_unique_full`
4. Dead position proofs — independent, can be done in parallel

## Phase 2 — Quantify the Search Space

Make the search-space estimates computable instead of string-based.

- [ ] `branchingFactor : GameState → Nat` with proof `= (allLegalMoves gs).length`
- [ ] `countLegalPositions : Nat → Nat` — positions reachable in N plies
- [ ] State-space upper bound (Tromp's ~2×10^44) from first principles
- [ ] Replace string estimates in `SearchSpace.lean` with `Nat` values backed by computable definitions
- [ ] Prove: `branchingFactor gs = (allLegalMoves gs).length`

## Phase 3 — Prove Symmetry Reductions

Each reduction requires a **soundness theorem** (doesn't change game-theoretic value) and a **factor theorem** (exact reduction factor).

| Reduction | Factor | Proof path | Status |
|-----------|--------|------------|--------|
| Color symmetry (`value(gs) = -value(flipColor gs)`) | ÷2 | Define `flipColor`, prove rule isomorphism | Conjectured |
| Horizontal reflection (a↔h file mirror) | ÷2 | Define `mirror`, prove legality preservation | Conjectured |
| Transposition tables (identical board states) | ÷10^5+ | Prove position equality decidable | Conjectured |
| Composition soundness (combining the above) | — | Prove reductions commute | Not started |

## Phase 4 — Prove Pruning Invariants

| Pruning rule | Factor | Status |
|-------------|--------|--------|
| 50/75-move rule bounds tree depth to ~150 plies | large | Draw detection proven; depth bound not yet |
| 3-fold / 5-fold repetition prunes cycles | ~10^0.5 | Detection proven; tree pruning factor not yet |
| Insufficient material prunes dead subtrees | ~10^0.5 | Detection proven; factor not yet |
| Alpha-beta: `alphaBeta gs α β = minimax gs` within window | ÷√(tree) | Partly proven in `Analysis/` |
| Fortress detection (blocked-pawn draw configs) | ~10^2 | Not started |
| Zugzwang / blockade detection | ~10^1–10^2 | Not started |

## Phase 5 — Endgame Decomposition

- [ ] Formalize 3–5 piece endgame tablebases (KQK, KRK, KPK, KBN-K, …)
- [ ] Prove retrograde analysis correctness: tablebase values are game-theoretically exact
- [ ] Pawn-structure equivalence classes: positions with identical pawn skeletons share evaluations
- [ ] Wrong-colored bishop, opposite-color bishop draws as pruning lemmas

## Phase 6 — Automated Reduction Discovery

- [ ] Build `ProvenReduction` pipeline (computable factor, soundness theorem, detection function, composition proof)
- [ ] Live tracking: `lake exe searchSpace` reports estimate after each proven reduction
- [ ] Cluster positions by outcome (automated invariant search)
- [ ] Use Lean tactic framework to search for proof-backed reductions

### Candidate queue

| Priority | Candidate | Est. factor | Status |
|----------|-----------|-------------|--------|
| 1 | Fortress patterns | 10^2 | Not started |
| 2 | Opposite-color bishop draw | 10^1 | Not started |
| 3 | Pawn structure hashing | 10^2 | Not started |
| 4 | Zugzwang detection | 10^1 | Not started |
| 5 | Blockade detection | 10^2 | Not started |

### Promotion criteria
A candidate becomes a `ProvenReduction` when:
1. Lean theorem compiles and type-checks
2. Factor is computed exactly (not estimated)
3. Detection function passes all tests
4. Composition with existing reductions is proven sound
5. Added to `SearchSpaceState.appliedReductions`

## Phase 7 — Toward the Solve

- [ ] Combine all proven reductions; measure effective search space; determine gap to feasibility (~10^20 ops)
- [ ] Verified search at increasing depth: prove game-theoretic value for depth-1, 2, … positions
- [ ] Integrate tablebase results bottom-up to extend proven depth
- [ ] Identify narrowest bottleneck (which middlegame structures resist reduction) and target specifically
