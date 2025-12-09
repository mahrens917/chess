# Chess Formalization Roadmap

This document tracks every open item on the path from the current Lean implementation to a provably correct, fully featured chess engine and beyond.

## 1. Reach Full Chess Feature Compliance
- **Move application consistency**
  - Route every state transition (`perft`, generators, demos) through `GameState.playMove` so checkmate/stalemate/draw flags are always finalized.
  - Audit for direct `movePiece` usage and either prove safety lemmas or eliminate the calls.
- **Rule coverage gaps**
  - Ensure en-passant availability requires a legal double-push history, not just board plausibility.
  - Enforce half-move/full-move counters inside SAN/PGN play to detect 50/75-move draws mid-game.
  - Verify automatic draw detection triggers when PGN-specified results disagree with board state.
  - Model underpromotion captures from SAN/PGN with explicit target piece validation.
  - Guarantee history snapshots include the starting position loaded via FEN/PGN for repetition checks.
- **Parsing robustness**
  - FEN: validate impossible castling flags (king/rook moved) via move history metadata where available.
  - SAN: support all suffix annotations (`!!`, `!?`, `??`), “ep” markers, and algebraic ambiguity detection for rare piece counts (e.g., four knights).
  - PGN: handle comments/variations deterministically (reject unsupported constructs with clear errors).
- **Demo polish**
  - Demonstrate FEN/SAN/PGN round-trips, en-passant, castling, and draw detection in `chessDemo`.
  - Provide CLI flags or inputs to load PGN/FEN from files for reproducible showcases.
- **Documentation**
  - Expand README with end-to-end usage examples (parsing a PGN, running perft, invoking slow tests).
  - Record FEN/SAN/PGN specification references and any deviations.

## 2. Testing Requirements
- **Fast suite (`lake test`)**
  - Cover every rule branch: castling legality, en-passant validation, promotion variants, repetition/draw triggers, parser round-trips.
  - Assert that SAN check/mate hints are validated across diverse boards.
  - Include canonical perft depths (1–3 for start, plus tactical FENs) with expected node counts.
- **Slow/extended suite (`RUN_SLOW_TESTS=1`)**
  - Deeper perft baselines (depth 4–5) for start and edge-case FENs (castling, en-passant).
  - Full PGN game corpus samples (e.g., famous games, tablebase endings) to exercise long sequences.
  - Stress FEN loader with random legal positions (coordinated with generator once available).
- **Continuous integration**
  - Make slow tests part of release workflow or nightly build.
  - Capture test commands/results in PR templates.

## 3. Documentation Artifacts
- **Specification references**
  - Link to official FIDE Laws of Chess, PGN standard, and SAN/FEN documents.
  - Document assumptions (e.g., clocks ignored, no adjournments).
- **Developer guides**
  - Explain how to add new rules plus the proofs/tests required.
  - Checklist for introducing new parsing features or demo scenarios.
- **User/demo docs**
  - Walkthrough for deriving SAN from a board, playing PGN files, and exporting FEN snapshots.

## 4. Formal Proof Backlog
- **Core theorems**
  - Prove `allLegalMoves` exactly matches the encoded rules (piece movement, castling, en-passant, promotions).
  - Show `GameState.playMove` preserves board invariants (single occupancy, piece counts) and updates clocks correctly.
  - Formalize draw detection correctness: 50/75-move rules, repetition counts, insufficient material classifications.
  - Demonstrate SAN/FEN/PGN parser soundness (parsed game reproduces original when serialized) and completeness (all legal SAN strings parse).
- **Perft correctness**
  - Prove `perft` counts match the recursive expansion definition using induction over depth.
- **History/repetition**
  - Establish the link between stored `history` snapshots and the official repetition rules.
- **Documentation of proofs**
  - Record theorem names and statements in README/CLAUDE requirements, ensuring future contributors see the growing proof corpus.

## 5. Search Space Tracking System

Every reduction must be **computable** - we track exact search space at each step.

### 5.1 Core Data Structures

```lean
/-- A proven reduction with its exact factor -/
structure ProvenReduction where
  name : String
  factor : ℕ                           -- Exact reduction factor (e.g., 2 for color symmetry)
  proof : ProofCertificate             -- Link to Lean theorem
  applies : GameState → Bool           -- When does this reduction apply?
  count : GameState → ℕ                -- Positions eliminated in this state

/-- Running search space tracker -/
structure SearchSpaceState where
  currentEstimate : ℕ                  -- Current search space size
  appliedReductions : List ProvenReduction
  remainingCandidates : List ReductionCandidate
  computationLog : List (String × ℕ)   -- (reduction name, space after)
```

### 5.2 Implementation Phases

**Phase 1: Baseline Computation**
- [ ] Implement `countLegalPositions : ℕ → ℕ` - count positions reachable in N plies
- [ ] Implement `estimateStateSpace : ℕ` - compute Tromp's 2×10^44 from first principles
- [ ] Implement `branchingFactor : GameState → ℕ` - exact legal move count
- [ ] Prove: `branchingFactor gs = (allLegalMoves gs).length`

**Phase 2: Reduction Pipeline**
- [ ] Each reduction is a `ProvenReduction` with computable factor
- [ ] `applyReduction : SearchSpaceState → ProvenReduction → SearchSpaceState`
- [ ] Log every application: `(name, before, after, factor)`
- [ ] Invariant: `after = before / factor` (with proof)

**Phase 3: Computable Reductions**
| Reduction | Factor Formula | Implementation |
|-----------|---------------|----------------|
| Color symmetry | `2` | `÷ 2` always |
| Board reflection | `symmetricPositions gs / totalPositions` | Compute per-position |
| 50-move rule | `drawableByRule gs ? 0 : current` | Prune when drawable |
| Repetition | `seenBefore gs ? 0 : current` | Prune on repeat |
| Insufficient material | `isDead gs ? 0 : current` | Prune dead positions |
| Alpha-beta | `√(branchingFactor gs)` | Per-node reduction |

**Phase 4: Live Tracking Output**
```
Starting search space: 2.00 × 10^44
After color symmetry (÷2): 1.00 × 10^44  [Proven: Color.opposite_opposite]
After transposition (÷10^79): 1.00 × 10^44  [Note: already at position level]
After alpha-beta (÷10^22): 1.00 × 10^22  [Proven: alpha_beta_correct]
After 50-move pruning (÷10^3): 1.00 × 10^19  [Proven: fifty_move_terminates]
...
Current estimate: X.XX × 10^N
Gap to feasibility (10^20): 10^(N-20)
```

### 5.3 Proof Requirements Per Reduction

Each reduction MUST have:
1. **Soundness theorem**: Reduction doesn't change game-theoretic value
2. **Factor theorem**: Exact reduction factor is provably correct
3. **Decidability**: `applies` function is computable
4. **Composition**: Combining with other reductions is sound

## 6. Reduction Discovery System

A systematic process for finding and proving new search space reductions.

### 6.1 The Discovery Loop

```
┌─────────────────────────────────────────────────────────────┐
│                    DISCOVERY SYSTEM                          │
├─────────────────────────────────────────────────────────────┤
│                                                              │
│  ┌──────────┐    ┌──────────┐    ┌──────────┐    ┌────────┐│
│  │ IDENTIFY │───▶│ FORMALIZE│───▶│  PROVE   │───▶│QUANTIFY││
│  └──────────┘    └──────────┘    └──────────┘    └────────┘│
│       │                                              │      │
│       │              ┌──────────┐                    │      │
│       └──────────────│IMPLEMENT │◀───────────────────┘      │
│                      └──────────┘                           │
│                           │                                 │
│                           ▼                                 │
│                    ┌──────────┐                             │
│                    │  TRACK   │──▶ Update SearchSpaceState  │
│                    └──────────┘                             │
└─────────────────────────────────────────────────────────────┘
```

### 6.2 Discovery Sources

**Source A: Chess Knowledge Mining**
- [ ] Endgame theory (fortresses, wrong-colored bishop, etc.)
- [ ] Opening theory (transposition classes)
- [ ] Middlegame patterns (piece coordination bounds)
- [ ] Known tablebase properties (DTZ patterns)

**Source B: Structural Analysis**
- [ ] Pawn structure equivalence classes
- [ ] King safety zone enumeration
- [ ] Piece mobility bounds by position
- [ ] Blocked position detection

**Source C: Automated Search**
- [ ] Generate random positions, cluster by outcome
- [ ] Find invariants that predict game-theoretic value
- [ ] Use Lean's tactic framework to search for proofs

**Source D: Literature Review**
- [ ] Allis (1994) - game-theoretic techniques
- [ ] Tromp - position enumeration methods
- [ ] Tablebase papers - retrograde analysis

### 6.3 Candidate Evaluation Criteria

| Criterion | Weight | Question |
|-----------|--------|----------|
| **Provability** | 40% | Can we write a Lean proof? |
| **Factor size** | 30% | How much does it reduce? (10^N) |
| **Applicability** | 20% | What % of positions does it apply to? |
| **Compute cost** | 10% | Is detection O(1), O(n), O(n²)? |

Score = Provability × Factor × Applicability / ComputeCost

### 6.4 Current Candidate Queue

| Priority | Candidate | Est. Factor | Proof Path | Status |
|----------|-----------|-------------|------------|--------|
| 1 | `allLegalMoves` completeness | - | Induction on piece types | **In Progress** |
| 2 | Fortress patterns | 10^2 | Case enumeration | Not Started |
| 3 | Opposite-color bishop draw | 10^1 | Tablebase verification | Not Started |
| 4 | Pawn structure hashing | 10^2 | Equivalence relation | Not Started |
| 5 | Zugzwang detection | 10^1 | Position analysis | Not Started |
| 6 | Blockade detection | 10^2 | Pawn chain analysis | Not Started |

### 6.5 Promotion Criteria

A candidate becomes a `ProvenReduction` when:
1. ✓ Lean theorem compiles and type-checks
2. ✓ Factor is computed exactly (not estimated)
3. ✓ Detection function passes all tests
4. ✓ Composition with existing reductions is proven sound
5. ✓ Added to `SearchSpaceState.appliedReductions`

## 7. Beyond Full Compliance: Toward Solving Chess

- **Symmetry reductions**
  - Formally prove color-flip and rotational symmetries so equivalent positions can be collapsed.
- **Recursive decomposition**
  - Identify substructures (pawnless endings, locked pawn files) and prove they reduce to smaller solved cases.
- **Pruning invariants**
  - Prove sufficient conditions for pruning (fortresses, perpetual checks, tablebase draws) during search.
- **Automated strategy**
  - Combine reductions and pruning into a verified search that incrementally increases solved depth.
- **Long-term milestone**
  - Aim for endgame-tablebase proofs, then middlegame strategies, ultimately inching toward a complete solution.
