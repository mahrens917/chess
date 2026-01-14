# Assumptions & Scope

This repository has three “layers” with different completeness bars.

## Layer 1: Executable Chess Rules (Implemented + Tested)

The Lean code under `Chess/` implements:
- Move generation (`Rules.allLegalMoves`)
- Move application (`GameState.playMove`)
- Check detection (`Rules.inCheck`)
- Draw helpers (50/75-move, repetition, plus additional endgame predicates)
- FEN/SAN/PGN tooling (parse/print/replay/export)

These are heavily regression-tested via `lake test`.
FEN parsing seeds history snapshots; when an en passant target is present, the parser infers the prior
double-push snapshot so repetition accounting remains consistent.

## Layer 2: Rules-Complete Formal Spec (Generator-Exact)

For “rules-complete” development, the Prop-level legality predicate is defined to match the current
executable move generator:

- `Chess/RulesComplete.lean`: `encodedLegal gs m`
- `Chess/Spec.lean`: `fideLegal := encodedLegal`
- Theorem: `m ∈ allLegalMoves gs ↔ fideLegal gs m`

This gives a two-sided, non-ambiguous formal contract for the current implementation.

## Layer 3: Semantic (FIDE-like) Formal Spec (In Progress)

`Chess/Spec.lean` also defines `fideLegalSemantic`, intended to look like an “official rules”
predicate (piece geometry + path clearance + EP/castling/promotion constraints + king safety).

Equivalence to the executable generator is not yet fully proven; the main remaining proof work is:
- semantic soundness: `m ∈ allLegalMoves gs → fideLegalSemantic gs m`
- semantic completeness: `fideLegalSemantic gs m → m ∈ allLegalMoves gs`
- pawn/EP semantics *soundness and completeness* for the generator (advance, capture, en passant, promotion)
- castling semantic soundness/completeness (rights + empty squares + “through-check” safety)
- “safety filter” proof: `basicLegalAndSafe` / `allLegalMoves` implies the semantic `¬inCheck` clause

Already completed building blocks:
- sliding move geometry + path clearance for rook/bishop/queen targets (`Chess/SemanticSlidingGeometryLemmas.lean`, `Chess/SemanticSlidingPathClearLemmas.lean`)
- Bool/Prop bridge for attacks and `inCheck` (`Chess/AttackSpec.lean`)
- corrected pawn attack geometry (`Movement.isPawnCapture` now matches the coordinate system used by move generation and check detection)

Practical note: perft baselines in the test suite are treated as the executable “ground truth” and are
periodically revalidated against Stockfish for representative positions (not a proof, but a guardrail).

## “100% Complete” (Definition of Done)

This repo can mean “100% complete” at different bars; we treat each bar as a separately checkable gate.

### Gate A: Rules-Complete (Generator-Exact)
- The Prop-level spec is two-sided and exact: `m ∈ allLegalMoves gs ↔ fideLegal gs m` (`fideLegal := encodedLegal`)
- `lake build` and `lake test` pass
- `Chess/Proofs.lean` imports keep the proof surface on-build

### Gate B: Semantic (FIDE-like) Complete
- Two-sided equivalence: `m ∈ allLegalMoves gs ↔ fideLegalSemantic gs m`
- No semantic “holes” (EP/castling/promotion/safety all proved) and no `sorry` in proof surface
- Parser/notation proof bar explicitly chosen (either formal round-trips or “tests only”)

### Gate C: Analysis / Engine Complete (Optional)
- A pure spec (`minimax` or equivalent) is defined over `GameState`
- Implementations (alpha-beta, repetition-aware logic, PV extraction) have correctness theorems vs the spec
- Performance representations (e.g., bitboards) are either absent or come with refinement proofs

## Analysis / Engine Layer (Optional)

If the repo is extended into an “analysis library” (minimax/alpha-beta/etc.), that becomes an
additional bar requiring:
- a spec (`minimax`) and terminal handling
- correctness theorems for optimized search (alpha-beta, repetition-aware logic, PV extraction)
- optional refinement proofs for performance representations (e.g., bitboards)
