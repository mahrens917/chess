# Endgame Dead-Position Plan (Semantic `Rules.isDeadPosition`)

This repo already has a semantic dead-position proof for **K vs K** (`Chess/KkDeadPositionProofs.lean`).

This document is the roadmap for extending that approach to the next “insufficient material” endgames,
with **Prop-level proofs** (not just `deadPosition`/`insufficientMaterial` Bool heuristics).

## Scope

Target statement shape (per endgame family):

> If a game state satisfies an explicit endgame invariant (exactly these pieces, legal king separation, etc),
> then `Chess.Rules.isDeadPosition gs`.

Reminder: `Rules.isDeadPosition` is the *legal-sequence* definition:
no legal sequence of moves can reach a checkmate.

## Shared Infrastructure (Already Landed)

- K vs K invariant + closure + `isDeadPosition` theorem: `Chess/KkDeadPositionProofs.lean`
- Kings+one-minor board invariant and “who can give check” lemmas: `Chess/KMinorBoard.lean`
- K+minor closure under `applyLegalMove(s)` (either stays K+minor or collapses to K vs K): `Chess/KMinorDeadPositionInvariants.lean`

## Next Targets (In Order)

### 1) K+N vs K

1. Define invariant `KknInv gs`:
   - board contains exactly two kings and one knight (either side)
   - kings are not adjacent (`¬ Movement.isKingStep wk bk`)
2. Prove closure under `applyLegalMoves`:
   - legal moves cannot create new pieces (no promotion/castling/EP in this material)
   - captures can reduce `KknInv` to the existing K vs K invariant (`KkInv`)
3. Prove “no checkmate is possible” lemma:
   - `KknInv gs → Rules.isCheckmate gs = false`
   - core obligation: if the side-to-move is in check, construct a legal response (king move or capture)
4. Conclude `KknInv gs → Rules.isDeadPosition gs`.

### 2) K+B vs K

Same template as K+N vs K, but the “no checkmate possible” lemma uses bishop geometry:
the bishop can only control one color-complex, which prevents covering all king escapes.

## Shared Subgoal: “Escape Move Exists” Lemma (Recommended)

In K+minor vs K endgames, the checked side (if any) is always the **lone king** side, and the check
comes from the **single minor** (assuming kings are not adjacent).

To show `isCheckmate = false` in the “in check” branch, it is enough to prove:

> If the lone king is in check by a single bishop/knight and the kings are not adjacent,
> then there exists a legal king move to an empty square that is not attacked in the resulting position.

Suggested structure:

1. Use `Chess/KMinorBoard.lean`:
   - `KingsPlusMinor.inCheck_*_implies_minor_attacker` to identify the checking piece and rule out king-adjacency checks.
2. Construct a **concrete** escape king step (often an orthogonal step chosen to keep kings non-adjacent).
3. Show the destination is empty via the `KingsPlusMinor` emptiness clause.
4. Show the move is safe by ruling out attacks from:
   - the enemy king (by non-adjacency), and
   - the minor (by bishop/knight geometry after the step).
5. Conclude the move is in `allLegalMoves` via `mem_allLegalMoves_iff_encodedLegal`.

### 3) K+NN vs K

Same template, but needs a careful “no checkmate possible” lemma (two knights can give check, but still cannot mate).

### 4) K+BB (same-color bishops) vs K

Same template; key geometry invariant is “all bishop attacks live on one color-complex”.

## Acceptance Gate Integration

For each new theorem, add a `#check` to the proof bar:
- `Test/AcceptanceGate.lean`

And index it:
- `THEOREM_INDEX.md`

And check it off in:
- `CHECKLIST_ANALYTICAL_LIBRARY.md`
