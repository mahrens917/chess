# Sliding Piece `pieceTargets` Completeness Plan (Rook/Bishop/Queen)

Goal: prove the remaining “semantic geometry ⇒ membership in `pieceTargets`” lemmas for sliding pieces:

- `fideLegalSemantic gs m → m.piece.pieceType = Rook → m ∈ Rules.pieceTargets gs m.fromSq m.piece`
- `… Bishop …`
- `… Queen …` (split into rook-like vs diagonal cases)

## Non-crossed decomposition

1) **Normalize flags (semantic → “plain sliding move”)**
   - From `fideLegalSemantic gs m`, show for non-pawn sliding pieces:
     - `m.promotion = none`
     - `m.isEnPassant = false`
     - `m.isCastle = false`
     - `m.castleRookFrom = none ∧ m.castleRookTo = none`
   - Use the existing helpers in `Chess/SemanticPieceTargetsCompletenessLemmas.lean`.

2) **Extract geometry payload**
   - From `respectsGeometry gs m` and `m.piece.pieceType = Rook/Bishop/Queen`, derive:
     - Rook: `Movement.isRookMove m.fromSq m.toSq` and `Rules.pathClear gs.board m.fromSq m.toSq = true`
     - Bishop: `Movement.isDiagonal …` and `pathClear = true`
     - Queen: `Movement.isQueenMove …` and `pathClear = true`

3) **Convert `pathClear = true` to per-square emptiness**
   - Use `Chess/PathValidationProofs.lean`: `Rules.pathClear_eq_true_iff`.

4) **Connect “move geometry” to a concrete `(df,dr)` and offset `k`**
   - Choose `(df, dr)` and `k` based on the move shape:
     - Rook: `Movement.rookDelta src tgt`, `Movement.rookOffset src tgt`
     - Bishop: `Movement.bishopDelta src tgt`, `Movement.bishopOffset src tgt`
   - Prove:
     - `(df, dr)` is in the delta list used by `Rules.pieceTargets` (rook/bishop/queen delta lists).
     - `1 ≤ k` and `k ≤ 7`.
     - `Movement.squareFromInts (src.fileInt + df * (k : Int)) (src.rankInt + dr * (k : Int)) = some tgt`.
   - This step likely needs small “integer sign / natAbs” arithmetic lemmas:
     - e.g. `Movement.signInt x * (Int.ofNat x.natAbs) = x`.

5) **Show the generator reaches `k` (intermediate squares don’t block)**
   - For each `t < k`, use step (3) + “`squareFromInts` at offset `t` lies in `Movement.squaresBetween`” to show:
     - `gs.board sq = none`, hence `Rules.isEmpty gs.board sq = true`.

6) **Prove membership in `Rules.slidingTargets.walk`**
   - Unfold `Rules.slidingTargets.walk` and induct down the `step` counter.
   - Use `Chess/SlidingTargetsCompletenessHelpers.lean`:
     - `slidingTargets_walk_mem_of_empty_square` / `slidingTargets_walk_mem_of_enemy_square`
     - `slidingTargets_walk_acc_subset` (to keep previously-added moves in the final output)

7) **Lift `walk` membership to `slidingTargets` and then to `pieceTargets`**
   - `Rules.slidingTargets` is a `foldr` over delta directions; once membership in the correct `walk` call is shown,
     conclude membership in the full `slidingTargets` list (hence in `pieceTargets`).

8) **Reconcile capture flag**
   - Split on `gs.board m.toSq`:
     - `none` → show `m.isCapture = false`
     - `some p` with `p.color ≠ m.piece.color` (from `destinationFriendlyFreeProp`) → show `m.isCapture = true`
   - Reuse `capture_eq_of_target_empty` / `capture_eq_true_of_target_enemy` from
     `Chess/SemanticPieceTargetsCompletenessLemmas.lean`, then rebuild `m` via record equality.

