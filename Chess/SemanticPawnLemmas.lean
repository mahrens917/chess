import Init.Omega
import Chess.PathValidationProofs
import Chess.SemanticPromotionLemmas

namespace Chess
namespace Rules

open Movement

/-!
Semantic lemmas for pawn move geometry.

These are intended as building blocks for semantic soundness/completeness proofs:
they connect the coordinates used by the executable pawn move generator to the
Prop-level predicates `Movement.isPawnAdvance` and `Movement.isPawnCapture`.
-/

theorem pawnDirection_ne_zero (c : Color) : Movement.pawnDirection c ≠ 0 := by
  cases c <;> simp [Movement.pawnDirection]

theorem isPawnAdvance_of_oneStep
    (c : Color) (src tgt : Square)
    (hSq :
      Movement.squareFromInts src.fileInt (src.rankInt + Movement.pawnDirection c) = some tgt) :
    Movement.isPawnAdvance c src tgt := by
  have hFile :
      tgt.fileInt = src.fileInt :=
    Movement.squareFromInts_fileInt src.fileInt (src.rankInt + Movement.pawnDirection c) tgt hSq
  have hRank :
      tgt.rankInt = src.rankInt + Movement.pawnDirection c :=
    Movement.squareFromInts_rankInt src.fileInt (src.rankInt + Movement.pawnDirection c) tgt hSq
  unfold Movement.isPawnAdvance
  refine ⟨?_, ?_, ?_⟩
  · intro hEq
    have hNe : Movement.pawnDirection c ≠ 0 := pawnDirection_ne_zero c
    have : tgt.rankInt = src.rankInt := by simpa [hEq] using congrArg Square.rankInt rfl
    -- `tgt.rankInt = src.rankInt + pawnDirection c`, so pawnDirection must be 0.
    have : src.rankInt + Movement.pawnDirection c = src.rankInt := by
      simpa [hRank] using this
    have : Movement.pawnDirection c = 0 := by
      have : src.rankInt + Movement.pawnDirection c = src.rankInt + 0 := by simpa using this
      exact Int.add_left_cancel this
    exact hNe this
  · unfold Movement.fileDiff
    simp [hFile]
  · left
    unfold Movement.rankDiff
    simp [hRank, Movement.pawnDirection]
    omega

theorem isPawnAdvance_of_twoStep
    (c : Color) (src tgt : Square)
    (hSq :
      Movement.squareFromInts src.fileInt (src.rankInt + 2 * Movement.pawnDirection c) = some tgt) :
    Movement.isPawnAdvance c src tgt := by
  have hFile :
      tgt.fileInt = src.fileInt :=
    Movement.squareFromInts_fileInt src.fileInt (src.rankInt + 2 * Movement.pawnDirection c) tgt hSq
  have hRank :
      tgt.rankInt = src.rankInt + 2 * Movement.pawnDirection c :=
    Movement.squareFromInts_rankInt src.fileInt (src.rankInt + 2 * Movement.pawnDirection c) tgt hSq
  unfold Movement.isPawnAdvance
  refine ⟨?_, ?_, ?_⟩
  · intro hEq
    have hNe : Movement.pawnDirection c ≠ 0 := pawnDirection_ne_zero c
    -- Same argument as one-step: nonzero rank change.
    have : tgt.rankInt = src.rankInt := by simpa [hEq] using congrArg Square.rankInt rfl
    have : src.rankInt + 2 * Movement.pawnDirection c = src.rankInt := by
      simpa [hRank] using this
    have : 2 * Movement.pawnDirection c = 0 := by
      have : src.rankInt + 2 * Movement.pawnDirection c = src.rankInt + 0 := by simpa using this
      exact Int.add_left_cancel this
    have : Movement.pawnDirection c = 0 := by
      -- In Int, `2 * x = 0` implies `x = 0`.
      omega
    exact hNe this
  · unfold Movement.fileDiff
    simp [hFile]
  · right
    unfold Movement.rankDiff
    simp [hRank]
    omega

theorem isPawnCapture_of_step
    (c : Color) (src tgt : Square) (df : Int)
    (hDf : df = -1 ∨ df = 1)
    (hSq :
      Movement.squareFromInts (src.fileInt + df) (src.rankInt + Movement.pawnDirection c) = some tgt) :
    Movement.isPawnCapture c src tgt := by
  have hFile :
      tgt.fileInt = src.fileInt + df :=
    Movement.squareFromInts_fileInt (src.fileInt + df) (src.rankInt + Movement.pawnDirection c) tgt hSq
  have hRank :
      tgt.rankInt = src.rankInt + Movement.pawnDirection c :=
    Movement.squareFromInts_rankInt (src.fileInt + df) (src.rankInt + Movement.pawnDirection c) tgt hSq
  unfold Movement.isPawnCapture
  refine ⟨?_, ?_, ?_⟩
  · intro hEq
    have hNe : df ≠ 0 := by
      rcases hDf with rfl | rfl <;> decide
    have : tgt.fileInt = src.fileInt := by simpa [hEq] using congrArg Square.fileInt rfl
    have : src.fileInt + df = src.fileInt := by
      simpa [hFile] using this
    have : df = 0 := by
      have : src.fileInt + df = src.fileInt + 0 := by simpa using this
      exact Int.add_left_cancel this
    exact hNe this
  · unfold Movement.fileDiff Movement.absInt
    -- `fileDiff = src.fileInt - tgt.fileInt = -df`.
    have hfd : src.fileInt - tgt.fileInt = -df := by
      simp [hFile]
      omega
    -- Reduce to the two cases df = ±1.
    rcases hDf with rfl | rfl <;> simp [hfd]
  · unfold Movement.rankDiff
    simp [hRank]
    omega

theorem promotionMoves_mem_preserves_squares (m base : Move) :
    m ∈ promotionMoves base →
      m.fromSq = base.fromSq ∧
        m.toSq = base.toSq ∧
        m.piece = base.piece ∧
        m.isCapture = base.isCapture ∧
        m.isEnPassant = base.isEnPassant := by
  intro hMem
  unfold promotionMoves at hMem
  by_cases hProm :
      base.piece.pieceType = PieceType.Pawn ∧
        base.toSq.rankNat = pawnPromotionRank base.piece.color
  · simp [hProm] at hMem
    rcases hMem with ⟨pt, _hPtMem, hEq⟩
    subst hEq
    simp
  · simp [hProm] at hMem
    subst hMem
    simp

end Rules
end Chess
