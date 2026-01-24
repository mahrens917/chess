import Init.Omega
import Chess.PathValidationProofs
import Chess.SemanticPromotionLemmas

namespace Chess
namespace Rules

open Movement

-- TODO: These proofs need omega fixes for current Lean 4 version.

theorem pawnDirection_ne_zero (c : Color) : Movement.pawnDirection c ≠ 0 := by
  cases c <;> simp [Movement.pawnDirection]

theorem isPawnAdvance_of_oneStep
    (c : Color) (src tgt : Square)
    (hSq :
      Movement.squareFromInts src.fileInt (src.rankInt + Movement.pawnDirection c) = some tgt) :
    Movement.isPawnAdvance c src tgt := by
  -- Extract coordinates from squareFromInts
  have hFile := Movement.squareFromInts_fileInt src.fileInt (src.rankInt + Movement.pawnDirection c) tgt hSq
  have hRank := Movement.squareFromInts_rankInt src.fileInt (src.rankInt + Movement.pawnDirection c) tgt hSq
  unfold Movement.isPawnAdvance Movement.fileDiff Movement.rankDiff
  constructor
  · -- src ≠ tgt (ranks differ by pawnDirection c ≠ 0)
    intro heq
    rw [heq] at hRank
    have hpd := pawnDirection_ne_zero c
    omega
  constructor
  · -- fileDiff = 0
    omega
  · -- rankDiff = -pawnDirection c
    left
    omega

theorem isPawnAdvance_of_twoStep
    (c : Color) (src tgt : Square)
    (hStart : src.rankNat = pawnStartRank c)
    (hSq :
      Movement.squareFromInts src.fileInt (src.rankInt + 2 * Movement.pawnDirection c) = some tgt) :
    Movement.isPawnAdvance c src tgt := by
  -- Extract coordinates from squareFromInts
  have hFile := Movement.squareFromInts_fileInt src.fileInt (src.rankInt + 2 * Movement.pawnDirection c) tgt hSq
  have hRank := Movement.squareFromInts_rankInt src.fileInt (src.rankInt + 2 * Movement.pawnDirection c) tgt hSq
  unfold Movement.isPawnAdvance Movement.fileDiff Movement.rankDiff
  constructor
  · -- src ≠ tgt (ranks differ by 2*pawnDirection c ≠ 0)
    intro heq
    rw [heq] at hRank
    have hpd := pawnDirection_ne_zero c
    have : 2 * Movement.pawnDirection c ≠ 0 := by
      cases c <;> simp [Movement.pawnDirection]
    omega
  constructor
  · -- fileDiff = 0
    omega
  · -- rankDiff = -2*pawnDirection c
    right
    omega

theorem isPawnCapture_of_step
    (c : Color) (src tgt : Square) (df : Int) (hdf : df = 1 ∨ df = -1)
    (hSq :
      Movement.squareFromInts (src.fileInt + df) (src.rankInt + Movement.pawnDirection c) = some tgt) :
    Movement.isPawnCapture c src tgt := by
  -- Extract coordinates from squareFromInts
  have hFile := Movement.squareFromInts_fileInt (src.fileInt + df) (src.rankInt + Movement.pawnDirection c) tgt hSq
  have hRank := Movement.squareFromInts_rankInt (src.fileInt + df) (src.rankInt + Movement.pawnDirection c) tgt hSq
  unfold Movement.isPawnCapture Movement.fileDiff Movement.rankDiff Movement.absInt
  constructor
  · -- src ≠ tgt (files or ranks differ)
    intro heq
    rw [heq] at hFile
    rcases hdf with hdf1 | hdfm1 <;> omega
  constructor
  · -- absInt (fileDiff) = 1
    -- fileDiff = src.fileInt - tgt.fileInt = src.fileInt - (src.fileInt + df) = -df
    -- absInt (-df) = absInt df = 1 since df = 1 or df = -1
    rcases hdf with hdf1 | hdfm1 <;> omega
  · -- rankDiff = -pawnDirection c
    omega

theorem promotionMoves_mem_preserves_squares (m base : Move) :
    m ∈ Rules.promotionMoves base →
    m.fromSq = base.fromSq ∧ m.toSq = base.toSq := by
  intro hmem
  unfold Rules.promotionMoves at hmem
  split at hmem
  · -- Promotion case: m ∈ promotionTargets.map (fun pt => { base with promotion := some pt })
    simp only [List.mem_map] at hmem
    obtain ⟨pt, _, hm⟩ := hmem
    rw [← hm]
    exact ⟨rfl, rfl⟩
  · -- Non-promotion case: m ∈ [base]
    simp only [List.mem_singleton] at hmem
    rw [hmem]
    exact ⟨rfl, rfl⟩

end Rules
end Chess
