import Chess.Rules

namespace Chess
namespace Rules

theorem promotionMoves_mem_promotion_isSome_iff (m base : Move) (hBase : base.promotion = none) :
    m ∈ promotionMoves base →
      (m.promotion.isSome = true ↔
        (base.piece.pieceType = PieceType.Pawn ∧
          base.toSq.rankNat = pawnPromotionRank base.piece.color)) := by
  intro hMem
  unfold promotionMoves at hMem
  by_cases hProm :
      base.piece.pieceType = PieceType.Pawn ∧
        base.toSq.rankNat = pawnPromotionRank base.piece.color
  · simp [hProm] at hMem
    rcases hMem with ⟨pt, _hPtMem, hEq⟩
    subst hEq
    simp [hProm]
  · simp [hProm] at hMem
    subst hMem
    simp [hProm, hBase]

theorem promotionMoves_mem_promotion_isSome (m base : Move) (hBase : base.promotion = none) :
    m ∈ promotionMoves base →
    m.promotion.isSome = true →
    base.piece.pieceType = PieceType.Pawn ∧
      base.toSq.rankNat = pawnPromotionRank base.piece.color := by
  intro hMem hSome
  have := (promotionMoves_mem_promotion_isSome_iff m base hBase hMem).1 hSome
  exact this

theorem promotionMoves_mem_promotion_if_at_rank (m base : Move) (hBase : base.promotion = none)
    (hPawn : base.piece.pieceType = PieceType.Pawn)
    (hRank : base.toSq.rankNat = pawnPromotionRank base.piece.color) :
    m ∈ promotionMoves base →
    m.promotion.isSome = true := by
  intro hMem
  have : base.piece.pieceType = PieceType.Pawn ∧
      base.toSq.rankNat = pawnPromotionRank base.piece.color := ⟨hPawn, hRank⟩
  exact (promotionMoves_mem_promotion_isSome_iff m base hBase hMem).2 this

theorem mem_promotionMoves_of_mem_promotionTargets (base : Move) (pt : PieceType)
    (hPawn : base.piece.pieceType = PieceType.Pawn)
    (hRank : base.toSq.rankNat = pawnPromotionRank base.piece.color)
    (hPt : pt ∈ promotionTargets) :
    ({ base with promotion := some pt } : Move) ∈ promotionMoves base := by
  unfold promotionMoves
  have hCond :
      base.piece.pieceType = PieceType.Pawn ∧
        base.toSq.rankNat = pawnPromotionRank base.piece.color := ⟨hPawn, hRank⟩
  simpa [hCond] using hPt

end Rules
end Chess
