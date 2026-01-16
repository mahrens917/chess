import Chess.CoreSoundnessLemmas
import Chess.SemanticCastlingLemmas
import Chess.SemanticMoveFlagLemmas
import Chess.SemanticNonCastleRookFieldLemmas
import Chess.SemanticPromotionSoundnessLemmas

namespace Chess
namespace Rules

theorem allLegalMoves_sound_fideLegalSemantic (gs : GameState) (m : Move) :
    hasValidEPRank gs →
    m ∈ allLegalMoves gs →
    fideLegalSemantic gs m := by
  intro hValid hMem
  have hCore := allLegalMoves_sound_fideLegalCore gs m hMem
  have hGeom : respectsGeometry gs m := allLegalMoves_sound_respectsGeometry gs m hMem
  have hCapEP : captureFlagConsistentWithEP gs m :=
    allLegalMoves_sound_captureFlagConsistentWithEP gs m hMem
  rcases hCore with ⟨hTurn, hFrom, hDestFree, hSafe⟩
  have hNotCheck : ¬(inCheck (simulateMove gs m).board gs.toMove) := by
    intro hChk
    have hTrue : inCheck (gs.movePiece m).board gs.toMove = true := by
      simpa using hChk
    have : (true : Bool) = false := by
      simpa [hTrue] using hSafe
    cases this
  have hPromoForward :
      (m.piece.pieceType = PieceType.Pawn ∧
            m.toSq.rankNat = pawnPromotionRank m.piece.color →
          m.promotion.isSome) := by
    intro h
    exact mem_allLegalMoves_pawn_toPromotionRank_implies_promotion_isSome
      gs m hValid hMem h.1 h.2
  have hPromoBackward :
      (m.promotion.isSome →
        m.piece.pieceType = PieceType.Pawn ∧
          m.toSq.rankNat = pawnPromotionRank m.piece.color ∧
            (∀ pt, m.promotion = some pt → pt ∈ promotionTargets)) := by
    intro hSome
    have hPawnRank :=
      mem_allLegalMoves_promotion_isSome_implies_pawn_and_rank gs m hMem hSome
    refine ⟨hPawnRank.1, hPawnRank.2, ?_⟩
    intro pt hEq
    have hNoCastle : m.isCastle = false := by
      cases hIs : m.isCastle with
      | false => simp [hIs]
      | true =>
          have hKing : m.piece.pieceType = PieceType.King :=
            mem_allLegalMoves_isCastle_implies_king gs m hMem (by simp [hIs])
          have : False := by
            have : (PieceType.Pawn : PieceType) = PieceType.King := by
              simpa [hPawnRank.1] using hKing.symm
            cases this
          cases this
    have hEnc : encodedLegal gs m :=
      (mem_allLegalMoves_iff_encodedLegal gs m).1 hMem
    rcases hEnc with ⟨sq, p, _hBoard, _hColor, hTargets, _hPin, _hSafe⟩
    have hPieceFrom : m.piece = p ∧ m.fromSq = sq :=
      Chess.Parsing.mem_pieceTargets_piece_fromSq_of_not_castle gs sq p m hTargets hNoCastle
    have hPawnP : p.pieceType = PieceType.Pawn := by
      simpa [hPieceFrom.1] using hPawnRank.1
    exact
      mem_pawn_pieceTargets_promotion_eq_some_implies_mem_promotionTargets gs sq p m pt hPawnP hTargets hEq
  have hCastleClause :
      (m.isCastle →
        ∃ kingSide : Bool,
          let cfg := castleConfig m.piece.color kingSide
          cfg.kingFrom = m.fromSq ∧
          cfg.kingTo = m.toSq ∧
          m.castleRookFrom = some cfg.rookFrom ∧
          m.castleRookTo = some cfg.rookTo ∧
          castleRight gs.castlingRights m.piece.color kingSide ∧
          gs.board cfg.kingFrom = some m.piece ∧
          (∃ rook : Piece,
            gs.board cfg.rookFrom = some rook ∧
            rook.pieceType = PieceType.Rook ∧ rook.color = m.piece.color) ∧
          cfg.emptySquares.all (isEmpty gs.board) ∧
          cfg.checkSquares.all (fun sq =>
            ¬(inCheck
                (gs.board.update cfg.kingFrom none |>.update sq (some m.piece))
                m.piece.color))) := by
    intro hCastle
    have hCastleEq : m.isCastle = true := by
      simpa using hCastle
    have hEnc : encodedLegal gs m :=
      (mem_allLegalMoves_iff_encodedLegal gs m).1 hMem
    rcases hEnc with ⟨sq, p, _hBoard, _hColor, hTargets, _hPin, _hSafe⟩
    have hEx : ∃ kingSide, castleMoveIfLegal gs kingSide = some m :=
      Chess.Parsing.mem_pieceTargets_castle_exists gs sq p m hTargets hCastleEq
    rcases hEx with ⟨kingSide, hCM⟩
    exact castleMoveIfLegal_implies_semantic_clause gs kingSide m hCM
  have hEPType : (m.isEnPassant → m.piece.pieceType = PieceType.Pawn) := by
    intro hEP
    have hEPEq : m.isEnPassant = true := by
      simpa using hEP
    exact mem_allLegalMoves_isEnPassant_implies_pawn gs m hMem hEPEq
  have hCastleType : (m.isCastle → m.piece.pieceType = PieceType.King) := by
    intro hCastle
    have hCastleEq : m.isCastle = true := by
      simpa using hCastle
    exact mem_allLegalMoves_isCastle_implies_king gs m hMem hCastleEq
  have hNonCastleRooks :
      (¬m.isCastle → m.castleRookFrom = none ∧ m.castleRookTo = none) := by
    intro hNoCastle
    exact mem_allLegalMoves_nonCastle_rookFields_none gs m hMem hNoCastle
  refine
    ⟨hTurn, hFrom, hGeom, hDestFree, hCapEP, hNotCheck, hPromoForward, hPromoBackward, hCastleClause,
      hEPType, hCastleType, hNonCastleRooks⟩

end Rules
end Chess
