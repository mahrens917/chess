import Chess.KMinorBoard
import Chess.RulesComplete
import Chess.SemanticMoveFlagLemmas
import Chess.SemanticPromotionSoundnessLemmas

namespace Chess
namespace Rules

theorem KingsPlusMinor.mem_allLegalMoves_isCastle_false
    (gs : GameState) (m : Move) {wk bk msq : Square} {mp : Piece} :
    KingsPlusMinor gs.board wk bk msq mp →
    m ∈ allLegalMoves gs →
    m.isCastle = false := by
  intro hKPM hMem
  classical
  by_cases hCastle : m.isCastle = true
  · have hEnc : encodedLegal gs m :=
      (mem_allLegalMoves_iff_encodedLegal gs m).1 hMem
    rcases hEnc with ⟨src, p, hAtSrc, _hTurn, hTargets, _hPin, _hSafe⟩
    have hNoCastle : ∀ kingSide, castleMoveIfLegal gs kingSide = none :=
      KingsPlusMinor.castleMoveIfLegal_none (gs := gs) (wk := wk) (bk := bk) (msq := msq) (mp := mp) hKPM
    have hEx : ∃ kingSide, castleMoveIfLegal gs kingSide = some m :=
      Chess.Parsing.mem_pieceTargets_castle_exists gs src p m hTargets hCastle
    rcases hEx with ⟨kingSide, hSome⟩
    cases (show False by simpa [hNoCastle kingSide] using hSome)
  · simpa [Bool.not_eq_true] using hCastle

theorem KingsPlusMinor.mem_allLegalMoves_fromSq
    (gs : GameState) (m : Move) {wk bk msq : Square} {mp : Piece} :
    KingsPlusMinor gs.board wk bk msq mp →
    m ∈ allLegalMoves gs →
    m.fromSq = wk ∨ m.fromSq = bk ∨ m.fromSq = msq := by
  intro hKPM hMem
  have hEnc : encodedLegal gs m :=
    (mem_allLegalMoves_iff_encodedLegal gs m).1 hMem
  rcases hEnc with ⟨src, p, hAtSrc, _hTurn, hTargets, _hPin, _hSafe⟩
  have hAtSrc' : gs.board.get src = some p := by simpa using hAtSrc
  have hNoCastle : m.isCastle = false :=
    KingsPlusMinor.mem_allLegalMoves_isCastle_false (gs := gs) (m := m)
      (wk := wk) (bk := bk) (msq := msq) (mp := mp) hKPM hMem
  have hPieceFrom : m.piece = p ∧ m.fromSq = src :=
    Chess.Parsing.mem_pieceTargets_piece_fromSq_of_not_castle gs src p m hTargets hNoCastle
  have hSrcCases :=
    KingsPlusMinor.pieceType_cases (b := gs.board) (wk := wk) (bk := bk) (msq := msq) (mp := mp) hKPM src p hAtSrc'
  rcases hSrcCases with ⟨_hp, hs⟩ | ⟨_hp, hs⟩ | ⟨_hp, hs⟩
  · left
    simp [hPieceFrom.2, hs]
  · right; left
    simp [hPieceFrom.2, hs]
  · right; right
    simp [hPieceFrom.2, hs]

theorem KingsPlusMinor.mem_allLegalMoves_piece_cases
    (gs : GameState) (m : Move) {wk bk msq : Square} {mp : Piece} :
    KingsPlusMinor gs.board wk bk msq mp →
    m ∈ allLegalMoves gs →
    m.piece = kingPiece Color.White ∨ m.piece = kingPiece Color.Black ∨ m.piece = mp := by
  intro hKPM hMem
  have hEnc : encodedLegal gs m :=
    (mem_allLegalMoves_iff_encodedLegal gs m).1 hMem
  rcases hEnc with ⟨src, p, hAtSrc, _hTurn, hTargets, _hPin, _hSafe⟩
  have hAtSrc' : gs.board.get src = some p := by simpa using hAtSrc
  have hNoCastle : m.isCastle = false :=
    KingsPlusMinor.mem_allLegalMoves_isCastle_false (gs := gs) (m := m)
      (wk := wk) (bk := bk) (msq := msq) (mp := mp) hKPM hMem
  have hPieceFrom : m.piece = p ∧ m.fromSq = src :=
    Chess.Parsing.mem_pieceTargets_piece_fromSq_of_not_castle gs src p m hTargets hNoCastle
  have hSrcCases :=
    KingsPlusMinor.pieceType_cases (b := gs.board) (wk := wk) (bk := bk) (msq := msq) (mp := mp) hKPM src p hAtSrc'
  rcases hSrcCases with ⟨hp, _hs⟩ | ⟨hp, _hs⟩ | ⟨hp, _hs⟩
  · left
    simp [hPieceFrom.1, hp]
  · right; left
    simp [hPieceFrom.1, hp]
  · right; right
    simp [hPieceFrom.1, hp]

theorem KingsPlusMinor.mem_allLegalMoves_isEnPassant_false
    (gs : GameState) (m : Move) {wk bk msq : Square} {mp : Piece} :
    KingsPlusMinor gs.board wk bk msq mp →
    m ∈ allLegalMoves gs →
    m.isEnPassant = false := by
  intro hKPM hMem
  classical
  cases hEP : m.isEnPassant with
  | false =>
      rfl
  | true =>
      have hPawn : m.piece.pieceType = PieceType.Pawn :=
        mem_allLegalMoves_isEnPassant_implies_pawn (gs := gs) (m := m) hMem (by simp [hEP])
      have hPieceCases :
          m.piece = kingPiece Color.White ∨ m.piece = kingPiece Color.Black ∨ m.piece = mp :=
        KingsPlusMinor.mem_allLegalMoves_piece_cases (gs := gs) (m := m)
          (wk := wk) (bk := bk) (msq := msq) (mp := mp) hKPM hMem
      have hMinor : isMinorPieceType mp.pieceType := hKPM.2.2.2.1
      rcases hPieceCases with hW | hB | hM
      · have : (kingPiece Color.White).pieceType = PieceType.Pawn := by simpa [hW] using hPawn
        simp [kingPiece] at this
      · have : (kingPiece Color.Black).pieceType = PieceType.Pawn := by simpa [hB] using hPawn
        simp [kingPiece] at this
      · have : mp.pieceType = PieceType.Pawn := by simpa [hM] using hPawn
        rcases hMinor with hB | hN
        · simp [hB] at this
        · simp [hN] at this

theorem KingsPlusMinor.mem_allLegalMoves_promotion_none
    (gs : GameState) (m : Move) {wk bk msq : Square} {mp : Piece} :
    KingsPlusMinor gs.board wk bk msq mp →
    m ∈ allLegalMoves gs →
    m.promotion = none := by
  intro hKPM hMem
  classical
  cases hSome : m.promotion with
  | none =>
      rfl
  | some pt =>
      have hPawn : m.piece.pieceType = PieceType.Pawn :=
        (mem_allLegalMoves_promotion_isSome_implies_pawn_and_rank (gs := gs) (m := m) hMem (by
          simp [hSome])).1
      have hPieceCases :
          m.piece = kingPiece Color.White ∨ m.piece = kingPiece Color.Black ∨ m.piece = mp :=
        KingsPlusMinor.mem_allLegalMoves_piece_cases (gs := gs) (m := m)
          (wk := wk) (bk := bk) (msq := msq) (mp := mp) hKPM hMem
      have hMinor : isMinorPieceType mp.pieceType := hKPM.2.2.2.1
      have : False := by
        rcases hPieceCases with hW | hB | hM
        · have : (kingPiece Color.White).pieceType = PieceType.Pawn := by simpa [hW] using hPawn
          simp [kingPiece] at this
        · have : (kingPiece Color.Black).pieceType = PieceType.Pawn := by simpa [hB] using hPawn
          simp [kingPiece] at this
        · have : mp.pieceType = PieceType.Pawn := by simpa [hM] using hPawn
          rcases hMinor with hB | hN
          · simp [hB] at this
          · simp [hN] at this
      cases this

end Rules
end Chess
