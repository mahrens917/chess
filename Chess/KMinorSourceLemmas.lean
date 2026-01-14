import Chess.KMinorMoveLemmas

namespace Chess
namespace Rules

theorem KingsPlusMinor.mem_allLegalMoves_fromSq_eq_wk_of_piece_whiteKing
    (gs : GameState) (m : Move) {wk bk msq : Square} {mp : Piece} :
    KingsPlusMinor gs.board wk bk msq mp →
    m ∈ allLegalMoves gs →
    m.piece = kingPiece Color.White →
    m.fromSq = wk := by
  intro hKPM hMem hPiece
  have hEnc : encodedLegal gs m :=
    (mem_allLegalMoves_iff_encodedLegal gs m).1 hMem
  rcases hEnc with ⟨src, p, hAtSrc, _hTurn, hTargets, _hPin, _hSafe⟩
  have hAtSrc' : gs.board.get src = some p := by simpa using hAtSrc
  have hNoCastle : m.isCastle = false :=
    KingsPlusMinor.mem_allLegalMoves_isCastle_false (gs := gs) (m := m)
      (wk := wk) (bk := bk) (msq := msq) (mp := mp) hKPM hMem
  have hPieceFrom : m.piece = p ∧ m.fromSq = src :=
    Chess.Parsing.mem_pieceTargets_piece_fromSq_of_not_castle gs src p m hTargets hNoCastle
  have hp : p = kingPiece Color.White := by
    simpa [hPieceFrom.1] using hPiece
  have hSrcCases :=
    KingsPlusMinor.pieceType_cases (b := gs.board) (wk := wk) (bk := bk) (msq := msq) (mp := mp) hKPM src p hAtSrc'
  rcases hSrcCases with ⟨hp', hs⟩ | ⟨hp', hs⟩ | ⟨hp', hs⟩
  · -- src has the white king
    have : m.fromSq = src := hPieceFrom.2
    simpa [hs] using this
  · -- src has the black king: contradict `p = white king`
    have : kingPiece Color.Black = kingPiece Color.White := by
      simpa [hp] using hp'.symm
    cases this
  · -- src has the minor: contradict that `mp` is minor
    have hMinor : isMinorPieceType mp.pieceType := by
      simpa [isMinorPiece] using hKPM.2.2.2.1
    have hEq : mp = kingPiece Color.White := by
      simpa [hp'] using hp
    have : mp.pieceType = PieceType.King := by
      simpa [hEq, kingPiece] using (rfl : (kingPiece Color.White).pieceType = PieceType.King)
    rcases hMinor with hB | hN
    · simp [hB] at this
    · simp [hN] at this

theorem KingsPlusMinor.mem_allLegalMoves_fromSq_eq_bk_of_piece_blackKing
    (gs : GameState) (m : Move) {wk bk msq : Square} {mp : Piece} :
    KingsPlusMinor gs.board wk bk msq mp →
    m ∈ allLegalMoves gs →
    m.piece = kingPiece Color.Black →
    m.fromSq = bk := by
  intro hKPM hMem hPiece
  have hEnc : encodedLegal gs m :=
    (mem_allLegalMoves_iff_encodedLegal gs m).1 hMem
  rcases hEnc with ⟨src, p, hAtSrc, _hTurn, hTargets, _hPin, _hSafe⟩
  have hAtSrc' : gs.board.get src = some p := by simpa using hAtSrc
  have hNoCastle : m.isCastle = false :=
    KingsPlusMinor.mem_allLegalMoves_isCastle_false (gs := gs) (m := m)
      (wk := wk) (bk := bk) (msq := msq) (mp := mp) hKPM hMem
  have hPieceFrom : m.piece = p ∧ m.fromSq = src :=
    Chess.Parsing.mem_pieceTargets_piece_fromSq_of_not_castle gs src p m hTargets hNoCastle
  have hp : p = kingPiece Color.Black := by
    simpa [hPieceFrom.1] using hPiece
  have hSrcCases :=
    KingsPlusMinor.pieceType_cases (b := gs.board) (wk := wk) (bk := bk) (msq := msq) (mp := mp) hKPM src p hAtSrc'
  rcases hSrcCases with ⟨hp', hs⟩ | ⟨hp', hs⟩ | ⟨hp', hs⟩
  · have : kingPiece Color.White = kingPiece Color.Black := by
      simpa [hp] using hp'.symm
    cases this
  · have : m.fromSq = src := hPieceFrom.2
    simpa [hs] using this
  · have hMinor : isMinorPieceType mp.pieceType := by
      simpa [isMinorPiece] using hKPM.2.2.2.1
    have hEq : mp = kingPiece Color.Black := by
      simpa [hp'] using hp
    have : mp.pieceType = PieceType.King := by
      simpa [hEq, kingPiece] using (rfl : (kingPiece Color.Black).pieceType = PieceType.King)
    rcases hMinor with hB | hN
    · simp [hB] at this
    · simp [hN] at this

theorem KingsPlusMinor.mem_allLegalMoves_fromSq_eq_msq_of_piece_minor
    (gs : GameState) (m : Move) {wk bk msq : Square} {mp : Piece} :
    KingsPlusMinor gs.board wk bk msq mp →
    m ∈ allLegalMoves gs →
    m.piece = mp →
    m.fromSq = msq := by
  intro hKPM hMem hPiece
  have hEnc : encodedLegal gs m :=
    (mem_allLegalMoves_iff_encodedLegal gs m).1 hMem
  rcases hEnc with ⟨src, p, hAtSrc, _hTurn, hTargets, _hPin, _hSafe⟩
  have hAtSrc' : gs.board.get src = some p := by simpa using hAtSrc
  have hNoCastle : m.isCastle = false :=
    KingsPlusMinor.mem_allLegalMoves_isCastle_false (gs := gs) (m := m)
      (wk := wk) (bk := bk) (msq := msq) (mp := mp) hKPM hMem
  have hPieceFrom : m.piece = p ∧ m.fromSq = src :=
    Chess.Parsing.mem_pieceTargets_piece_fromSq_of_not_castle gs src p m hTargets hNoCastle
  have hp : p = mp := by
    exact Eq.trans hPieceFrom.1.symm hPiece
  have hSrcCases :=
    KingsPlusMinor.pieceType_cases (b := gs.board) (wk := wk) (bk := bk) (msq := msq) (mp := mp) hKPM src p hAtSrc'
  rcases hSrcCases with ⟨hp', hs⟩ | ⟨hp', hs⟩ | ⟨hp', hs⟩
  · have hMinor : isMinorPieceType mp.pieceType := by
      simpa [isMinorPiece] using hKPM.2.2.2.1
    have : mp.pieceType = PieceType.King := by
      have : mp = kingPiece Color.White := by simpa [hp] using hp'
      simpa [this, kingPiece] using (rfl : (kingPiece Color.White).pieceType = PieceType.King)
    rcases hMinor with hB | hN
    · simp [hB] at this
    · simp [hN] at this
  · have hMinor : isMinorPieceType mp.pieceType := by
      simpa [isMinorPiece] using hKPM.2.2.2.1
    have : mp.pieceType = PieceType.King := by
      have : mp = kingPiece Color.Black := by simpa [hp] using hp'
      simpa [this, kingPiece] using (rfl : (kingPiece Color.Black).pieceType = PieceType.King)
    rcases hMinor with hB | hN
    · simp [hB] at this
    · simp [hN] at this
  · have : m.fromSq = src := hPieceFrom.2
    simpa [hs] using this

end Rules
end Chess
