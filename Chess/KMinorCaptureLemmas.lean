import Chess.KMinorSourceLemmas
import Chess.KMinorTransitionLemmas

namespace Chess
namespace Rules

private theorem mem_allLegalMoves_implies_captureFlagConsistent
    (gs : GameState) (m : Move) :
    m ∈ allLegalMoves gs → captureFlagConsistent gs m = true := by
  intro hMem
  have hBasic : basicMoveLegalBool gs m = true :=
    mem_allLegalMoves_implies_basicMoveLegalBool gs m hMem
  have hConj :
      (((originHasPiece gs m = true ∧ turnMatches gs m = true) ∧
            destinationFriendlyFree gs m = true) ∧
          captureFlagConsistent gs m = true) ∧
        squaresDiffer m = true := by
    simpa [basicMoveLegalBool, Bool.and_eq_true] using hBasic
  exact hConj.1.2

theorem KingsPlusMinor.mem_allLegalMoves_isCapture_implies_toSq_minorSquare
    (gs : GameState) (m : Move) {wk bk msq : Square} {mp : Piece} :
    KingsPlusMinor gs.board wk bk msq mp →
    m ∈ allLegalMoves gs →
    m.isCapture = true →
    m.toSq = msq := by
  intro hKPM hMem hCap
  have hCapCons : captureFlagConsistent gs m = true :=
    mem_allLegalMoves_implies_captureFlagConsistent (gs := gs) (m := m) hMem
  have hEP : m.isEnPassant = false :=
    KingsPlusMinor.mem_allLegalMoves_isEnPassant_false (gs := gs) (m := m)
      (wk := wk) (bk := bk) (msq := msq) (mp := mp) hKPM hMem
  -- With `isEnPassant = false`, `captureFlagConsistent = true` forces the target square to be occupied.
  have hOcc : ∃ p, gs.board.get m.toSq = some p := by
    unfold captureFlagConsistent at hCapCons
    simp [hEP] at hCapCons
    cases hAt : gs.board.get m.toSq with
    | none =>
        have : ¬m.isCapture = true := by simpa [hAt] using hCapCons
        cases (this hCap)
    | some p =>
        -- After `cases`, the goal is definitional.
        exact ⟨p, rfl⟩
  rcases hOcc with ⟨p, hAt⟩
  -- On kings+minor boards, the only occupied non-king destination is the minor square.
  have :=
    KingsPlusMinor.mem_allLegalMoves_destination_empty_or_minorSquare
      (gs := gs) (m := m) (wk := wk) (bk := bk) (msq := msq) (mp := mp) hKPM hMem
  cases this with
  | inl hEmpty =>
      have : (some p : Option Piece) = none := by
        simpa [hAt] using hEmpty
      cases this
  | inr hEq =>
      exact hEq

theorem KingsPlusMinor.mem_allLegalMoves_isCapture_implies_piece_is_opponentKing
    (gs : GameState) (m : Move) {wk bk msq : Square} {mp : Piece} :
    KingsPlusMinor gs.board wk bk msq mp →
    m ∈ allLegalMoves gs →
    m.isCapture = true →
    m.piece = kingPiece mp.color.opposite := by
  intro hKPM hMem hCap
  have hTo : m.toSq = msq :=
    KingsPlusMinor.mem_allLegalMoves_isCapture_implies_toSq_minorSquare
      (gs := gs) (m := m) (wk := wk) (bk := bk) (msq := msq) (mp := mp) hKPM hMem hCap
  have hDest : destinationFriendlyFree gs m = true :=
    mem_allLegalMoves_implies_destinationFriendlyFree gs m hMem
  have hAtMsq : gs.board.get msq = some mp := hKPM.2.2.1
  -- Destination is occupied by the minor.
  have hAt : gs.board.get m.toSq = some mp := by simpa [hTo] using hAtMsq
  -- Unpack `destinationFriendlyFree` to learn the mover's color is opposite the minor's color.
  have hDec :
      decide (mp.color ≠ m.piece.color ∧ mp.pieceType ≠ PieceType.King) = true := by
    unfold destinationFriendlyFree at hDest
    simpa [hAt] using hDest
  have hProp : mp.color ≠ m.piece.color ∧ mp.pieceType ≠ PieceType.King :=
    of_decide_eq_true hDec
  -- Now `m.piece` is one of {white king, black king, mp}; and cannot be `mp` (same color).
  have hPieceCases :
      m.piece = kingPiece Color.White ∨ m.piece = kingPiece Color.Black ∨ m.piece = mp :=
    KingsPlusMinor.mem_allLegalMoves_piece_cases (gs := gs) (m := m)
      (wk := wk) (bk := bk) (msq := msq) (mp := mp) hKPM hMem
  -- Split on the minor's color.
  cases hC : mp.color with
  | White =>
      have hNeed : m.piece = kingPiece Color.Black := by
        rcases hPieceCases with hW | hB | hM
        · -- mover is white king: impossible, same color as minor
          have : m.piece.color = Color.White := by simpa [hW, kingPiece] using rfl
          cases hProp.1 (by simpa [hC, this] using rfl)
        · exact hB
        · -- mover is mp: impossible, same color as minor
          have : m.piece.color = Color.White := by simpa [hM] using hC
          cases hProp.1 (by simpa [hC, this] using rfl)
      simp [Color.opposite, hC, hNeed]
  | Black =>
      have hNeed : m.piece = kingPiece Color.White := by
        rcases hPieceCases with hW | hB | hM
        · exact hW
        · -- mover is black king: impossible, same color as minor
          have : m.piece.color = Color.Black := by simpa [hB, kingPiece] using rfl
          cases hProp.1 (by simpa [hC, this] using rfl)
        · have : m.piece.color = Color.Black := by simpa [hM] using hC
          cases hProp.1 (by simpa [hC, this] using rfl)
      simp [Color.opposite, hC, hNeed]

theorem KingsPlusMinor.mem_allLegalMoves_isCapture_implies_fromSq_opponentKingSquare
    (gs : GameState) (m : Move) {wk bk msq : Square} {mp : Piece} :
    KingsPlusMinor gs.board wk bk msq mp →
    m ∈ allLegalMoves gs →
    m.isCapture = true →
    m.fromSq = (if mp.color = Color.White then bk else wk) := by
  intro hKPM hMem hCap
  have hPiece : m.piece = kingPiece mp.color.opposite :=
    KingsPlusMinor.mem_allLegalMoves_isCapture_implies_piece_is_opponentKing
      (gs := gs) (m := m) (wk := wk) (bk := bk) (msq := msq) (mp := mp) hKPM hMem hCap
  cases hC : mp.color with
  | White =>
      have : m.piece = kingPiece Color.Black := by simpa [hC, Color.opposite] using hPiece
      have hFrom : m.fromSq = bk :=
        KingsPlusMinor.mem_allLegalMoves_fromSq_eq_bk_of_piece_blackKing (gs := gs) (m := m)
          (wk := wk) (bk := bk) (msq := msq) (mp := mp) hKPM hMem this
      simpa [hC] using hFrom
  | Black =>
      have : m.piece = kingPiece Color.White := by simpa [hC, Color.opposite] using hPiece
      have hFrom : m.fromSq = wk :=
        KingsPlusMinor.mem_allLegalMoves_fromSq_eq_wk_of_piece_whiteKing (gs := gs) (m := m)
          (wk := wk) (bk := bk) (msq := msq) (mp := mp) hKPM hMem this
      simpa [hC] using hFrom

end Rules
end Chess
