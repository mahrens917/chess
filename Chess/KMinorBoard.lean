import Chess.AttackSpec
import Chess.BoardRoundtripProofs
import Chess.KkBoard
import Chess.KingSquareLemmas
import Chess.Movement

namespace Chess
namespace Rules

def isMinorPieceType (pt : PieceType) : Prop :=
  pt = PieceType.Bishop ∨ pt = PieceType.Knight

def isMinorPiece (p : Piece) : Prop :=
  isMinorPieceType p.pieceType

def kMinorBoard (wk bk msq : Square) (mp : Piece) : Board :=
  Board.fromList [(wk, kingPiece Color.White), (bk, kingPiece Color.Black), (msq, mp)]

def kMinorGameState (wk bk msq : Square) (mp : Piece) (toMove : Color) : GameState :=
  { (default : GameState) with
    board := kMinorBoard wk bk msq mp
    toMove := toMove
    castlingRights := noCastlingRights
    enPassantTarget := none
    history := []
    result := none }

/--
Board invariant: exactly two kings and exactly one minor piece.

This is intentionally “board-only”: it does not constrain clocks/history/result.
-/
def KingsPlusMinor (b : Board) (wk bk msq : Square) (mp : Piece) : Prop :=
  b.get wk = some (kingPiece Color.White) ∧
  b.get bk = some (kingPiece Color.Black) ∧
  b.get msq = some mp ∧
  isMinorPiece mp ∧
  wk ≠ bk ∧
  wk ≠ msq ∧
  bk ≠ msq ∧
  ∀ sq, sq ≠ wk → sq ≠ bk → sq ≠ msq → b.get sq = none

theorem KingsPlusMinor.white_unique {b : Board} {wk bk msq : Square} {mp : Piece} :
    KingsPlusMinor b wk bk msq mp →
    ∀ sq, b.get sq = some (kingPiece Color.White) → sq = wk := by
  intro h sq hAt
  rcases h with ⟨hWk, hBk, hMsq, hMinor, hWkNeBk, hWkNeMsq, hBkNeMsq, hOther⟩
  by_cases hEq : sq = wk
  · exact hEq
  · have hNeBk : sq ≠ bk := by
      intro hEqBk
      have hBlack : b.get sq = some (kingPiece Color.Black) := by
        simpa [hEqBk] using hBk
      have : some (kingPiece Color.White) = some (kingPiece Color.Black) :=
        Eq.trans hAt.symm hBlack
      cases Option.some.inj this
    have hNeMsq : sq ≠ msq := by
      intro hEqMsq
      have hMinorAt : b.get sq = some mp := by
        simpa [hEqMsq] using hMsq
      have : some (kingPiece Color.White) = some mp := Eq.trans hAt.symm hMinorAt
      have hEqPiece : kingPiece Color.White = mp := Option.some.inj this
      have : (kingPiece Color.White).pieceType = PieceType.King := by simp [kingPiece]
      have : mp.pieceType = PieceType.King := by simpa [hEqPiece] using this
      rcases hMinor with hMinor | hMinor <;> simp [isMinorPieceType, this] at hMinor
    have : b.get sq = none := hOther sq hEq hNeBk hNeMsq
    simp [this] at hAt

theorem KingsPlusMinor.black_unique {b : Board} {wk bk msq : Square} {mp : Piece} :
    KingsPlusMinor b wk bk msq mp →
    ∀ sq, b.get sq = some (kingPiece Color.Black) → sq = bk := by
  intro h sq hAt
  rcases h with ⟨hWk, hBk, hMsq, hMinor, hWkNeBk, hWkNeMsq, hBkNeMsq, hOther⟩
  by_cases hEq : sq = bk
  · exact hEq
  · have hNeWk : sq ≠ wk := by
      intro hEqWk
      have hWhite : b.get sq = some (kingPiece Color.White) := by
        simpa [hEqWk] using hWk
      have : some (kingPiece Color.Black) = some (kingPiece Color.White) :=
        Eq.trans hAt.symm hWhite
      cases Option.some.inj this
    have hNeMsq : sq ≠ msq := by
      intro hEqMsq
      have hMinorAt : b.get sq = some mp := by
        simpa [hEqMsq] using hMsq
      have : some (kingPiece Color.Black) = some mp := Eq.trans hAt.symm hMinorAt
      have hEqPiece : kingPiece Color.Black = mp := Option.some.inj this
      have : (kingPiece Color.Black).pieceType = PieceType.King := by simp [kingPiece]
      have : mp.pieceType = PieceType.King := by simpa [hEqPiece] using this
      rcases hMinor with hMinor | hMinor <;> simp [isMinorPieceType, this] at hMinor
    have : b.get sq = none := hOther sq hNeWk hEq hNeMsq
    simp [this] at hAt

theorem KingsPlusMinor.kingSquare_white {b : Board} {wk bk msq : Square} {mp : Piece} :
    KingsPlusMinor b wk bk msq mp →
    kingSquare b Color.White = some wk := by
  intro h
  refine kingSquare_eq_some_of_uniqueKing (b := b) (c := Color.White) (k := wk) ?_ ?_
  · exact h.1
  · intro sq hsq
    exact KingsPlusMinor.white_unique h sq (by simpa using hsq)

theorem KingsPlusMinor.kingSquare_black {b : Board} {wk bk msq : Square} {mp : Piece} :
    KingsPlusMinor b wk bk msq mp →
    kingSquare b Color.Black = some bk := by
  intro h
  refine kingSquare_eq_some_of_uniqueKing (b := b) (c := Color.Black) (k := bk) ?_ ?_
  · exact h.2.1
  · intro sq hsq
    exact KingsPlusMinor.black_unique h sq (by simpa using hsq)

theorem KingsPlusMinor.pieceType_cases {b : Board} {wk bk msq : Square} {mp : Piece} :
    KingsPlusMinor b wk bk msq mp →
    ∀ sq p, b.get sq = some p →
      (p = kingPiece Color.White ∧ sq = wk) ∨
      (p = kingPiece Color.Black ∧ sq = bk) ∨
      (p = mp ∧ sq = msq) := by
  intro h sq p hAt
  rcases h with ⟨hWk, hBk, hMsq, _hMinor, hWkNeBk, hWkNeMsq, hBkNeMsq, hOther⟩
  by_cases hSqWk : sq = wk
  · subst hSqWk
    left
    refine ⟨?_, rfl⟩
    have : some p = some (kingPiece Color.White) := Eq.trans hAt.symm hWk
    exact Option.some.inj this
  · by_cases hSqBk : sq = bk
    · subst hSqBk
      right; left
      refine ⟨?_, rfl⟩
      have : some p = some (kingPiece Color.Black) := Eq.trans hAt.symm hBk
      exact Option.some.inj this
    · by_cases hSqMsq : sq = msq
      · subst hSqMsq
        right; right
        refine ⟨?_, rfl⟩
        have : some p = some mp := Eq.trans hAt.symm hMsq
        exact Option.some.inj this
      · have : b.get sq = none := hOther sq hSqWk hSqBk hSqMsq
        simp [this] at hAt

theorem KingsPlusMinor.castleMoveIfLegal_none (gs : GameState) {wk bk msq : Square} {mp : Piece} :
    KingsPlusMinor gs.board wk bk msq mp →
    ∀ kingSide, castleMoveIfLegal gs kingSide = none := by
  intro h kingSide
  classical
  rcases h with ⟨hWk, hBk, hMsq, hMinor, hWkNeBk, hWkNeMsq, hBkNeMsq, hOther⟩
  have hInv : KingsPlusMinor gs.board wk bk msq mp :=
    ⟨hWk, hBk, hMsq, hMinor, hWkNeBk, hWkNeMsq, hBkNeMsq, hOther⟩
  unfold castleMoveIfLegal
  by_cases hRight : castleRight gs.castlingRights gs.toMove kingSide
  · simp [hRight]
    let cfg := castleConfig gs.toMove kingSide
    cases hKing : gs.board cfg.kingFrom <;> cases hRook : gs.board cfg.rookFrom <;> simp [cfg, hKing, hRook]
    · rename_i k r
      have hRookGet : gs.board.get cfg.rookFrom = some r := by simpa [cfg] using hRook
      have hCases :=
        KingsPlusMinor.pieceType_cases (b := gs.board) (wk := wk) (bk := bk) (msq := msq) (mp := mp) hInv
          cfg.rookFrom r hRookGet
      rcases hCases with ⟨hr, _⟩ | ⟨hr, _⟩ | ⟨hr, _⟩
      · subst hr; simp [kingPiece]
      · subst hr; simp [kingPiece]
      ·
        have hMinorR : isMinorPieceType r.pieceType := by
          -- `hMinor` is about `mp`; transport it across `r = mp`.
          have : isMinorPieceType mp.pieceType := hMinor
          simpa [hr] using this
        have hNotRook : r.pieceType ≠ PieceType.Rook := by
          intro hR
          rcases hMinorR with hB | hN
          · have : PieceType.Rook = PieceType.Bishop := by simpa [hR] using hB.symm
            cases this
          · have : PieceType.Rook = PieceType.Knight := by simpa [hR] using hN.symm
            cases this
        -- The rook-square content can't be a rook on a Kings+minor board.
        simp [hNotRook]
  · simp [hRight]

theorem KingsPlusMinor.inCheck_white_implies_minor_attacker
    {b : Board} {wk bk msq : Square} {mp : Piece}
    (h : KingsPlusMinor b wk bk msq mp)
    (hNoAdj : ¬ Movement.isKingStep wk bk) :
    inCheck b Color.White = true →
      mp.color = Color.Black ∧ attacksSpec b mp msq wk := by
  intro hChk
  have hKW : kingSquare b Color.White = some wk :=
    KingsPlusMinor.kingSquare_white (wk := wk) (bk := bk) (msq := msq) (mp := mp) h
  have :=
    (inCheck_eq_true_iff_exists_attacker b Color.White).1 hChk
  rcases this with ⟨kingSq, hKing, sq, p, _hSqMem, hAt, hColor, hAtk⟩
  have hk : kingSq = wk := by
    have : some wk = some kingSq := Eq.trans hKW.symm hKing
    exact (Option.some.inj this).symm
  cases hk
  have hAt' : b.get sq = some p := by simpa using hAt
  have hCases :=
    KingsPlusMinor.pieceType_cases (wk := wk) (bk := bk) (msq := msq) (mp := mp) h sq p hAt'
  rcases hCases with ⟨hp, hs⟩ | ⟨hp, hs⟩ | ⟨hp, hs⟩
  · cases hp
    have : Color.White = Color.Black := by
      simpa [kingPiece, Color.opposite] using hColor
    cases this
  · cases hp
    cases hs
    have : Movement.isKingStep bk wk := by
      simpa [attacksSpec, kingPiece] using hAtk
    exact (hNoAdj (Movement.isKingStep_symm bk wk this)).elim
  · cases hp
    cases hs
    refine ⟨?_, ?_⟩
    · exact hColor
    · simpa using hAtk

theorem KingsPlusMinor.inCheck_black_implies_minor_attacker
    {b : Board} {wk bk msq : Square} {mp : Piece}
    (h : KingsPlusMinor b wk bk msq mp)
    (hNoAdj : ¬ Movement.isKingStep wk bk) :
    inCheck b Color.Black = true →
      mp.color = Color.White ∧ attacksSpec b mp msq bk := by
  intro hChk
  have hKB : kingSquare b Color.Black = some bk :=
    KingsPlusMinor.kingSquare_black (wk := wk) (bk := bk) (msq := msq) (mp := mp) h
  have :=
    (inCheck_eq_true_iff_exists_attacker b Color.Black).1 hChk
  rcases this with ⟨kingSq, hKing, sq, p, _hSqMem, hAt, hColor, hAtk⟩
  have hk : kingSq = bk := by
    have : some bk = some kingSq := Eq.trans hKB.symm hKing
    exact (Option.some.inj this).symm
  cases hk
  have hAt' : b.get sq = some p := by simpa using hAt
  have hCases :=
    KingsPlusMinor.pieceType_cases (wk := wk) (bk := bk) (msq := msq) (mp := mp) h sq p hAt'
  rcases hCases with ⟨hp, hs⟩ | ⟨hp, hs⟩ | ⟨hp, hs⟩
  · cases hp
    cases hs
    have : Movement.isKingStep wk bk := by
      simpa [attacksSpec, kingPiece] using hAtk
    exact (hNoAdj this).elim
  · cases hp
    have : Color.Black = Color.White := by
      simpa [kingPiece, Color.opposite] using hColor
    cases this
  · cases hp
    cases hs
    refine ⟨?_, ?_⟩
    · exact hColor
    · simpa using hAtk

theorem KingsPlusMinor.inCheck_white_of_isKingStep
    {b : Board} {wk bk msq : Square} {mp : Piece}
    (h : KingsPlusMinor b wk bk msq mp) :
    Movement.isKingStep bk wk → inCheck b Color.White = true := by
  intro hStep
  have hKW : kingSquare b Color.White = some wk :=
    KingsPlusMinor.kingSquare_white (wk := wk) (bk := bk) (msq := msq) (mp := mp) h
  -- Use the attacker-exists characterization with the black king as attacker.
  refine (inCheck_eq_true_iff_exists_attacker b Color.White).2 ?_
  refine ⟨wk, hKW, ?_⟩
  refine ⟨bk, kingPiece Color.Black, ?_, ?_, ?_, ?_⟩
  · exact Square.mem_all bk
  · -- black king is at `bk`
    have : b.get bk = some (kingPiece Color.Black) := h.2.1
    simpa using this
  · simp [kingPiece, Color.opposite]
  · simpa [attacksSpec, kingPiece] using hStep

theorem KingsPlusMinor.inCheck_black_of_isKingStep
    {b : Board} {wk bk msq : Square} {mp : Piece}
    (h : KingsPlusMinor b wk bk msq mp) :
    Movement.isKingStep wk bk → inCheck b Color.Black = true := by
  intro hStep
  have hKB : kingSquare b Color.Black = some bk :=
    KingsPlusMinor.kingSquare_black (wk := wk) (bk := bk) (msq := msq) (mp := mp) h
  refine (inCheck_eq_true_iff_exists_attacker b Color.Black).2 ?_
  refine ⟨bk, hKB, ?_⟩
  refine ⟨wk, kingPiece Color.White, ?_, ?_, ?_, ?_⟩
  · exact Square.mem_all wk
  · have : b.get wk = some (kingPiece Color.White) := h.1
    simpa using this
  · simp [kingPiece, Color.opposite]
  · simpa [attacksSpec, kingPiece] using hStep

end Rules
end Chess
