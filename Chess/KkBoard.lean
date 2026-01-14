import Chess.AttackSpec
import Chess.BoardRoundtripProofs
import Chess.KingSquareLemmas
import Chess.Movement

namespace Chess
namespace Rules

def noCastlingRights : CastlingRights :=
  { whiteKingSide := false
    whiteQueenSide := false
    blackKingSide := false
    blackQueenSide := false }

def kkBoard (wk bk : Square) : Board :=
  Board.fromList [(wk, kingPiece Color.White), (bk, kingPiece Color.Black)]

def kkGameState (wk bk : Square) (toMove : Color) : GameState :=
  { (default : GameState) with
    board := kkBoard wk bk
    toMove := toMove
    castlingRights := noCastlingRights
    enPassantTarget := none
    history := []
    result := none }

def KingsOnly (b : Board) (wk bk : Square) : Prop :=
  b.get wk = some (kingPiece Color.White) ∧
  b.get bk = some (kingPiece Color.Black) ∧
  wk ≠ bk ∧
  ∀ sq, sq ≠ wk → sq ≠ bk → b.get sq = none

theorem kkBoard_get_whiteKing (wk bk : Square) (hNe : wk ≠ bk) :
    (kkBoard wk bk).get wk = some (kingPiece Color.White) := by
  classical
  have hMem : (wk, kingPiece Color.White) ∈
      [(wk, kingPiece Color.White), (bk, kingPiece Color.Black)] := by
    simp
  have hUniq :
      ∀ q, (wk, q) ∈ [(wk, kingPiece Color.White), (bk, kingPiece Color.Black)] →
        q = kingPiece Color.White := by
    intro q hq
    simp at hq
    rcases hq with hq | hq
    · exact hq
    · exact (hNe hq.1).elim
  simpa [kkBoard] using
    Board.fromList_get_eq_some_of_mem_unique
      [(wk, kingPiece Color.White), (bk, kingPiece Color.Black)]
      wk (kingPiece Color.White) hMem hUniq

theorem kkBoard_get_blackKing (wk bk : Square) (hNe : wk ≠ bk) :
    (kkBoard wk bk).get bk = some (kingPiece Color.Black) := by
  classical
  have hMem : (bk, kingPiece Color.Black) ∈
      [(wk, kingPiece Color.White), (bk, kingPiece Color.Black)] := by
    simp
  have hUniq :
      ∀ q, (bk, q) ∈ [(wk, kingPiece Color.White), (bk, kingPiece Color.Black)] →
        q = kingPiece Color.Black := by
    intro q hq
    simp at hq
    rcases hq with hq | hq
    · exact (hNe hq.1.symm).elim
    · exact hq
  simpa [kkBoard] using
    Board.fromList_get_eq_some_of_mem_unique
      [(wk, kingPiece Color.White), (bk, kingPiece Color.Black)]
      bk (kingPiece Color.Black) hMem hUniq

theorem kkBoard_get_other (wk bk sq : Square) (hw : sq ≠ wk) (hb : sq ≠ bk) :
    (kkBoard wk bk).get sq = none := by
  classical
  have hne :
      ∀ e ∈ [(wk, kingPiece Color.White), (bk, kingPiece Color.Black)], e.fst ≠ sq := by
    intro e he
    simp at he
    rcases he with he | he
    · simpa [he] using hw.symm
    · simpa [he] using hb.symm
  simpa [kkBoard] using
    Board.fromList_get_eq_none_of_forall_ne
      [(wk, kingPiece Color.White), (bk, kingPiece Color.Black)]
      sq hne

theorem kingsOnly_kkBoard (wk bk : Square) (hNe : wk ≠ bk) :
    KingsOnly (kkBoard wk bk) wk bk := by
  refine ⟨kkBoard_get_whiteKing wk bk hNe, kkBoard_get_blackKing wk bk hNe, hNe, ?_⟩
  intro sq hw hb
  exact kkBoard_get_other wk bk sq hw hb

theorem KingsOnly.white_unique {b : Board} {wk bk : Square} :
    KingsOnly b wk bk →
    ∀ sq, b.get sq = some (kingPiece Color.White) → sq = wk := by
  intro h sq hAt
  rcases h with ⟨hWk, hBk, hNe, hOther⟩
  by_cases hEq : sq = wk
  · exact hEq
  · have hNeBk : sq ≠ bk := by
      intro hEqBk
      have hBlack : b.get sq = some (kingPiece Color.Black) := by
        simpa [hEqBk] using hBk
      have : some (kingPiece Color.White) = some (kingPiece Color.Black) :=
        Eq.trans hAt.symm hBlack
      cases Option.some.inj this
    have : b.get sq = none := hOther sq hEq hNeBk
    simp [this] at hAt

theorem KingsOnly.black_unique {b : Board} {wk bk : Square} :
    KingsOnly b wk bk →
    ∀ sq, b.get sq = some (kingPiece Color.Black) → sq = bk := by
  intro h sq hAt
  rcases h with ⟨hWk, hBk, hNe, hOther⟩
  by_cases hEq : sq = bk
  · exact hEq
  · have hNeWk : sq ≠ wk := by
      intro hEqWk
      have hWhite : b.get sq = some (kingPiece Color.White) := by
        simpa [hEqWk] using hWk
      have : some (kingPiece Color.Black) = some (kingPiece Color.White) :=
        Eq.trans hAt.symm hWhite
      cases Option.some.inj this
    have : b.get sq = none := hOther sq hNeWk hEq
    simp [this] at hAt

theorem KingsOnly.kingSquare_white {b : Board} {wk bk : Square} :
    KingsOnly b wk bk →
    kingSquare b Color.White = some wk := by
  intro h
  refine kingSquare_eq_some_of_uniqueKing (b := b) (c := Color.White) (k := wk) ?_ ?_
  · exact h.1
  · intro sq hsq
    exact KingsOnly.white_unique h sq (by simpa using hsq)

theorem KingsOnly.kingSquare_black {b : Board} {wk bk : Square} :
    KingsOnly b wk bk →
    kingSquare b Color.Black = some bk := by
  intro h
  refine kingSquare_eq_some_of_uniqueKing (b := b) (c := Color.Black) (k := bk) ?_ ?_
  · exact h.2.1
  · intro sq hsq
    exact KingsOnly.black_unique h sq (by simpa using hsq)

theorem KingsOnly.black_piece_of_get_of_color {b : Board} {wk bk : Square} :
    KingsOnly b wk bk →
    ∀ sq p, b.get sq = some p → p.color = Color.Black → sq = bk ∧ p = kingPiece Color.Black := by
  intro h sq p hAt hColor
  rcases h with ⟨hWk, hBk, hNe, hOther⟩
  by_cases hSqBk : sq = bk
  · subst hSqBk
    refine ⟨rfl, ?_⟩
    have : some p = some (kingPiece Color.Black) := Eq.trans hAt.symm hBk
    exact Option.some.inj this
  · by_cases hSqWk : sq = wk
    · subst hSqWk
      have : some p = some (kingPiece Color.White) := Eq.trans hAt.symm hWk
      have hp : p = kingPiece Color.White := Option.some.inj this
      subst hp
      simp [kingPiece] at hColor
    · have : b.get sq = none := hOther sq hSqWk hSqBk
      simp [this] at hAt

theorem KingsOnly.white_piece_of_get_of_color {b : Board} {wk bk : Square} :
    KingsOnly b wk bk →
    ∀ sq p, b.get sq = some p → p.color = Color.White → sq = wk ∧ p = kingPiece Color.White := by
  intro h sq p hAt hColor
  rcases h with ⟨hWk, hBk, hNe, hOther⟩
  by_cases hSqWk : sq = wk
  · subst hSqWk
    refine ⟨rfl, ?_⟩
    have : some p = some (kingPiece Color.White) := Eq.trans hAt.symm hWk
    exact Option.some.inj this
  · by_cases hSqBk : sq = bk
    · subst hSqBk
      have : some p = some (kingPiece Color.Black) := Eq.trans hAt.symm hBk
      have hp : p = kingPiece Color.Black := Option.some.inj this
      subst hp
      simp [kingPiece] at hColor
    · have : b.get sq = none := hOther sq hSqWk hSqBk
      simp [this] at hAt

theorem KingsOnly.pieceType_eq_king {b : Board} {wk bk : Square} :
    KingsOnly b wk bk →
    ∀ sq p, b.get sq = some p → p.pieceType = PieceType.King := by
  intro h sq p hAt
  by_cases hSqWk : sq = wk
  · subst hSqWk
    have : some p = some (kingPiece Color.White) := Eq.trans hAt.symm h.1
    have hp : p = kingPiece Color.White := Option.some.inj this
    subst hp
    simp [kingPiece]
  · by_cases hSqBk : sq = bk
    · subst hSqBk
      have : some p = some (kingPiece Color.Black) := Eq.trans hAt.symm h.2.1
      have hp : p = kingPiece Color.Black := Option.some.inj this
      subst hp
      simp [kingPiece]
    · have : b.get sq = none := h.2.2.2 sq hSqWk hSqBk
      simp [this] at hAt

theorem KingsOnly.castleMoveIfLegal_none (gs : GameState) {wk bk : Square} :
    KingsOnly gs.board wk bk →
    ∀ kingSide, castleMoveIfLegal gs kingSide = none := by
  intro h kingSide
  classical
  unfold castleMoveIfLegal
  -- If castling rights are absent, we're done.
  by_cases hRight : castleRight gs.castlingRights gs.toMove kingSide
  · simp [hRight]
    -- Otherwise, the rook check fails because a KingsOnly board contains no rooks.
    let cfg := castleConfig gs.toMove kingSide
    cases hKing : gs.board cfg.kingFrom <;> cases hRook : gs.board cfg.rookFrom <;> simp [cfg, hKing, hRook]
    · -- Both squares are occupied, but the rook square cannot contain a rook.
      rename_i k r
      have hRookGet : gs.board.get cfg.rookFrom = some r := by simpa [cfg] using hRook
      have hPt : r.pieceType = PieceType.King :=
        KingsOnly.pieceType_eq_king (b := gs.board) (wk := wk) (bk := bk) h cfg.rookFrom r hRookGet
      simp [hPt]
  · simp [hRight]

theorem KingsOnly.inCheck_white_eq_true_iff_isKingStep {b : Board} {wk bk : Square}
    (h : KingsOnly b wk bk) :
    inCheck b Color.White = true ↔ Movement.isKingStep bk wk := by
  have hK : kingSquare b Color.White = some wk := KingsOnly.kingSquare_white h
  constructor
  · intro hChk
    have :=
      (inCheck_eq_true_iff_exists_attacker b Color.White).1 hChk
    rcases this with ⟨kingSq, hKing, sq, p, _hSqMem, hAt, hColor, hAtk⟩
    have hk : kingSq = wk := by
      have : some wk = some kingSq := Eq.trans hK.symm hKing
      exact (Option.some.inj this).symm
    subst hk
    have hAt' : b.get sq = some p := by simpa using hAt
    have ⟨hsq, hp⟩ := KingsOnly.black_piece_of_get_of_color h sq p hAt' hColor
    subst hsq
    subst hp
    simpa [attacksSpec, kingPiece] using hAtk
  · intro hStep
    have hEx :
        ∃ kingSq,
          kingSquare b Color.White = some kingSq ∧
          (∃ sq p,
            sq ∈ allSquares ∧
            b sq = some p ∧
            p.color = Color.Black ∧
            attacksSpec b p sq kingSq) := by
      refine ⟨wk, hK, ?_⟩
      refine ⟨bk, kingPiece Color.Black, Square.mem_all bk, ?_, rfl, ?_⟩
      · simpa using h.2.1
      · simpa [attacksSpec, kingPiece] using hStep
    exact (inCheck_eq_true_iff_exists_attacker b Color.White).2 hEx

theorem KingsOnly.inCheck_black_eq_true_iff_isKingStep {b : Board} {wk bk : Square}
    (h : KingsOnly b wk bk) :
    inCheck b Color.Black = true ↔ Movement.isKingStep wk bk := by
  -- Symmetric to the white case.
  have hK : kingSquare b Color.Black = some bk := KingsOnly.kingSquare_black h
  constructor
  · intro hChk
    have :=
      (inCheck_eq_true_iff_exists_attacker b Color.Black).1 hChk
    rcases this with ⟨kingSq, hKing, sq, p, _hSqMem, hAt, hColor, hAtk⟩
    have hk : kingSq = bk := by
      have : some bk = some kingSq := Eq.trans hK.symm hKing
      exact (Option.some.inj this).symm
    subst hk
    have hAt' : b.get sq = some p := by simpa using hAt
    have ⟨hsq, hp⟩ := KingsOnly.white_piece_of_get_of_color h sq p hAt' hColor
    subst hsq
    subst hp
    simpa [attacksSpec, kingPiece] using hAtk
  · intro hStep
    have hEx :
        ∃ kingSq,
          kingSquare b Color.Black = some kingSq ∧
          (∃ sq p,
            sq ∈ allSquares ∧
            b sq = some p ∧
            p.color = Color.White ∧
            attacksSpec b p sq kingSq) := by
      refine ⟨bk, hK, ?_⟩
      refine ⟨wk, kingPiece Color.White, Square.mem_all wk, ?_, rfl, ?_⟩
      · simpa using h.1
      · simpa [attacksSpec, kingPiece] using hStep
    exact (inCheck_eq_true_iff_exists_attacker b Color.Black).2 hEx

end Rules
end Chess
