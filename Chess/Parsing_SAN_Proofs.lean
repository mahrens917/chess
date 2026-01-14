import Chess.Parsing
import Chess.Rules

namespace Chess
namespace Parsing

-- ============================================================================
-- FORMAL PROOFS: SAN Round-Trip and Parser Soundness
-- ============================================================================

-- ============================================================================
-- BOARD VALIDITY PREDICATES
-- ============================================================================

/-- A board has at most one king of the given color.
    This is a fundamental invariant for valid chess positions. -/
def hasAtMostOneKing (b : Board) (c : Color) : Prop :=
  ∀ sq1 sq2 : Square,
    (∃ p1, b sq1 = some p1 ∧ p1.pieceType = PieceType.King ∧ p1.color = c) →
    (∃ p2, b sq2 = some p2 ∧ p2.pieceType = PieceType.King ∧ p2.color = c) →
    sq1 = sq2

/-- A board has valid king configuration (at most one king per color). -/
def hasValidKings (b : Board) : Prop :=
  hasAtMostOneKing b Color.White ∧ hasAtMostOneKing b Color.Black

/-- Helper: If two squares both have kings of the same color and there's at most one,
    the squares are equal. -/
theorem king_squares_eq_of_unique (b : Board) (c : Color) (sq1 sq2 : Square)
    (h_unique : hasAtMostOneKing b c)
    (h1 : ∃ p, b sq1 = some p ∧ p.pieceType = PieceType.King ∧ p.color = c)
    (h2 : ∃ p, b sq2 = some p ∧ p.pieceType = PieceType.King ∧ p.color = c) :
    sq1 = sq2 :=
  h_unique sq1 sq2 h1 h2

/-- Helper: If two squares have the same king (unique), the pieces are equal. -/
theorem king_piece_eq_of_unique (b : Board) (c : Color) (sq1 sq2 : Square) (p1 p2 : Piece)
    (h_unique : hasAtMostOneKing b c)
    (h1 : b sq1 = some p1 ∧ p1.pieceType = PieceType.King ∧ p1.color = c)
    (h2 : b sq2 = some p2 ∧ p2.pieceType = PieceType.King ∧ p2.color = c) :
    p1 = p2 := by
  have hsq : sq1 = sq2 := h_unique sq1 sq2 ⟨p1, h1⟩ ⟨p2, h2⟩
  subst hsq
  rw [h1.1] at h2
  exact Option.some.inj h2.1

-- ============================================================================
-- HELPER LEMMAS: List membership through foldr
-- ============================================================================

/-- Helper: m in foldr implies exists x in xs, m in f x (or m in init) -/
theorem mem_foldr_append {alpha beta : Type} (f : alpha → List beta) (init : List beta) (xs : List alpha) (m : beta) :
    m ∈ xs.foldr (fun x acc => f x ++ acc) init →
    m ∈ init ∨ ∃ x, x ∈ xs ∧ m ∈ f x := by
  intro hmem
  induction xs with
  | nil =>
    simp only [List.foldr_nil] at hmem
    exact Or.inl hmem
  | cons x rest ih =>
    simp only [List.foldr_cons] at hmem
    rw [List.mem_append] at hmem
    rcases hmem with hl | hr
    · right
      exact ⟨x, List.mem_cons_self, hl⟩
    · rcases ih hr with hinit | ⟨y, hy_mem, hy⟩
      · exact Or.inl hinit
      · right
        exact ⟨y, List.mem_cons.mpr (Or.inr hy_mem), hy⟩

/-- Helper: membership in legalMovesForCached implies basicLegalAndSafe -/
theorem mem_legalMovesForCached_implies_basicLegalAndSafe
    (gs : GameState) (sq : Square) (pins : List (Square × Square)) (m : Move) :
    m ∈ Rules.legalMovesForCached gs sq pins → Rules.basicLegalAndSafe gs m = true := by
  intro hmem
  unfold Rules.legalMovesForCached at hmem
  split at hmem
  · simp at hmem
  · rename_i p heq
    split at hmem
    · simp at hmem
    · have := List.mem_filter.mp hmem
      exact this.2

/-- Helper: membership in allLegalMoves implies basicLegalAndSafe -/
theorem mem_allLegalMoves_implies_basicLegalAndSafe
    (gs : GameState) (m : Move) :
    m ∈ Rules.allLegalMoves gs → Rules.basicLegalAndSafe gs m = true := by
  intro hmem
  unfold Rules.allLegalMoves at hmem
  have h := mem_foldr_append
    (fun sq => Rules.legalMovesForCached gs sq (Rules.pinnedSquares gs gs.toMove))
    [] allSquares m hmem
  rcases h with hinit | ⟨sq, _, hsq⟩
  · simp at hinit
  · exact mem_legalMovesForCached_implies_basicLegalAndSafe gs sq _ m hsq

/-- Helper: filter preserves membership in original list -/
theorem filter_mem_of_mem {alpha : Type} (l : List alpha) (p : alpha → Bool) (x : alpha) :
    x ∈ l.filter p → x ∈ l := by
  intro hmem
  exact (List.mem_filter.mp hmem).1

-- ============================================================================
-- HELPER LEMMAS: slidingTargets and pawn move properties
-- ============================================================================

/-- Helper: all moves in walk output have piece = p and fromSq = src -/
private theorem walk_piece_fromSq (src : Square) (p : Piece) (board : Board) (color : Color)
    (maxStep : Nat) (df dr : Int) (step : Nat) (acc : List Move)
    (hacc : ∀ m ∈ acc, m.piece = p ∧ m.fromSq = src) (m : Move)
    (hmem : m ∈ Rules.slidingTargets.walk src p board color maxStep df dr step acc) :
    m.piece = p ∧ m.fromSq = src := by
  induction step generalizing acc with
  | zero =>
    simp only [Rules.slidingTargets.walk] at hmem
    exact hacc m hmem
  | succ s ih =>
    simp only [Rules.slidingTargets.walk] at hmem
    cases h1 : Movement.squareFromInts (src.fileInt + df * (Int.ofNat (maxStep - s))) (src.rankInt + dr * (Int.ofNat (maxStep - s))) with
    | none =>
      simp only [h1] at hmem
      exact hacc m hmem
    | some target =>
      simp only [h1] at hmem
      by_cases he : Rules.isEmpty board target = true
      · simp only [he, ↓reduceIte] at hmem
        apply ih _ _ hmem
        intro m' hm'
        rw [List.mem_cons] at hm'
        rcases hm' with rfl | hacc'
        · simp
        · exact hacc m' hacc'
      · simp only [he, Bool.false_eq_true, ↓reduceIte] at hmem
        by_cases hc : Rules.isEnemyAt board color target = true
        · simp only [hc, ↓reduceIte] at hmem
          rw [List.mem_cons] at hmem
          rcases hmem with rfl | hacc'
          · simp
          · exact hacc m hacc'
        · simp only [hc, Bool.false_eq_true, ↓reduceIte] at hmem
          exact hacc m hmem

/-- Helper for foldr: all moves in foldr result have piece = p and fromSq = src -/
private theorem foldr_walk_piece_fromSq (src : Square) (p : Piece) (board : Board) (color : Color)
    (maxStep : Nat) (deltas : List (Int × Int)) (m : Move)
    (hmem : m ∈ deltas.foldr (fun d acc => Rules.slidingTargets.walk src p board color maxStep d.fst d.snd maxStep acc) []) :
    m.piece = p ∧ m.fromSq = src := by
  induction deltas generalizing m with
  | nil =>
    simp at hmem
  | cons d rest ih =>
    simp only [List.foldr_cons] at hmem
    apply walk_piece_fromSq src p board color maxStep d.fst d.snd maxStep _ _ m hmem
    intro m' hm'
    exact ih m' hm'

/-- Moves produced by slidingTargets all have piece = p and fromSq = src.
    This is a structural property: the walk function in slidingTargets constructs
    all moves with piece := p and fromSq := src by construction.
    Referenced by SemanticSlidingRespectsGeometryLemmas. -/
theorem mem_slidingTargets_piece_fromSq (gs : GameState) (src : Square) (p : Piece)
    (deltas : List (Int × Int)) (m : Move) :
    m ∈ Rules.slidingTargets gs src p deltas → m.piece = p ∧ m.fromSq = src := by
  intro hmem
  unfold Rules.slidingTargets at hmem
  exact foldr_walk_piece_fromSq src p gs.board p.color 7 deltas m hmem

-- Alias for backward compatibility
theorem slidingTargets_piece_fromSq (gs : GameState) (src : Square) (p : Piece)
    (deltas : List (Int × Int)) (m : Move) :
    m ∈ Rules.slidingTargets gs src p deltas → m.piece = p ∧ m.fromSq = src :=
  mem_slidingTargets_piece_fromSq gs src p deltas m

/-- Helper: promotionMoves preserves piece and fromSq. -/
theorem promotionMoves_piece_fromSq (m m' : Move) :
    m' ∈ Rules.promotionMoves m → m'.piece = m.piece ∧ m'.fromSq = m.fromSq := by
  intro hmem
  unfold Rules.promotionMoves at hmem
  split at hmem
  · simp only [List.mem_map] at hmem
    obtain ⟨pt, _, heq⟩ := hmem
    simp [← heq]
  · simp only [List.mem_singleton] at hmem
    simp [hmem]

/-- Helper: All pawn moves have piece = p and fromSq = src. -/
theorem pawn_pieceTargets_piece_fromSq (gs : GameState) (src : Square) (p : Piece) (m : Move)
    (hp : p.pieceType = PieceType.Pawn) :
    m ∈ Rules.pieceTargets gs src p → m.piece = p ∧ m.fromSq = src := by
  -- All pawn moves (forward and capture) are constructed with piece = p and fromSq = src.
  -- The proof requires tracing through the pawn move construction in pieceTargets.
  sorry

-- ============================================================================
-- HELPER LEMMAS: Properties of allLegalMoves membership
-- ============================================================================

/-- Helper: Moves in allLegalMoves have the correct turn color. -/
theorem allLegalMoves_turnMatches (gs : GameState) (m : Move)
    (h_valid : hasValidKings gs.board) :
    m ∈ Rules.allLegalMoves gs → m.piece.color = gs.toMove := by
  -- By construction of allLegalMoves: legalMovesForCached only generates moves
  -- when p.color = gs.toMove, and pieceTargets sets m.piece = p.
  sorry

/-- Helper: pieceTargets always sets move.piece to the given piece p. -/
theorem pieceTargets_sets_piece (gs : GameState) (sq : Square) (p : Piece) (m : Move)
    (h_valid : hasValidKings gs.board)
    (h_turn : p.color = gs.toMove) :
    gs.board sq = some p →
    m ∈ Rules.pieceTargets gs sq p → m.piece = p := by
  -- All piece types construct moves with piece = p.
  -- Castle case uses king uniqueness from h_valid.
  sorry

/-- Helper: pieceTargets always sets move.fromSq to the source square. -/
theorem pieceTargets_sets_fromSq (gs : GameState) (sq : Square) (p : Piece) (m : Move)
    (h_valid : hasValidKings gs.board)
    (h_turn : p.color = gs.toMove) :
    gs.board sq = some p →
    m ∈ Rules.pieceTargets gs sq p → m.fromSq = sq := by
  -- All piece types construct moves with fromSq = sq.
  -- Castle case uses king uniqueness from h_valid to show cfg.kingFrom = sq.
  sorry

/-- Helper: Moves in allLegalMoves have their piece at the origin square. -/
theorem allLegalMoves_originHasPiece (gs : GameState) (m : Move)
    (h_valid : hasValidKings gs.board) :
    m ∈ Rules.allLegalMoves gs → gs.board m.fromSq = some m.piece := by
  -- By construction: legalMovesForCached only generates moves when gs.board sq = some p,
  -- and pieceTargets sets move.piece = p and move.fromSq = sq.
  sorry

/-- Helper: Moves in allLegalMoves have different from and to squares. -/
theorem allLegalMoves_squaresDiffer (gs : GameState) (m : Move) :
    m ∈ Rules.allLegalMoves gs → m.fromSq ≠ m.toSq := by
  intro hmem
  have h1 := mem_allLegalMoves_implies_basicLegalAndSafe gs m hmem
  unfold Rules.basicLegalAndSafe at h1
  simp only [Bool.and_eq_true] at h1
  have h2 := h1.1
  unfold Rules.basicMoveLegalBool at h2
  simp only [Bool.and_eq_true] at h2
  obtain ⟨⟨⟨⟨_, _⟩, _⟩, _⟩, hsd⟩ := h2
  unfold Rules.squaresDiffer at hsd
  simp only [ne_eq, decide_eq_true_eq] at hsd
  exact hsd

-- Helper: Moves are equivalent if they produce the same board transformation
def MoveEquiv (m1 m2 : Move) : Prop :=
  m1.piece = m2.piece ∧
  m1.fromSq = m2.fromSq ∧
  m1.toSq = m2.toSq ∧
  m1.isCapture = m2.isCapture ∧
  m1.promotion = m2.promotion ∧
  m1.isCastle = m2.isCastle ∧
  m1.isEnPassant = m2.isEnPassant

-- ============================================================================
-- SAN ROUND-TRIP PROPERTIES
-- ============================================================================

/-- SAN round-trip property - parsing generated SAN recovers the original move. -/
theorem moveFromSAN_moveToSAN_roundtrip (gs : GameState) (m : Move) :
    Rules.isLegalMove gs m = true →
    ∃ m', moveFromSAN gs (moveToSAN gs m) = Except.ok m' ∧ MoveEquiv m m' := by
  -- The proof combines:
  -- 1. moveToSAN generates unique SAN for legal m
  -- 2. parseSanToken succeeds on moveToSAN output
  -- 3. moveFromSanToken finds m in filtered candidates
  -- 4. validateCheckHint passes (check/mate suffix from moveToSAN matches)
  sorry

/-- Helper: parseSanToken succeeds on moveToSAN output. -/
theorem parseSanToken_succeeds_on_moveToSAN (gs : GameState) (m : Move) :
    ∃ token, Parsing.parseSanToken (Parsing.moveToSAN gs m) = Except.ok token := by
  -- moveToSAN produces base ++ suffix where suffix in {"", "+", "#"}
  -- parseSanToken strips the check/mate suffix and normalizes castling notation.
  sorry

/-- Helper: parseSanToken extracts moveToSanBase correctly from moveToSAN output. -/
theorem parseSanToken_extracts_moveToSanBase (gs : GameState) (m : Move) (token : SanToken) :
    Parsing.parseSanToken (Parsing.moveToSAN gs m) = Except.ok token →
    Parsing.moveToSanBase gs m = token.san := by
  -- moveToSAN = moveToSanBase ++ suffix where suffix in {"", "+", "#"}
  -- parseSanToken strips the suffix and normalizes castling notation.
  sorry

/-- Legal moves pass the pawn promotion rank check in moveFromSanToken. -/
theorem legal_move_passes_promotion_rank_check (gs : GameState) (m : Move) :
    m ∈ Rules.allLegalMoves gs →
    (if m.piece.pieceType = PieceType.Pawn ∧ m.promotion.isSome then
      m.toSq.rankNat = Rules.pawnPromotionRank m.piece.color
    else true) := by
  intro h_legal
  by_cases h_pawn : m.piece.pieceType = PieceType.Pawn ∧ m.promotion.isSome
  · simp [h_pawn]
    -- From legality, promotion moves are at the correct rank.
    sorry
  · simp [h_pawn]

/-- Helper: moveFromSanToken finds and returns a move from the filter. -/
theorem moveFromSanToken_finds_move (gs : GameState) (token : SanToken) (m : Move)
    (hm_legal : m ∈ Rules.allLegalMoves gs)
    (hbase : Parsing.moveToSanBase gs m = token.san) :
    ∃ m', moveFromSanToken gs token = Except.ok m' ∧ MoveEquiv m m' := by
  -- The proof requires showing m passes all filters and is found.
  sorry

/-- Helper: moveFromSanToken only returns moves from allLegalMoves. -/
theorem moveFromSanToken_returns_legal (gs : GameState) (token : SanToken) (m : Move) :
    moveFromSanToken gs token = Except.ok m → m ∈ Rules.allLegalMoves gs := by
  intro hparse
  unfold moveFromSanToken at hparse
  simp only at hparse
  split at hparse
  · rename_i m' heq
    cases hv : validateCheckHint token (gs.movePiece m') with
    | error e =>
      simp only [hv] at hparse
      cases hparse
    | ok u =>
      simp only [hv, pure, Except.pure, bind, Except.bind] at hparse
      have heq' : m' = m := by injection hparse
      have h_singleton : m' ∈ [m'] := List.mem_singleton_self m'
      have heq_sym := heq.symm
      rw [heq_sym] at h_singleton
      have h_in_filtered := List.mem_filter.mp h_singleton
      have h_in_first_filter := List.mem_filter.mp h_in_filtered.1
      rw [heq'] at h_in_first_filter
      exact h_in_first_filter.1
  · simp at hparse
  · simp at hparse

/-- Helper: moveFromSAN only returns moves that are in allLegalMoves. -/
theorem moveFromSAN_returns_legal (gs : GameState) (san : String) (m : Move) :
    moveFromSAN gs san = Except.ok m → m ∈ Rules.allLegalMoves gs := by
  intro hparse
  unfold moveFromSAN at hparse
  cases hps : parseSanToken san with
  | error e =>
    simp only [hps] at hparse
    cases hparse
  | ok token =>
    simp only [hps] at hparse
    exact moveFromSanToken_returns_legal gs token m hparse

-- Theorem: SAN parsing preserves move structure
theorem moveFromSAN_preserves_move_structure (gs : GameState) (san : String) (m : Move)
    (h_valid : hasValidKings gs.board) :
    moveFromSAN gs san = Except.ok m →
    (m.piece.color = gs.toMove ∧
     gs.board m.fromSq = some m.piece ∧
     m.fromSq ≠ m.toSq) := by
  intro hparse
  have hmem : m ∈ Rules.allLegalMoves gs := moveFromSAN_returns_legal gs san m hparse
  exact And.intro (allLegalMoves_turnMatches gs m h_valid hmem)
         (And.intro (allLegalMoves_originHasPiece gs m h_valid hmem)
                    (allLegalMoves_squaresDiffer gs m hmem))

-- Theorem: Castling SAN strings are normalized
theorem parseSanToken_normalizes_castling (token : String) :
    (token.contains '0') →
    ∃ st, parseSanToken token = Except.ok st ∧ ¬(st.san.contains '0') := by
  -- parseSanToken uses normalizeCastleToken which replaces '0' with 'O'
  sorry

-- Theorem: Check/mate hints are validated
theorem moveFromSanToken_validates_check_hint (gs : GameState) (token : SanToken) (m : Move) :
    moveFromSanToken gs token = Except.ok m →
    (token.checkHint = some SanCheckHint.check →
      Rules.inCheck (Rules.GameState.playMove gs m).board (Rules.GameState.playMove gs m).toMove) ∧
    (token.checkHint = some SanCheckHint.mate →
      Rules.isCheckmate (Rules.GameState.playMove gs m)) := by
  -- The proof requires showing that validateCheckHint's check is equivalent
  -- to the check/mate state after GameState.playMove.
  sorry

end Parsing
end Chess
