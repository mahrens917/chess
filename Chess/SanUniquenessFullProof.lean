import Chess.Parsing
import Chess.Rules
import Chess.PathValidationProofs

namespace Chess
namespace Parsing

open Rules

set_option maxHeartbeats 800000

-- ============================================================================
-- MoveEquiv with all 9 fields (including castleRookFrom, castleRookTo)
-- ============================================================================

/-- Full move equivalence: all move fields are equal. -/
def MoveEquivFull (m1 m2 : Move) : Prop :=
  m1.piece = m2.piece ∧
  m1.fromSq = m2.fromSq ∧
  m1.toSq = m2.toSq ∧
  m1.isCapture = m2.isCapture ∧
  m1.promotion = m2.promotion ∧
  m1.isCastle = m2.isCastle ∧
  m1.isEnPassant = m2.isEnPassant ∧
  m1.castleRookFrom = m2.castleRookFrom ∧
  m1.castleRookTo = m2.castleRookTo

-- ============================================================================
-- SECTION 1: INJECTIVITY LEMMAS
-- ============================================================================

/-- pieceLetter is injective on PieceType -/
theorem pieceLetter_injective (pt1 pt2 : PieceType) :
    pieceLetter pt1 = pieceLetter pt2 → pt1 = pt2 := by
  cases pt1 <;> cases pt2 <;> simp [pieceLetter] <;> decide

/-- Square.algebraic is injective -/
theorem algebraic_injective {s1 s2 : Square} :
    s1.algebraic = s2.algebraic → s1 = s2 := by
  intro h
  have : ∀ (f1 f2 : Fin 8) (r1 r2 : Fin 8),
      ({ file := f1, rank := r1 } : Square).algebraic =
      ({ file := f2, rank := r2 } : Square).algebraic →
      f1 = f2 ∧ r1 = r2 := by native_decide
  have ⟨hf, hr⟩ := this s1.file s2.file s1.rank s2.rank h
  exact Square.ext hf hr

/-- fileChar is injective -/
theorem fileChar_injective {s1 s2 : Square}
    (h : s1.fileChar = s2.fileChar) : s1.file = s2.file := by
  have : ∀ (f1 f2 : Fin 8) (r1 r2 : Fin 8),
      ({ file := f1, rank := r1 } : Square).fileChar =
      ({ file := f2, rank := r2 } : Square).fileChar →
      f1 = f2 := by native_decide
  exact this s1.file s2.file s1.rank s2.rank h

-- ============================================================================
-- SECTION 2: STRING LENGTH LEMMAS
-- ============================================================================

/-- algebraic produces exactly 2 characters -/
theorem algebraic_toList_length (sq : Square) : sq.algebraic.toList.length = 2 := by
  unfold Square.algebraic
  simp [String.toList_append, Char.toString, String.toList_singleton]
  have hr := sq.rank.isLt
  unfold Square.rankNat Rank.toNat at *
  match sq.rank.val, hr with
  | 0, _ => native_decide | 1, _ => native_decide | 2, _ => native_decide | 3, _ => native_decide
  | 4, _ => native_decide | 5, _ => native_decide | 6, _ => native_decide | 7, _ => native_decide
  | n + 8, h => omega

/-- pieceLetter for non-Pawn types produces exactly 1 character -/
theorem pieceLetter_toList_length (pt : PieceType) (h : pt ≠ PieceType.Pawn) :
    (pieceLetter pt).toList.length = 1 := by
  cases pt with
  | King => native_decide | Queen => native_decide | Rook => native_decide
  | Bishop => native_decide | Knight => native_decide
  | Pawn => exact absurd rfl h

-- ============================================================================
-- SECTION 3: LIST APPEND CANCELLATION
-- ============================================================================

/-- If two appended lists are equal and left parts have equal length,
    then left parts are equal and right parts are equal. -/
theorem list_append_cancel_left {α : Type} (l1 l2 l3 l4 : List α)
    (hlen : l1.length = l3.length) (h : l1 ++ l2 = l3 ++ l4) :
    l1 = l3 ∧ l2 = l4 := by
  induction l1 generalizing l3 with
  | nil =>
    cases l3
    · simp at h; exact ⟨rfl, h⟩
    · simp at hlen
  | cons hd1 tl1 ih =>
    cases l3 with
    | nil => simp at hlen
    | cons hd3 tl3 =>
      simp only [List.cons_append] at h
      injection h with hhd htl
      subst hhd
      have := ih tl3 (by simp at hlen; omega) htl
      exact ⟨by rw [this.1], this.2⟩

-- ============================================================================
-- SECTION 4: FIRST CHARACTER ANALYSIS (pawn vs piece distinction)
-- ============================================================================

/-- pieceLetter for non-Pawn types starts with an uppercase character -/
private theorem pieceLetter_first_upper (pt : PieceType) (h : pt ≠ PieceType.Pawn) :
    ∃ c, (pieceLetter pt).toList = [c] ∧ c.isUpper = true := by
  cases pt with
  | King => exact ⟨'K', by native_decide, by native_decide⟩
  | Queen => exact ⟨'Q', by native_decide, by native_decide⟩
  | Rook => exact ⟨'R', by native_decide, by native_decide⟩
  | Bishop => exact ⟨'B', by native_decide, by native_decide⟩
  | Knight => exact ⟨'N', by native_decide, by native_decide⟩
  | Pawn => exact absurd rfl h

/-- File chars (a-h) are not uppercase -/
private theorem fileChar_not_upper (f : Fin 8) :
    (Char.ofNat ('a'.toNat + f.val)).isUpper = false := by
  have hf := f.isLt
  match f.val, hf with
  | 0, _ => native_decide | 1, _ => native_decide | 2, _ => native_decide | 3, _ => native_decide
  | 4, _ => native_decide | 5, _ => native_decide | 6, _ => native_decide | 7, _ => native_decide
  | n + 8, h => omega

/-- For a non-castle pawn move, the first char of moveToSanBase is not uppercase -/
private theorem pawn_san_first_not_upper (gs : GameState) (m : Move)
    (hnc : m.isCastle = false) (hp : m.piece.pieceType = PieceType.Pawn) :
    ∀ c, (moveToSanBase gs m).toList.head? = some c → c.isUpper = false := by
  intro c hc
  unfold moveToSanBase at hc
  simp only [hnc, hp, ↓reduceIte, Bool.false_eq_true] at hc
  by_cases hcap : (m.isCapture || m.isEnPassant) = true
  · simp only [hcap, ↓reduceIte] at hc
    rw [String.toList_append, String.toList_append, String.toList_append,
        String.toList_singleton] at hc
    simp only [List.cons_append, List.head?_cons] at hc
    injection hc with heq; rw [← heq]
    unfold Square.fileChar Square.fileNat File.toNat
    exact fileChar_not_upper m.fromSq.file
  · simp only [hcap, Bool.false_eq_true, ↓reduceIte] at hc
    rw [String.toList_append, String.toList_append, String.toList_append,
        String.toList_empty] at hc
    simp only [List.nil_append] at hc
    unfold Square.algebraic at hc
    rw [String.toList_append] at hc
    change ((String.singleton (Char.ofNat ('a'.toNat + m.toSq.fileNat))).toList ++
        (toString (m.toSq.rankNat + 1)).toList ++ (promotionSuffix m).toList).head? = some c at hc
    rw [String.toList_singleton] at hc
    simp only [List.cons_append, List.head?_cons] at hc
    injection hc with heq; rw [← heq]
    unfold Square.fileNat File.toNat
    exact fileChar_not_upper m.toSq.file

/-- For a non-castle non-pawn move, the first char of moveToSanBase is uppercase -/
private theorem piece_san_first_upper (gs : GameState) (m : Move)
    (hnc : m.isCastle = false) (hp : m.piece.pieceType ≠ PieceType.Pawn) :
    ∀ c, (moveToSanBase gs m).toList.head? = some c → c.isUpper = true := by
  intro c hc
  unfold moveToSanBase at hc
  simp only [hnc, hp, ↓reduceIte, Bool.false_eq_true] at hc
  obtain ⟨pc, hpc_list, hpc_upper⟩ := pieceLetter_first_upper m.piece.pieceType hp
  rw [String.toList_append, String.toList_append, String.toList_append,
      String.toList_append] at hc
  rw [hpc_list] at hc
  simp only [List.cons_append, List.head?_cons] at hc
  injection hc with heq; rw [← heq]
  exact hpc_upper

/-- moveToSanBase is nonempty for non-castle moves -/
private theorem moveToSanBase_toList_ne_nil (gs : GameState) (m : Move)
    (hnc : m.isCastle = false) :
    (moveToSanBase gs m).toList ≠ [] := by
  unfold moveToSanBase
  simp only [hnc, ↓reduceIte, Bool.false_eq_true]
  split
  · -- Pawn case
    intro h
    rw [String.toList_append, String.toList_append, String.toList_append] at h
    have := List.append_eq_nil_iff.mp h
    have := List.append_eq_nil_iff.mp this.1
    have h_alg_nil := this.2
    have h_alg_len := algebraic_toList_length m.toSq
    rw [h_alg_nil] at h_alg_len; simp at h_alg_len
  · -- Piece case
    rename_i hnp
    intro h
    rw [String.toList_append, String.toList_append, String.toList_append,
        String.toList_append] at h
    have := List.append_eq_nil_iff.mp h
    have := List.append_eq_nil_iff.mp this.1
    have := List.append_eq_nil_iff.mp this.1
    have := List.append_eq_nil_iff.mp this.1
    obtain ⟨_, hpc, _⟩ := pieceLetter_first_upper m.piece.pieceType hnp
    rw [hpc] at this
    exact List.cons_ne_nil _ _ this.1

-- ============================================================================
-- SECTION 5: NON-CASTLE LEGAL MOVES HAVE castleRookFrom/To = none
-- ============================================================================

/-- walk-generated moves have castleRookFrom/To = none -/
private theorem walk_castle_none (src : Square) (p : Piece) (board : Board) (color : Color)
    (maxStep : Nat) (df dr : Int) (step : Nat) (acc : List Move)
    (hacc : ∀ m ∈ acc, m.castleRookFrom = none ∧ m.castleRookTo = none)
    (m : Move)
    (hmem : m ∈ Rules.slidingTargets.walk src p board color maxStep df dr step acc) :
    m.castleRookFrom = none ∧ m.castleRookTo = none := by
  induction step generalizing acc with
  | zero =>
    simp only [Rules.slidingTargets.walk] at hmem
    exact hacc m hmem
  | succ s ih =>
    simp only [Rules.slidingTargets.walk] at hmem
    cases h1 : Movement.squareFromInts (src.fileInt + df * (Int.ofNat (maxStep - s)))
        (src.rankInt + dr * (Int.ofNat (maxStep - s))) with
    | none => simp only [h1] at hmem; exact hacc m hmem
    | some target =>
      simp only [h1] at hmem
      by_cases he : Rules.isEmpty board target = true
      · simp only [he, ↓reduceIte] at hmem
        apply ih _ _ hmem
        intro m' hm'
        rw [List.mem_cons] at hm'
        rcases hm' with rfl | h'
        · exact ⟨rfl, rfl⟩
        · exact hacc m' h'
      · simp only [he, Bool.false_eq_true, ↓reduceIte] at hmem
        by_cases hc : Rules.isEnemyAt board color target = true
        · simp only [hc, ↓reduceIte] at hmem
          rw [List.mem_cons] at hmem
          rcases hmem with rfl | h'
          · exact ⟨rfl, rfl⟩
          · exact hacc m h'
        · simp only [hc, Bool.false_eq_true, ↓reduceIte] at hmem
          exact hacc m hmem

/-- foldr of walk: castleRookFrom/To = none -/
private theorem foldr_walk_castle_none (src : Square) (p : Piece) (board : Board)
    (color : Color) (maxStep : Nat) (deltas : List (Int × Int)) (m : Move)
    (hmem : m ∈ deltas.foldr (fun d acc =>
      Rules.slidingTargets.walk src p board color maxStep d.fst d.snd maxStep acc) []) :
    m.castleRookFrom = none ∧ m.castleRookTo = none := by
  induction deltas generalizing m with
  | nil => simp at hmem
  | cons d rest ih =>
    simp only [List.foldr_cons] at hmem
    exact walk_castle_none src p board color maxStep d.fst d.snd maxStep
      _ (fun m' hm' => ih m' hm') m hmem

/-- filterMap-generated moves: castleRookFrom/To = none -/
private theorem filterMap_castle_none (gs : GameState) (sq : Square) (p : Piece)
    (targets : List Square) (m : Move)
    (hmem : m ∈ targets.filterMap (fun target =>
      if Rules.destinationFriendlyFree gs { piece := p, fromSq := sq, toSq := target } then
        match gs.board target with
        | some _ => some { piece := p, fromSq := sq, toSq := target, isCapture := true }
        | none => some { piece := p, fromSq := sq, toSq := target }
      else none)) :
    m.castleRookFrom = none ∧ m.castleRookTo = none := by
  obtain ⟨target, _, hfm⟩ := List.mem_filterMap.mp hmem
  by_cases hdest : Rules.destinationFriendlyFree gs { piece := p, fromSq := sq, toSq := target } = true
  · simp only [hdest, ↓reduceIte] at hfm
    split at hfm
    · injection hfm with h; subst h; exact ⟨rfl, rfl⟩
    · injection hfm with h; subst h; exact ⟨rfl, rfl⟩
  · simp only [hdest, Bool.false_eq_true, ↓reduceIte] at hfm; exact absurd hfm Option.noConfusion

/-- promotionMoves preserves castleRookFrom/To = none -/
private theorem promotionMoves_castle_none (m m' : Move)
    (hm : m.castleRookFrom = none ∧ m.castleRookTo = none) :
    m' ∈ Rules.promotionMoves m →
    m'.castleRookFrom = none ∧ m'.castleRookTo = none := by
  intro hmem
  unfold Rules.promotionMoves at hmem
  split at hmem
  · simp only [List.mem_map] at hmem
    obtain ⟨_, _, heq⟩ := hmem; subst heq; exact ⟨hm.1, hm.2⟩
  · simp only [List.mem_singleton] at hmem; subst hmem; exact hm

/-- Pawn forward base moves: castleRookFrom/To = none -/
private theorem pawn_fwd_castle_none (gs : GameState) (src : Square) (p : Piece) (m : Move)
    (hmem : m ∈ (match Movement.squareFromInts src.fileInt (src.rankInt + Movement.pawnDirection p.color) with
      | some target =>
          if Rules.isEmpty gs.board target then
            [{ piece := p, fromSq := src, toSq := target : Move }] ++
            (if src.rankNat = Rules.pawnStartRank p.color then
              match Movement.squareFromInts src.fileInt (src.rankInt + 2 * Movement.pawnDirection p.color) with
              | some target2 =>
                  if Rules.isEmpty gs.board target2 then
                    [{ piece := p, fromSq := src, toSq := target2 : Move }]
                  else []
              | none => []
            else [])
          else []
      | none => [])) :
    m.castleRookFrom = none ∧ m.castleRookTo = none := by
  cases h1 : Movement.squareFromInts src.fileInt (src.rankInt + Movement.pawnDirection p.color) with
  | none => simp only [h1] at hmem; simp at hmem
  | some target =>
    simp only [h1] at hmem
    by_cases he : Rules.isEmpty gs.board target = true
    · simp only [he, ↓reduceIte] at hmem
      rw [List.mem_append] at hmem
      rcases hmem with hb | hd
      · simp only [List.mem_singleton] at hb; subst hb; exact ⟨rfl, rfl⟩
      · by_cases hr : src.rankNat = Rules.pawnStartRank p.color
        · simp only [hr, ↓reduceIte] at hd
          cases h2 : Movement.squareFromInts src.fileInt (src.rankInt + 2 * Movement.pawnDirection p.color) with
          | none => simp only [h2] at hd; simp at hd
          | some t2 =>
            simp only [h2] at hd
            by_cases he2 : Rules.isEmpty gs.board t2 = true
            · simp only [he2, ↓reduceIte, List.mem_singleton] at hd; subst hd; exact ⟨rfl, rfl⟩
            · simp only [he2, Bool.false_eq_true, ↓reduceIte, List.not_mem_nil] at hd
        · simp only [hr, ↓reduceIte, List.not_mem_nil] at hd
    · simp only [he, Bool.false_eq_true, ↓reduceIte, List.not_mem_nil] at hmem

/-- Pawn capture moves: castleRookFrom/To = none -/
private theorem pawn_cap_castle_none (gs : GameState) (src : Square) (p : Piece) (m : Move)
    (hmem : m ∈ ([-1, 1] : List Int).foldr
        (fun df acc =>
          match Movement.squareFromInts (src.fileInt + df) (src.rankInt + Movement.pawnDirection p.color) with
          | some target =>
              if Rules.isEnemyAt gs.board p.color target then
                Rules.promotionMoves { piece := p, fromSq := src, toSq := target, isCapture := true } ++ acc
              else if gs.enPassantTarget = some target ∧ Rules.isEmpty gs.board target then
                { piece := p, fromSq := src, toSq := target, isCapture := true, isEnPassant := true } :: acc
              else acc
          | none => acc)
        []) :
    m.castleRookFrom = none ∧ m.castleRookTo = none := by
  simp only [List.foldr_cons, List.foldr_nil] at hmem
  cases h1 : Movement.squareFromInts (src.fileInt + (-1)) (src.rankInt + Movement.pawnDirection p.color) with
  | none =>
    simp only [h1] at hmem
    cases h2 : Movement.squareFromInts (src.fileInt + 1) (src.rankInt + Movement.pawnDirection p.color) with
    | none => simp only [h2] at hmem; simp at hmem
    | some t2 =>
      simp only [h2] at hmem
      by_cases he2 : Rules.isEnemyAt gs.board p.color t2 = true
      · simp only [he2, ↓reduceIte, List.append_nil] at hmem
        exact promotionMoves_castle_none _ m ⟨rfl, rfl⟩ hmem
      · simp only [he2, Bool.false_eq_true, ↓reduceIte] at hmem
        by_cases hep : gs.enPassantTarget = some t2 ∧ Rules.isEmpty gs.board t2
        · rw [if_pos hep] at hmem; simp only [List.mem_singleton] at hmem; subst hmem; exact ⟨rfl, rfl⟩
        · rw [if_neg hep] at hmem; simp at hmem
  | some t1 =>
    simp only [h1] at hmem
    by_cases he1 : Rules.isEnemyAt gs.board p.color t1 = true
    · simp only [he1, ↓reduceIte] at hmem
      rw [List.mem_append] at hmem
      rcases hmem with hp1 | hrest
      · exact promotionMoves_castle_none _ m ⟨rfl, rfl⟩ hp1
      · cases h2 : Movement.squareFromInts (src.fileInt + 1) (src.rankInt + Movement.pawnDirection p.color) with
        | none => simp only [h2] at hrest; simp at hrest
        | some t2 =>
          simp only [h2] at hrest
          by_cases he2 : Rules.isEnemyAt gs.board p.color t2 = true
          · simp only [he2, ↓reduceIte, List.append_nil] at hrest
            exact promotionMoves_castle_none _ m ⟨rfl, rfl⟩ hrest
          · simp only [he2, Bool.false_eq_true, ↓reduceIte] at hrest
            by_cases hep : gs.enPassantTarget = some t2 ∧ Rules.isEmpty gs.board t2
            · rw [if_pos hep] at hrest; simp only [List.mem_singleton] at hrest; subst hrest; exact ⟨rfl, rfl⟩
            · rw [if_neg hep] at hrest; simp at hrest
    · simp only [he1, Bool.false_eq_true, ↓reduceIte] at hmem
      by_cases hep1 : gs.enPassantTarget = some t1 ∧ Rules.isEmpty gs.board t1
      · rw [if_pos hep1] at hmem
        rw [List.mem_cons] at hmem
        rcases hmem with rfl | hrest
        · exact ⟨rfl, rfl⟩
        · cases h2 : Movement.squareFromInts (src.fileInt + 1) (src.rankInt + Movement.pawnDirection p.color) with
          | none => simp only [h2] at hrest; simp at hrest
          | some t2 =>
            simp only [h2] at hrest
            by_cases he2 : Rules.isEnemyAt gs.board p.color t2 = true
            · simp only [he2, ↓reduceIte, List.append_nil] at hrest
              exact promotionMoves_castle_none _ m ⟨rfl, rfl⟩ hrest
            · simp only [he2, Bool.false_eq_true, ↓reduceIte] at hrest
              by_cases hep : gs.enPassantTarget = some t2 ∧ Rules.isEmpty gs.board t2
              · rw [if_pos hep] at hrest; simp only [List.mem_singleton] at hrest; subst hrest; exact ⟨rfl, rfl⟩
              · rw [if_neg hep] at hrest; simp at hrest
      · rw [if_neg hep1] at hmem
        cases h2 : Movement.squareFromInts (src.fileInt + 1) (src.rankInt + Movement.pawnDirection p.color) with
        | none => simp only [h2] at hmem; simp at hmem
        | some t2 =>
          simp only [h2] at hmem
          by_cases he2 : Rules.isEnemyAt gs.board p.color t2 = true
          · simp only [he2, ↓reduceIte, List.append_nil] at hmem
            exact promotionMoves_castle_none _ m ⟨rfl, rfl⟩ hmem
          · simp only [he2, Bool.false_eq_true, ↓reduceIte] at hmem
            by_cases hep : gs.enPassantTarget = some t2 ∧ Rules.isEmpty gs.board t2
            · rw [if_pos hep] at hmem; simp only [List.mem_singleton] at hmem; subst hmem; exact ⟨rfl, rfl⟩
            · rw [if_neg hep] at hmem; simp at hmem

/-- foldr of promotionMoves preserves castle-none -/
private theorem foldr_promotionMoves_castle_none (moves : List Move) (m : Move)
    (hbase : ∀ mb ∈ moves, mb.castleRookFrom = none ∧ mb.castleRookTo = none)
    (hmem : m ∈ moves.foldr (fun mv acc => Rules.promotionMoves mv ++ acc) []) :
    m.castleRookFrom = none ∧ m.castleRookTo = none := by
  induction moves with
  | nil => simp at hmem
  | cons x xs ih =>
    simp only [List.foldr_cons] at hmem
    rw [List.mem_append] at hmem
    rcases hmem with hp | hrest
    · exact promotionMoves_castle_none x m (hbase x (List.mem_cons_self)) hp
    · exact ih (fun mb hm => hbase mb (List.mem_cons.mpr (Or.inr hm))) hrest

/-- Castle moves from castleMoveIfLegal have isCastle = true -/
private theorem castleMoveIfLegal_isCastle (gs : GameState) (kingSide : Bool) (m : Move) :
    castleMoveIfLegal gs kingSide = some m → m.isCastle = true := by
  intro h
  unfold castleMoveIfLegal at h
  simp only [Bool.and_eq_true] at h
  split at h
  case isTrue =>
    split at h
    case h_1 k r _ _ =>
      split at h
      case isTrue =>
        split at h
        case isTrue => injection h with h; subst h; rfl
        case isFalse => exact Option.noConfusion h
      case isFalse => exact Option.noConfusion h
    case h_2 => exact Option.noConfusion h
  case isFalse => exact Option.noConfusion h

/-- All non-castle pieceTargets moves have castleRookFrom/To = none -/
private theorem pieceTargets_castle_none (gs : GameState) (sq : Square) (p : Piece) (m : Move)
    (hmem : m ∈ Rules.pieceTargets gs sq p) (hnc : m.isCastle = false) :
    m.castleRookFrom = none ∧ m.castleRookTo = none := by
  unfold Rules.pieceTargets at hmem
  cases hp : p.pieceType with
  | King =>
    simp only [hp] at hmem
    rw [List.mem_append] at hmem
    rcases hmem with hstd | hcastle
    · exact filterMap_castle_none gs sq p _ m hstd
    · -- Castle moves have isCastle = true, contradicting hnc
      obtain ⟨opt, hopt_mem, hopt_eq⟩ := List.mem_filterMap.mp hcastle
      simp only [id_eq] at hopt_eq
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hopt_mem
      rcases hopt_mem with rfl | rfl
      · exact absurd (castleMoveIfLegal_isCastle gs true m hopt_eq) (by rw [hnc]; decide)
      · exact absurd (castleMoveIfLegal_isCastle gs false m hopt_eq) (by rw [hnc]; decide)
  | Queen =>
    simp only [hp] at hmem; unfold Rules.slidingTargets at hmem
    exact foldr_walk_castle_none sq p gs.board p.color 7 _ m hmem
  | Rook =>
    simp only [hp] at hmem; unfold Rules.slidingTargets at hmem
    exact foldr_walk_castle_none sq p gs.board p.color 7 _ m hmem
  | Bishop =>
    simp only [hp] at hmem; unfold Rules.slidingTargets at hmem
    exact foldr_walk_castle_none sq p gs.board p.color 7 _ m hmem
  | Knight =>
    simp only [hp] at hmem
    exact filterMap_castle_none gs sq p _ m hmem
  | Pawn =>
    simp only [hp] at hmem
    rw [List.mem_append] at hmem
    rcases hmem with hfwd | hcap
    · exact foldr_promotionMoves_castle_none _ m (fun mb hm => pawn_fwd_castle_none gs sq p mb hm) hfwd
    · exact pawn_cap_castle_none gs sq p m hcap

/-- Helper: foldr append membership -/
private theorem mem_foldr_append {α β : Type} (f : α → List β) (xs : List α) (m : β) :
    m ∈ xs.foldr (fun x acc => f x ++ acc) [] →
    ∃ x, x ∈ xs ∧ m ∈ f x := by
  intro hmem
  induction xs with
  | nil => simp at hmem
  | cons x rest ih =>
    simp only [List.foldr_cons] at hmem
    rw [List.mem_append] at hmem
    rcases hmem with hl | hr
    · exact ⟨x, List.mem_cons_self, hl⟩
    · have ⟨y, hy, hm⟩ := ih hr
      exact ⟨y, List.mem_cons.mpr (Or.inr hy), hm⟩

/-- Non-castle legal moves have castleRookFrom = none and castleRookTo = none -/
theorem noncastle_legal_castle_none (gs : GameState) (m : Move)
    (hmem : m ∈ Rules.allLegalMoves gs) (hnc : m.isCastle = false) :
    m.castleRookFrom = none ∧ m.castleRookTo = none := by
  unfold Rules.allLegalMoves at hmem
  have ⟨sq, _, hsq⟩ := mem_foldr_append
    (fun sq => Rules.legalMovesForCached gs sq (Rules.pinnedSquares gs gs.toMove))
    allSquares m hmem
  unfold Rules.legalMovesForCached at hsq
  cases hbd : gs.board sq with
  | none => simp only [hbd, List.not_mem_nil] at hsq
  | some p =>
    simp only [hbd] at hsq
    by_cases hcolor : p.color ≠ gs.toMove
    · rw [if_pos hcolor] at hsq; simp at hsq
    · rw [if_neg hcolor] at hsq
      have h1 := List.mem_filter.mp hsq
      have h2 := List.mem_filter.mp h1.1
      exact pieceTargets_castle_none gs sq p m h2.1 hnc

-- ============================================================================
-- SECTION 5b: HELPER LEMMAS FOR STRING DECOMPOSITION
-- ============================================================================

/-- promotionSuffix is injective: same suffix string → same promotion -/
private theorem promotionSuffix_injective (m1 m2 : Move)
    (h : promotionSuffix m1 = promotionSuffix m2) : m1.promotion = m2.promotion := by
  unfold promotionSuffix at h
  match hp1 : m1.promotion, hp2 : m2.promotion with
  | none, none => rfl
  | none, some pt2 =>
    simp only [hp1, hp2] at h
    have hlen := congrArg String.length h
    simp [String.length_append] at hlen
    have : (toString "=").length = 1 := by native_decide
    omega
  | some pt1, none =>
    simp only [hp1, hp2] at h
    have hlen := congrArg String.length h
    simp [String.length_append] at hlen
    have : (toString "=").length = 1 := by native_decide
    omega
  | some pt1, some pt2 =>
    simp only [hp1, hp2] at h
    congr 1
    apply pieceLetter_injective
    have hlist := congrArg String.toList h
    simp [String.toList_append] at hlist
    exact String.toList_inj.mp hlist

/-- sanDisambiguation for pawns is empty -/
private theorem sanDisambiguation_pawn (gs : GameState) (m : Move)
    (hp : m.piece.pieceType = PieceType.Pawn) :
    sanDisambiguation gs m = "" := by
  unfold sanDisambiguation
  simp [hp]

/-- algebraic.toList has the form [fileChar, rankChar] -/
private theorem algebraic_toList_form (sq : Square) :
    sq.algebraic.toList = [sq.fileChar, sq.rankChar] := by
  have : ∀ (f r : Fin 8),
    ({ file := f, rank := r } : Square).algebraic.toList =
    [({ file := f, rank := r } : Square).fileChar, ({ file := f, rank := r } : Square).rankChar] := by
    native_decide
  exact this sq.file sq.rank

/-- rankChar is never 'x' -/
private theorem rankChar_ne_x (sq : Square) : sq.rankChar ≠ 'x' := by
  have : ∀ (f r : Fin 8), ({ file := f, rank := r } : Square).rankChar ≠ 'x' := by native_decide
  exact this sq.file sq.rank

/-- rankChar is injective -/
private theorem rankChar_injective {s1 s2 : Square}
    (h : s1.rankChar = s2.rankChar) : s1.rank = s2.rank := by
  have : ∀ (f1 f2 : Fin 8) (r1 r2 : Fin 8),
      ({ file := f1, rank := r1 } : Square).rankChar =
      ({ file := f2, rank := r2 } : Square).rankChar →
      r1 = r2 := by native_decide
  exact this s1.file s2.file s1.rank s2.rank h

/-- 'x' is not in a singleton fileChar string -/
private theorem x_not_in_singleton_fileChar (sq : Square) :
    'x' ∉ (String.singleton sq.fileChar).toList := by
  simp only [String.toList_singleton, List.mem_singleton]
  intro h
  have : ∀ (f r : Fin 8), ({ file := f, rank := r } : Square).fileChar ≠ 'x' := by native_decide
  exact this sq.file sq.rank h.symm

/-- 'x' is not in a singleton rankChar string -/
private theorem x_not_in_singleton_rankChar (sq : Square) :
    'x' ∉ (String.singleton sq.rankChar).toList := by
  simp only [String.toList_singleton, List.mem_singleton]
  intro h
  have : ∀ (f r : Fin 8), ({ file := f, rank := r } : Square).rankChar ≠ 'x' := by native_decide
  exact this sq.file sq.rank h.symm

/-- Characters in sanDisambiguation are fileChar or rankChar of fromSq -/
private theorem sanDisambiguation_chars (gs : GameState) (m : Move) (c : Char)
    (hc : c ∈ (sanDisambiguation gs m).toList) :
    c = m.fromSq.fileChar ∨ c = m.fromSq.rankChar := by
  unfold sanDisambiguation at hc
  by_cases hp : m.piece.pieceType = PieceType.Pawn
  · simp [hp] at hc
  · simp only [hp, ↓reduceIte] at hc
    generalize (Rules.allLegalMoves gs |>.filter _) = peers at hc
    by_cases he : peers.isEmpty = true
    · simp [he] at hc
    · simp only [he, ↓reduceIte] at hc
      generalize peers.any (fun p => decide (p.fromSq.file = m.fromSq.file)) = fc at hc
      generalize peers.any (fun p => decide (p.fromSq.rank = m.fromSq.rank)) = rc at hc
      cases fc <;> cases rc <;>
        simp_all [String.toList_singleton, String.toList_append, List.mem_singleton, List.mem_cons]

/-- 'x' does not appear in sanDisambiguation output -/
private theorem x_not_in_sanDisambiguation (gs : GameState) (m : Move) :
    'x' ∉ (sanDisambiguation gs m).toList := by
  intro hc
  rcases sanDisambiguation_chars gs m 'x' hc with h1 | h2
  · have : ∀ (f r : Fin 8), ({ file := f, rank := r } : Square).fileChar ≠ 'x' := by native_decide
    exact this m.fromSq.file m.fromSq.rank h1.symm
  · have : ∀ (f r : Fin 8), ({ file := f, rank := r } : Square).rankChar ≠ 'x' := by native_decide
    exact this m.fromSq.file m.fromSq.rank h2.symm

/-- 'x' does not appear in algebraic output -/
private theorem x_not_in_algebraic (sq : Square) : 'x' ∉ sq.algebraic.toList := by
  have : ∀ (f r : Fin 8), 'x' ∉ ({ file := f, rank := r } : Square).algebraic.toList := by native_decide
  exact this sq.file sq.rank

/-- 'x' does not appear in promotionSuffix output -/
private theorem x_not_in_promotionSuffix (m : Move) : 'x' ∉ (promotionSuffix m).toList := by
  unfold promotionSuffix
  match m.promotion with
  | none => simp
  | some pt =>
    simp only [String.toList_append, List.mem_append]
    intro h
    rcases h with h1 | h2
    · have : (toString "=").toList = ['='] := by native_decide
      rw [this] at h1; simp only [List.mem_singleton] at h1
      exact absurd h1 (by native_decide)
    · cases pt <;> (simp [pieceLetter] at h2; exact absurd h2 (by native_decide))

/-- 'x' does not appear in pieceLetter for non-Pawn -/
private theorem x_not_in_pieceLetter (pt : PieceType) (hnp : pt ≠ PieceType.Pawn) :
    'x' ∉ (pieceLetter pt).toList := by
  cases pt <;> simp_all [pieceLetter] <;> native_decide

/-- 'x' appears in piece SAN (non-pawn, non-castle) iff capture -/
private theorem x_not_in_piece_san_nocap (gs : GameState) (m : Move)
    (hnc : m.isCastle = false) (hnp : m.piece.pieceType ≠ PieceType.Pawn)
    (hcap : (m.isCapture || m.isEnPassant) = false) :
    'x' ∉ (moveToSanBase gs m).toList := by
  intro hmem
  have hsan : moveToSanBase gs m =
    pieceLetter m.piece.pieceType ++ sanDisambiguation gs m ++ "" ++ m.toSq.algebraic ++ promotionSuffix m := by
    unfold moveToSanBase; simp [hnc, hnp, hcap]
  rw [hsan] at hmem
  simp only [String.toList_append, List.mem_append, String.toList_empty, List.not_mem_nil,
             or_false] at hmem
  rcases hmem with ((h1 | h2) | h4) | h5
  · exact x_not_in_pieceLetter m.piece.pieceType hnp h1
  · exact x_not_in_sanDisambiguation gs m h2
  · exact x_not_in_algebraic m.toSq h4
  · exact x_not_in_promotionSuffix m h5

private theorem x_mem_piece_san_iff (gs : GameState) (m : Move)
    (hnc : m.isCastle = false) (hnp : m.piece.pieceType ≠ PieceType.Pawn) :
    'x' ∈ (moveToSanBase gs m).toList ↔ (m.isCapture || m.isEnPassant) = true := by
  constructor
  · intro hmem
    by_cases hcap : (m.isCapture || m.isEnPassant) = true
    · exact hcap
    · exfalso
      have hcapf : (m.isCapture || m.isEnPassant) = false := by
        cases h : m.isCapture || m.isEnPassant
        · rfl
        · exact absurd h hcap
      exact x_not_in_piece_san_nocap gs m hnc hnp hcapf hmem
  · intro hcap
    have hsan : moveToSanBase gs m =
      pieceLetter m.piece.pieceType ++ sanDisambiguation gs m ++ "x" ++ m.toSq.algebraic ++ promotionSuffix m := by
      unfold moveToSanBase; simp [hnc, hnp, hcap]
    have hx : 'x' ∈ ("x" : String).toList := by native_decide
    -- Transport membership through the string equality
    have hlist_eq : (moveToSanBase gs m).toList =
      (pieceLetter m.piece.pieceType ++ sanDisambiguation gs m ++ "x" ++
       m.toSq.algebraic ++ promotionSuffix m).toList := congrArg String.toList hsan
    rw [hlist_eq]
    simp only [String.toList_append, List.mem_append]
    left; left; right; exact hx

/-- list_append_cancel_right: if suffix lengths match, both parts match -/
private theorem list_append_cancel_right {α : Type} (l1 l2 l3 l4 : List α)
    (hlen : l2.length = l4.length) (h : l1 ++ l2 = l3 ++ l4) :
    l1 = l3 ∧ l2 = l4 := by
  have hlen_total := congrArg List.length h
  simp [List.length_append] at hlen_total
  exact list_append_cancel_left l1 l2 l3 l4 (by omega) h

/-- pieceLetter has length 1 for non-Pawn (String.length version) -/
private theorem pieceLetter_length (pt : PieceType) (hnp : pt ≠ PieceType.Pawn) :
    (pieceLetter pt).length = 1 := by
  cases pt <;> simp_all [pieceLetter] <;> native_decide

/-- promotionSuffix has length 0, 1, or 2 (normally 0 or 2, 1 only for Pawn promotion) -/
private theorem promotionSuffix_length (m : Move) :
    (promotionSuffix m).toList.length ≤ 2 := by
  unfold promotionSuffix
  match m.promotion with
  | none => simp
  | some pt => simp [String.toList_append]; cases pt <;> simp [pieceLetter] <;> native_decide

-- ============================================================================
-- SECTION 6: CORE STRING DECOMPOSITION
-- ============================================================================

/-- Core string decomposition: equal moveToSanBase for non-castle legal moves
    implies same piece type, same toSq, same capture|ep flag, same promotion,
    same disambiguation, and same file char for pawn captures.

    This is the key string-level injectivity result that underpins SAN uniqueness.
    The proof requires character-level list analysis of the moveToSanBase output
    structure, handling pawn and piece cases separately through first-character
    distinction.

    PROOF STATUS: The cross-case impossibility (pawn vs piece) is fully proven
    via first-character analysis. The same-category decomposition requires
    further character-level parsing infrastructure. -/
private theorem moveToSanBase_eq_implies_fields (gs : GameState) (m1 m2 : Move)
    (h1 : m1 ∈ Rules.allLegalMoves gs) (h2 : m2 ∈ Rules.allLegalMoves gs)
    (hbase : moveToSanBase gs m1 = moveToSanBase gs m2)
    (hnc1 : m1.isCastle = false) (hnc2 : m2.isCastle = false) :
    m1.piece.pieceType = m2.piece.pieceType ∧
    m1.toSq = m2.toSq ∧
    (m1.isCapture || m1.isEnPassant) = (m2.isCapture || m2.isEnPassant) ∧
    m1.promotion = m2.promotion ∧
    sanDisambiguation gs m1 = sanDisambiguation gs m2 ∧
    (m1.piece.pieceType = PieceType.Pawn →
      (m1.isCapture || m1.isEnPassant) = true →
      m1.fromSq.fileChar = m2.fromSq.fileChar) := by
  have hne1 := moveToSanBase_toList_ne_nil gs m1 hnc1
  have hne2 := moveToSanBase_toList_ne_nil gs m2 hnc2
  have hhead : (moveToSanBase gs m1).toList.head? = (moveToSanBase gs m2).toList.head? := by
    rw [hbase]
  by_cases hp1 : m1.piece.pieceType = PieceType.Pawn
  · by_cases hp2 : m2.piece.pieceType = PieceType.Pawn
    · -- Both pawns: string decomposition
      unfold moveToSanBase at hbase
      simp only [hnc1, hnc2, hp1, hp2, ↓reduceIte, Bool.false_eq_true] at hbase
      have hlist := congrArg String.toList hbase
      simp only [String.toList_append] at hlist
      -- Case split on capture flags
      by_cases hc1 : (m1.isCapture || m1.isEnPassant) = true <;>
      by_cases hc2 : (m2.isCapture || m2.isEnPassant) = true
      · -- Both captures: [fc1, 'x'] ++ alg1 ++ prom1 = [fc2, 'x'] ++ alg2 ++ prom2
        simp only [hc1, hc2, ↓reduceIte, String.toList_singleton] at hlist
        simp only [List.cons_append, List.nil_append, List.append_assoc] at hlist
        have hfc := (List.cons.inj hlist).1
        have htail := (List.cons.inj (List.cons.inj hlist).2).2
        have halg_len := (algebraic_toList_length m1.toSq).trans (algebraic_toList_length m2.toSq).symm
        have ⟨halg, hprom⟩ := list_append_cancel_left _ _ _ _ halg_len htail
        refine ⟨hp1.trans hp2.symm, algebraic_injective (String.toList_inj.mp halg),
                hc1.trans hc2.symm, promotionSuffix_injective m1 m2 (String.toList_inj.mp hprom),
                (sanDisambiguation_pawn gs m1 hp1).trans (sanDisambiguation_pawn gs m2 hp2).symm,
                fun _ _ => hfc⟩
      · -- m1 capture, m2 non-capture: contradiction via 'x' vs rankChar
        simp only [hc1, hc2, ↓reduceIte, String.toList_singleton, Bool.false_eq_true,
                   String.toList_empty] at hlist
        simp only [List.cons_append, List.nil_append, List.append_assoc] at hlist
        exfalso
        rw [algebraic_toList_form m2.toSq] at hlist
        simp only [List.cons_append] at hlist
        have h2 := (List.cons.inj (List.cons.inj hlist).2).1
        exact rankChar_ne_x m2.toSq h2.symm
      · -- m1 non-capture, m2 capture: contradiction via rankChar vs 'x'
        simp only [hc1, hc2, ↓reduceIte, String.toList_singleton, Bool.false_eq_true,
                   String.toList_empty] at hlist
        simp only [List.cons_append, List.nil_append, List.append_assoc] at hlist
        exfalso
        rw [algebraic_toList_form m1.toSq] at hlist
        simp only [List.cons_append] at hlist
        have h2 := (List.cons.inj (List.cons.inj hlist).2).1
        exact rankChar_ne_x m1.toSq h2
      · -- Both non-captures: alg1 ++ prom1 = alg2 ++ prom2
        simp only [hc1, hc2, ↓reduceIte, Bool.false_eq_true, String.toList_empty] at hlist
        simp only [List.nil_append] at hlist
        have halg_len := (algebraic_toList_length m1.toSq).trans (algebraic_toList_length m2.toSq).symm
        have ⟨halg, hprom⟩ := list_append_cancel_left _ _ _ _ halg_len hlist
        have hc1f : (m1.isCapture || m1.isEnPassant) = false := by
          cases h : m1.isCapture || m1.isEnPassant <;> simp_all
        have hc2f : (m2.isCapture || m2.isEnPassant) = false := by
          cases h : m2.isCapture || m2.isEnPassant <;> simp_all
        refine ⟨hp1.trans hp2.symm, algebraic_injective (String.toList_inj.mp halg),
                hc1f.trans hc2f.symm, promotionSuffix_injective m1 m2 (String.toList_inj.mp hprom),
                (sanDisambiguation_pawn gs m1 hp1).trans (sanDisambiguation_pawn gs m2 hp2).symm,
                fun _ habs => absurd habs (by rw [hc1f]; decide)⟩
    · -- m1 pawn, m2 piece: cross-case contradiction
      exfalso
      let c := (moveToSanBase gs m1).toList.head hne1
      have hc1 : (moveToSanBase gs m1).toList.head? = some c := List.head?_eq_some_head hne1
      have hlow := pawn_san_first_not_upper gs m1 hnc1 hp1 c hc1
      have hc2 : (moveToSanBase gs m2).toList.head? = some c := hhead ▸ hc1
      have hhigh := piece_san_first_upper gs m2 hnc2 hp2 c hc2
      rw [hlow] at hhigh; exact absurd hhigh (by decide)
  · by_cases hp2 : m2.piece.pieceType = PieceType.Pawn
    · -- m1 piece, m2 pawn: cross-case contradiction
      exfalso
      let c := (moveToSanBase gs m2).toList.head hne2
      have hc2 : (moveToSanBase gs m2).toList.head? = some c := List.head?_eq_some_head hne2
      have hlow := pawn_san_first_not_upper gs m2 hnc2 hp2 c hc2
      have hc1 : (moveToSanBase gs m1).toList.head? = some c := hhead.symm ▸ hc2
      have hhigh := piece_san_first_upper gs m1 hnc1 hp1 c hc1
      rw [hlow] at hhigh; exact absurd hhigh (by decide)
    · -- Both pieces: string decomposition using character analysis
      -- piece type: first char (pieceLetter is 1 char, injective)
      -- capture flag: 'x' membership (x_mem_piece_san_iff)
      -- toSq, promo, dis: string decomposition after fixing pl and cap
      -- pawn file char: vacuously true since both are non-pawns
      -- Infrastructure: pieceLetter_injective, x_mem_piece_san_iff,
      --   algebraic_injective, promotionSuffix_injective, sanDisambiguation_chars
      -- Step 1: piece type from first char
      have hpt : m1.piece.pieceType = m2.piece.pieceType := by
        obtain ⟨c1, hc1_list, _⟩ := pieceLetter_first_upper m1.piece.pieceType hp1
        obtain ⟨c2, hc2_list, _⟩ := pieceLetter_first_upper m2.piece.pieceType hp2
        unfold moveToSanBase at hbase
        simp only [hnc1, hnc2, hp1, hp2, ↓reduceIte] at hbase
        have hlist := congrArg String.toList hbase
        simp only [String.toList_append] at hlist
        rw [hc1_list, hc2_list] at hlist
        simp only [List.singleton_append, List.cons_append] at hlist
        have heq_c := (List.cons.inj hlist).1
        apply pieceLetter_injective
        exact String.toList_inj.mp (by rw [hc1_list, hc2_list, heq_c])
      -- Step 2: same capture flag from 'x' membership
      have hcap_eq : (m1.isCapture || m1.isEnPassant) = (m2.isCapture || m2.isEnPassant) := by
        have h1x := x_mem_piece_san_iff gs m1 hnc1 hp1
        have h2x := x_mem_piece_san_iff gs m2 hnc2 hp2
        cases hc1v : m1.isCapture || m1.isEnPassant <;> cases hc2v : m2.isCapture || m2.isEnPassant
        · rfl
        · exfalso
          have hx2 : 'x' ∈ (moveToSanBase gs m2).toList := h2x.mpr rfl
          rw [← hbase] at hx2
          have := h1x.mp hx2
          rw [hc1v] at this; exact absurd this (by decide)
        · exfalso
          have hx1 : 'x' ∈ (moveToSanBase gs m1).toList := h1x.mpr rfl
          rw [hbase] at hx1
          have := h2x.mp hx1
          rw [hc2v] at this; exact absurd this (by decide)
        · rfl
      -- Step 3: unfold both sides and strip the 1-char piece letter from the front
      unfold moveToSanBase at hbase
      simp only [hnc1, hnc2, hp1, hp2, ↓reduceIte] at hbase
      have hlist := congrArg String.toList hbase
      simp only [String.toList_append] at hlist
      obtain ⟨c1, hc1_list, _⟩ := pieceLetter_first_upper m1.piece.pieceType hp1
      obtain ⟨c2, hc2_list, _⟩ := pieceLetter_first_upper m2.piece.pieceType hp2
      rw [hc1_list, hc2_list] at hlist
      simp only [List.singleton_append, List.cons_append] at hlist
      have htail := (List.cons.inj hlist).2
      -- htail: dis1.toList ++ cap_str1.toList ++ alg1.toList ++ prom1.toList =
      --        dis2.toList ++ cap_str2.toList ++ alg2.toList ++ prom2.toList
      -- Since cap flags match, the cap_str strings are identical
      have hcap_str_eq : (if (m1.isCapture || m1.isEnPassant) = true then "x" else ("" : String)) =
                         (if (m2.isCapture || m2.isEnPassant) = true then "x" else "") := by
        rw [hcap_eq]
      -- We also know the cap_str list representations match
      have hcap_list_eq : (if (m1.isCapture || m1.isEnPassant) = true then "x" else ("" : String)).toList =
                          (if (m2.isCapture || m2.isEnPassant) = true then "x" else "").toList := by
        rw [hcap_eq]
      -- Rewrite htail using matched cap_str
      rw [hcap_list_eq] at htail
      -- Now: dis1 ++ cap_str ++ alg1 ++ prom1 = dis2 ++ cap_str ++ alg2 ++ prom2
      -- Reassociate to: (dis1 ++ cap_str) ++ (alg1 ++ prom1) = (dis2 ++ cap_str) ++ (alg2 ++ prom2)
      rw [List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc] at htail
      -- The cap_str ++ alg ++ prom is on the right of dis.
      -- We need to determine lengths. We know:
      -- - alg has length 2
      -- - cap_str has length 0 or 1
      -- - prom has length 0 or 2
      -- Total suffix after dis: cap_str_len + 2 + prom_len
      -- Since both sides have same total length and same cap_str, the suffix lengths match
      -- iff dis lengths match. Let's compute the right part length.
      -- Strategy: the total list has the same length on both sides.
      -- dis1.len + cap.len + alg1.len + prom1.len = dis2.len + cap.len + alg2.len + prom2.len
      -- alg1.len = alg2.len = 2
      -- So: dis1.len + prom1.len = dis2.len + prom2.len
      -- We use: '=' does NOT appear in dis or alg or cap_str, but DOES appear in prom (if any).
      -- promotionSuffix is "" or "=" ++ letter. So the number of '=' chars determines prom.
      -- Count '=' in both sides.
      -- Actually, simpler: we reassociate to split at the algebraic boundary.
      -- Since alg.toList has length 2, and the suffix is alg ++ prom on both sides,
      -- but dis and cap_str are before it. Let's try a different approach:
      -- Reassociate to (dis ++ cap_str) ++ alg ++ prom on both sides, then
      -- count total lengths to match dis lengths.
      -- Actually the simplest approach: note that the '=' character appears ONLY in
      -- promotionSuffix (not in dis, cap_str, or algebraic), so counting '=' chars
      -- gives us that prom1 and prom2 have the same number of '=' chars, hence same length.
      -- But that requires showing '=' is not in sanDisambiguation, algebraic, or "x".
      -- Let's use a more direct approach: work from the RIGHT side of the lists.
      -- The tail is: dis ++ (cap_str ++ alg ++ prom)
      -- Both sides equal. The "suffix" = cap_str ++ alg ++ prom.
      -- We have cap_str same, alg.len = 2, prom.len varies.
      -- Key insight: since both entire lists are equal, their lengths are equal.
      -- So: |dis1| + |cap| + |alg1| + |prom1| = |dis2| + |cap| + |alg2| + |prom2|
      -- Since |alg1| = |alg2| = 2: |dis1| + |prom1| = |dis2| + |prom2|
      -- Now, the prom string starts with '=' if nonempty.
      -- Consider the last 2 chars of the full tail. They come from prom if |prom|=2,
      -- or from alg if |prom|=0. In both cases they encode something specific.
      -- Actually, let's use a cleaner approach. The right part of the list starting from
      -- algebraic is: alg ++ prom. The left part is: dis ++ cap_str.
      -- We need: (dis1 ++ cap_str ++ alg1) ++ prom1 = (dis2 ++ cap_str ++ alg2) ++ prom2
      -- Hmm, this is still tricky without knowing the lengths match.
      -- CLEANEST: show that promotionSuffix length matches by counting '=' chars.
      -- '=' not in sanDisambiguation (fileChar/rankChar, none are '=')
      -- '=' not in "x" or ""
      -- '=' not in algebraic (fileChar 'a'-'h', rankChar '1'-'8')
      -- '=' appears exactly once in promotionSuffix if promotion, 0 times if not.
      -- So: count of '=' in LHS = (0 or 1 from prom1) and same for RHS.
      -- Since the lists are equal, counts match, so prom1 and prom2 are both present or both absent.
      -- When both present, prom_len = 2 in both cases. When both absent, prom_len = 0.
      -- Either way, prom1.len = prom2.len.
      -- Then: |dis1| = |dis2|, and we can use list_append_cancel_left.
      -- Step 3a: show '=' is not in sanDisambiguation, cap_str, or algebraic
      have eq_not_in_dis : ∀ (gs' : GameState) (m' : Move),
          '=' ∉ (sanDisambiguation gs' m').toList := by
        intro gs' m' hmem
        rcases sanDisambiguation_chars gs' m' '=' hmem with h | h
        · have : ∀ (f r : Fin 8), ({ file := f, rank := r } : Square).fileChar ≠ '=' := by native_decide
          exact this m'.fromSq.file m'.fromSq.rank h.symm
        · have : ∀ (f r : Fin 8), ({ file := f, rank := r } : Square).rankChar ≠ '=' := by native_decide
          exact this m'.fromSq.file m'.fromSq.rank h.symm
      have eq_not_in_alg : ∀ (sq' : Square), '=' ∉ sq'.algebraic.toList := by
        intro sq'
        have : ∀ (f r : Fin 8), '=' ∉ ({ file := f, rank := r } : Square).algebraic.toList := by native_decide
        exact this sq'.file sq'.rank
      have eq_not_in_cap : ∀ (b : Bool), '=' ∉ (if b = true then "x" else ("" : String)).toList := by
        intro b; cases b <;> simp <;> native_decide
      -- Step 3b: '=' appears in promotionSuffix iff promotion is some
      have eq_in_prom_iff : ∀ (m' : Move), '=' ∈ (promotionSuffix m').toList ↔ m'.promotion.isSome = true := by
        intro m'
        unfold promotionSuffix
        match m'.promotion with
        | none => simp
        | some pt => simp [String.toList_append]; constructor
                     · intro; rfl
                     · intro; left; cases pt <;> simp [pieceLetter] <;> native_decide
      -- Step 3c: count '=' in both sides to show prom1.isSome = prom2.isSome
      have hprom_isSome : m1.promotion.isSome = m2.promotion.isSome := by
        -- '=' ∈ LHS ↔ '=' ∈ RHS (since the lists are equal)
        have hmem_iff : '=' ∈ (sanDisambiguation gs m1).toList ++
            (if (m2.isCapture || m2.isEnPassant) = true then "x" else ("" : String)).toList ++
            m1.toSq.algebraic.toList ++ (promotionSuffix m1).toList ↔
          '=' ∈ (sanDisambiguation gs m2).toList ++
            (if (m2.isCapture || m2.isEnPassant) = true then "x" else ("" : String)).toList ++
            m2.toSq.algebraic.toList ++ (promotionSuffix m2).toList := by
          rw [htail]
        simp only [List.mem_append] at hmem_iff
        -- '=' is not in dis, cap, or alg, so membership reduces to prom
        have h1_not : '=' ∉ (sanDisambiguation gs m1).toList := eq_not_in_dis gs m1
        have h2_not : '=' ∉ (sanDisambiguation gs m2).toList := eq_not_in_dis gs m2
        have h1_alg_not : '=' ∉ m1.toSq.algebraic.toList := eq_not_in_alg m1.toSq
        have h2_alg_not : '=' ∉ m2.toSq.algebraic.toList := eq_not_in_alg m2.toSq
        have h_cap_not : '=' ∉ (if (m2.isCapture || m2.isEnPassant) = true then "x" else ("" : String)).toList :=
          eq_not_in_cap _
        -- From hmem_iff, strip the non-prom parts
        have : '=' ∈ (promotionSuffix m1).toList ↔ '=' ∈ (promotionSuffix m2).toList := by
          constructor
          · intro hm
            have := hmem_iff.mp (Or.inr hm)
            rcases this with ((h | h) | h) | h
            · exact absurd h h2_not
            · exact absurd h h_cap_not
            · exact absurd h h2_alg_not
            · exact h
          · intro hm
            have := hmem_iff.mpr (Or.inr hm)
            rcases this with ((h | h) | h) | h
            · exact absurd h h1_not
            · exact absurd h h_cap_not
            · exact absurd h h1_alg_not
            · exact h
        rw [eq_in_prom_iff, eq_in_prom_iff] at this
        cases h1p : m1.promotion <;> cases h2p : m2.promotion <;> simp_all
      -- Step 3d: promotionSuffix lengths match
      have hprom_len : (promotionSuffix m1).toList.length = (promotionSuffix m2).toList.length := by
        unfold promotionSuffix
        cases h1p : m1.promotion <;> cases h2p : m2.promotion
        · simp
        · simp [h1p, h2p] at hprom_isSome
        · simp [h1p, h2p] at hprom_isSome
        · simp [String.toList_append]
          cases h1p.get <;> cases h2p.get <;> simp [pieceLetter] <;> native_decide
      -- Step 3e: alg lengths match (both = 2)
      have halg_len : m1.toSq.algebraic.toList.length = m2.toSq.algebraic.toList.length := by
        rw [algebraic_toList_length, algebraic_toList_length]
      -- Step 3f: the right suffix (alg ++ prom) has the same length on both sides
      have hright_len : (m1.toSq.algebraic.toList ++ (promotionSuffix m1).toList).length =
                        (m2.toSq.algebraic.toList ++ (promotionSuffix m2).toList).length := by
        simp [List.length_append, halg_len, hprom_len]
      -- Step 3g: reassociate again to isolate (dis ++ cap_str) from (alg ++ prom)
      have htail2 : (sanDisambiguation gs m1).toList ++
          (if (m2.isCapture || m2.isEnPassant) = true then "x" else ("" : String)).toList ++
          (m1.toSq.algebraic.toList ++ (promotionSuffix m1).toList) =
        (sanDisambiguation gs m2).toList ++
          (if (m2.isCapture || m2.isEnPassant) = true then "x" else ("" : String)).toList ++
          (m2.toSq.algebraic.toList ++ (promotionSuffix m2).toList) := by
        have := htail
        simp only [List.append_assoc] at this ⊢
        exact this
      -- Cancel from the right: left parts match, right parts match
      have ⟨hleft, hright⟩ := list_append_cancel_right
        ((sanDisambiguation gs m1).toList ++ (if (m2.isCapture || m2.isEnPassant) = true then "x" else ("" : String)).toList)
        (m1.toSq.algebraic.toList ++ (promotionSuffix m1).toList)
        ((sanDisambiguation gs m2).toList ++ (if (m2.isCapture || m2.isEnPassant) = true then "x" else ("" : String)).toList)
        (m2.toSq.algebraic.toList ++ (promotionSuffix m2).toList)
        hright_len htail2
      -- From hright, split alg and prom
      have ⟨halg_eq, hprom_eq⟩ := list_append_cancel_left
        m1.toSq.algebraic.toList (promotionSuffix m1).toList
        m2.toSq.algebraic.toList (promotionSuffix m2).toList
        halg_len hright
      -- From hleft, extract dis equality (cap_str is same, acts as suffix)
      have hcap_len : (if (m2.isCapture || m2.isEnPassant) = true then "x" else ("" : String)).toList.length =
                      (if (m2.isCapture || m2.isEnPassant) = true then "x" else ("" : String)).toList.length := rfl
      have ⟨hdis_eq, _⟩ := list_append_cancel_right
        (sanDisambiguation gs m1).toList
        (if (m2.isCapture || m2.isEnPassant) = true then "x" else ("" : String)).toList
        (sanDisambiguation gs m2).toList
        (if (m2.isCapture || m2.isEnPassant) = true then "x" else ("" : String)).toList
        hcap_len hleft
      -- Assemble the 6 conclusions
      exact ⟨hpt,
             algebraic_injective (String.toList_inj.mp halg_eq),
             hcap_eq,
             promotionSuffix_injective m1 m2 (String.toList_inj.mp hprom_eq),
             String.toList_inj.mp hdis_eq,
             fun h _ => absurd h hp1⟩

-- ============================================================================
-- SECTION 7: DISAMBIGUATION UNIQUENESS
-- ============================================================================

/-- fileChar values ('a'-'h') are distinct from rankChar values ('1'-'8') -/
private theorem fileChar_ne_rankChar (f r : Fin 8) :
    (Char.ofNat ('a'.toNat + f.val)) ≠ (Char.ofNat ('1'.toNat + r.val)) := by
  have : ∀ (f r : Fin 8),
    (Char.ofNat ('a'.toNat + f.val)) ≠ (Char.ofNat ('1'.toNat + r.val)) := by native_decide
  exact this f r

/-- rankChar is determined by rank -/
private theorem rankChar_form (sq : Square) :
    sq.rankChar = Char.ofNat ('1'.toNat + sq.rank.val) := by
  have : ∀ (f r : Fin 8),
    ({ file := f, rank := r } : Square).rankChar = Char.ofNat ('1'.toNat + r.val) := by native_decide
  exact this sq.file sq.rank

/-- fileChar is determined by file -/
private theorem fileChar_form (sq : Square) :
    sq.fileChar = Char.ofNat ('a'.toNat + sq.file.val) := by
  have : ∀ (f r : Fin 8),
    ({ file := f, rank := r } : Square).fileChar = Char.ofNat ('a'.toNat + f.val) := by native_decide
  exact this sq.file sq.rank

/-- sanDisambiguation length for non-pawn moves with non-empty peers -/
private theorem sanDisambiguation_length_cases (gs : GameState) (m : Move)
    (hnp : m.piece.pieceType ≠ PieceType.Pawn)
    (hpeers : ¬ ((Rules.allLegalMoves gs).filter fun cand =>
      cand.piece.pieceType = m.piece.pieceType ∧
      cand.piece.color = m.piece.color ∧
      cand.toSq = m.toSq ∧
      cand.fromSq ≠ m.fromSq).isEmpty) :
    (sanDisambiguation gs m = String.singleton m.fromSq.fileChar ∧
     ¬((Rules.allLegalMoves gs).filter fun cand =>
        cand.piece.pieceType = m.piece.pieceType ∧
        cand.piece.color = m.piece.color ∧
        cand.toSq = m.toSq ∧
        cand.fromSq ≠ m.fromSq).any (fun p => decide (p.fromSq.file = m.fromSq.file))) ∨
    (sanDisambiguation gs m = String.singleton m.fromSq.rankChar ∧
     ((Rules.allLegalMoves gs).filter fun cand =>
        cand.piece.pieceType = m.piece.pieceType ∧
        cand.piece.color = m.piece.color ∧
        cand.toSq = m.toSq ∧
        cand.fromSq ≠ m.fromSq).any (fun p => decide (p.fromSq.file = m.fromSq.file)) ∧
     ¬((Rules.allLegalMoves gs).filter fun cand =>
        cand.piece.pieceType = m.piece.pieceType ∧
        cand.piece.color = m.piece.color ∧
        cand.toSq = m.toSq ∧
        cand.fromSq ≠ m.fromSq).any (fun p => decide (p.fromSq.rank = m.fromSq.rank))) ∨
    (sanDisambiguation gs m = String.singleton m.fromSq.fileChar ++ String.singleton m.fromSq.rankChar) := by
  unfold sanDisambiguation
  simp only [hnp, ↓reduceIte]
  generalize (Rules.allLegalMoves gs |>.filter _) = peers at hpeers ⊢
  have hne : peers.isEmpty = false := by cases h : peers.isEmpty <;> simp_all
  simp only [hne, Bool.false_eq_true, ↓reduceIte]
  generalize peers.any (fun p => decide (p.fromSq.file = m.fromSq.file)) = fc
  generalize peers.any (fun p => decide (p.fromSq.rank = m.fromSq.rank)) = rc
  cases fc <;> cases rc <;> simp_all [Bool.not_eq_true']

private theorem same_disambiguation_implies_same_fromSq (gs : GameState) (m1 m2 : Move)
    (h1 : m1 ∈ Rules.allLegalMoves gs) (h2 : m2 ∈ Rules.allLegalMoves gs)
    (hpt : m1.piece.pieceType = m2.piece.pieceType)
    (hcolor : m1.piece.color = m2.piece.color)
    (htoSq : m1.toSq = m2.toSq)
    (hdis : sanDisambiguation gs m1 = sanDisambiguation gs m2)
    (hnp : m1.piece.pieceType ≠ PieceType.Pawn) :
    m1.fromSq = m2.fromSq := by
  -- Decide equality; if equal we're done
  by_cases hneq : m1.fromSq = m2.fromSq
  · exact hneq
  -- fromSq1 ≠ fromSq2: derive contradiction from disambiguation equality
  exfalso
  -- m2 is a peer of m1 (same type, color, target, different source)
  have hm2_peer : m2 ∈ (Rules.allLegalMoves gs).filter (fun cand =>
      cand.piece.pieceType = m1.piece.pieceType ∧
      cand.piece.color = m1.piece.color ∧
      cand.toSq = m1.toSq ∧
      cand.fromSq ≠ m1.fromSq) := by
    rw [List.mem_filter]
    exact ⟨h2, hpt.symm, hcolor.symm, htoSq.symm, Ne.symm hneq⟩
  -- m1 is a peer of m2
  have hm1_peer : m1 ∈ (Rules.allLegalMoves gs).filter (fun cand =>
      cand.piece.pieceType = m2.piece.pieceType ∧
      cand.piece.color = m2.piece.color ∧
      cand.toSq = m2.toSq ∧
      cand.fromSq ≠ m2.fromSq) := by
    rw [List.mem_filter]
    exact ⟨h1, hpt, hcolor, htoSq, hneq⟩
  -- Both peer lists are non-empty
  have hpeers1_ne : ¬((Rules.allLegalMoves gs).filter (fun cand =>
      cand.piece.pieceType = m1.piece.pieceType ∧
      cand.piece.color = m1.piece.color ∧
      cand.toSq = m1.toSq ∧
      cand.fromSq ≠ m1.fromSq)).isEmpty := by
    simp [List.isEmpty_iff, List.eq_nil_iff_forall_not_mem] at *
    exact ⟨m2, hm2_peer⟩
  have hnp2 : m2.piece.pieceType ≠ PieceType.Pawn := hpt.symm ▸ hnp
  have hpeers2_ne : ¬((Rules.allLegalMoves gs).filter (fun cand =>
      cand.piece.pieceType = m2.piece.pieceType ∧
      cand.piece.color = m2.piece.color ∧
      cand.toSq = m2.toSq ∧
      cand.fromSq ≠ m2.fromSq)).isEmpty := by
    simp [List.isEmpty_iff, List.eq_nil_iff_forall_not_mem] at *
    exact ⟨m1, hm1_peer⟩
  -- Get the 3-way case split for each disambiguation
  have hcases1 := sanDisambiguation_length_cases gs m1 hnp hpeers1_ne
  have hcases2 := sanDisambiguation_length_cases gs m2 hnp2 hpeers2_ne
  -- m2 is in peers of m1, check if it contributes to file/rank conflict
  -- Helper: m2 being a peer of m1 with same file means file conflict for m1
  have file_conflict_1_of_same_file : m1.fromSq.file = m2.fromSq.file →
      ((Rules.allLegalMoves gs).filter (fun cand =>
        cand.piece.pieceType = m1.piece.pieceType ∧
        cand.piece.color = m1.piece.color ∧
        cand.toSq = m1.toSq ∧
        cand.fromSq ≠ m1.fromSq)).any (fun p => decide (p.fromSq.file = m1.fromSq.file)) = true := by
    intro hf
    apply List.any_of_mem hm2_peer
    simp [hf]
  have file_conflict_2_of_same_file : m1.fromSq.file = m2.fromSq.file →
      ((Rules.allLegalMoves gs).filter (fun cand =>
        cand.piece.pieceType = m2.piece.pieceType ∧
        cand.piece.color = m2.piece.color ∧
        cand.toSq = m2.toSq ∧
        cand.fromSq ≠ m2.fromSq)).any (fun p => decide (p.fromSq.file = m2.fromSq.file)) = true := by
    intro hf
    apply List.any_of_mem hm1_peer
    simp [hf]
  have rank_conflict_1_of_same_rank : m1.fromSq.rank = m2.fromSq.rank →
      ((Rules.allLegalMoves gs).filter (fun cand =>
        cand.piece.pieceType = m1.piece.pieceType ∧
        cand.piece.color = m1.piece.color ∧
        cand.toSq = m1.toSq ∧
        cand.fromSq ≠ m1.fromSq)).any (fun p => decide (p.fromSq.rank = m1.fromSq.rank)) = true := by
    intro hr
    apply List.any_of_mem hm2_peer
    simp [hr]
  have rank_conflict_2_of_same_rank : m1.fromSq.rank = m2.fromSq.rank →
      ((Rules.allLegalMoves gs).filter (fun cand =>
        cand.piece.pieceType = m2.piece.pieceType ∧
        cand.piece.color = m2.piece.color ∧
        cand.toSq = m2.toSq ∧
        cand.fromSq ≠ m2.fromSq)).any (fun p => decide (p.fromSq.rank = m2.fromSq.rank)) = true := by
    intro hr
    apply List.any_of_mem hm1_peer
    simp [hr]
  -- Now case split on the 9 combinations
  rcases hcases1 with ⟨hd1, hnofc1⟩ | ⟨hd1, hfc1, hnorc1⟩ | hd1 <;>
  rcases hcases2 with ⟨hd2, hnofc2⟩ | ⟨hd2, hfc2, hnorc2⟩ | hd2
  · -- (file, file): fileChar(m1) = fileChar(m2) → same file → file conflict for m1. Contradiction.
    rw [hd1, hd2] at hdis
    have := String.toList_inj.mpr hdis
    simp [String.toList_singleton] at this
    have hf := fileChar_injective this
    exact absurd (file_conflict_1_of_same_file hf) (by simp_all)
  · -- (file, rank): fileChar = rankChar → impossible (disjoint ranges)
    rw [hd1, hd2] at hdis
    have := String.toList_inj.mpr hdis
    simp [String.toList_singleton] at this
    rw [fileChar_form, rankChar_form] at this
    exact absurd this (fileChar_ne_rankChar m1.fromSq.file m2.fromSq.rank)
  · -- (file, full): length 1 ≠ 2. Contradiction.
    rw [hd1, hd2] at hdis
    have := congrArg String.length hdis
    simp [String.length_singleton, String.length_append] at this
  · -- (rank, file): fileChar = rankChar → impossible
    rw [hd1, hd2] at hdis
    have := String.toList_inj.mpr hdis
    simp [String.toList_singleton] at this
    rw [fileChar_form, rankChar_form] at this
    exact absurd this.symm (fileChar_ne_rankChar m2.fromSq.file m1.fromSq.rank)
  · -- (rank, rank): rankChar(m1) = rankChar(m2) → same rank → rank conflict for m1. Contradiction.
    rw [hd1, hd2] at hdis
    have := String.toList_inj.mpr hdis
    simp [String.toList_singleton] at this
    have hr := rankChar_injective this
    exact absurd (rank_conflict_1_of_same_rank hr) (by simp_all)
  · -- (rank, full): length 1 ≠ 2. Contradiction.
    rw [hd1, hd2] at hdis
    have := congrArg String.length hdis
    simp [String.length_singleton, String.length_append] at this
  · -- (full, file): length 2 ≠ 1. Contradiction.
    rw [hd1, hd2] at hdis
    have := congrArg String.length hdis
    simp [String.length_singleton, String.length_append] at this
  · -- (full, rank): length 2 ≠ 1. Contradiction.
    rw [hd1, hd2] at hdis
    have := congrArg String.length hdis
    simp [String.length_singleton, String.length_append] at this
  · -- (full, full): fileChar(m1)++rankChar(m1) = fileChar(m2)++rankChar(m2) → same file, rank → same sq
    rw [hd1, hd2] at hdis
    have hlist := congrArg String.toList hdis
    simp [String.toList_append, String.toList_singleton] at hlist
    have hf := fileChar_injective (List.cons.inj hlist).1
    have hr := rankChar_injective ((List.cons.inj (List.cons.inj hlist).2).1)
    exact hneq (Square.ext hf hr)

-- ============================================================================
-- SECTION 8: CAPTURE/EP FLAGS FROM LEGALITY
-- ============================================================================

-- Helper: walk-generated moves have isEnPassant = false
private theorem walk_ep_false (src : Square) (p : Piece) (board : Board) (color : Color)
    (maxStep : Nat) (df dr : Int) (step : Nat) (acc : List Move)
    (hacc : ∀ m ∈ acc, m.isEnPassant = false)
    (m : Move)
    (hmem : m ∈ Rules.slidingTargets.walk src p board color maxStep df dr step acc) :
    m.isEnPassant = false := by
  induction step generalizing acc with
  | zero => simp only [Rules.slidingTargets.walk] at hmem; exact hacc m hmem
  | succ s ih =>
    simp only [Rules.slidingTargets.walk] at hmem
    cases h1 : Movement.squareFromInts (src.fileInt + df * (Int.ofNat (maxStep - s)))
        (src.rankInt + dr * (Int.ofNat (maxStep - s))) with
    | none => simp only [h1] at hmem; exact hacc m hmem
    | some target =>
      simp only [h1] at hmem
      by_cases he : Rules.isEmpty board target = true
      · simp only [he, ↓reduceIte] at hmem
        apply ih _ _ hmem
        intro mx hmx
        simp only [List.mem_cons] at hmx
        rcases hmx with rfl | hmx'
        · rfl
        · exact hacc mx hmx'
      · simp only [he, Bool.false_eq_true, ↓reduceIte] at hmem
        by_cases hc : Rules.isEnemyAt board color target = true
        · simp only [hc, ↓reduceIte] at hmem
          rw [List.mem_cons] at hmem
          rcases hmem with rfl | h'
          · rfl
          · exact hacc _ h'
        · simp only [hc, Bool.false_eq_true, ↓reduceIte] at hmem; exact hacc _ hmem

-- Helper: foldr of walk: isEnPassant = false
private theorem foldr_walk_ep_false (src : Square) (p : Piece) (board : Board)
    (color : Color) (maxStep : Nat) (deltas : List (Int × Int)) (m : Move)
    (hmem : m ∈ deltas.foldr (fun d acc =>
      Rules.slidingTargets.walk src p board color maxStep d.fst d.snd maxStep acc) []) :
    m.isEnPassant = false := by
  induction deltas generalizing m with
  | nil => simp at hmem
  | cons d rest ih =>
    simp only [List.foldr_cons] at hmem
    exact walk_ep_false src p board color maxStep d.fst d.snd maxStep
      _ (fun m' hm' => ih m' hm') m hmem

-- Helper: filterMap-generated moves: isEnPassant = false
private theorem filterMap_ep_false (gs : GameState) (sq : Square) (p : Piece)
    (targets : List Square) (m : Move)
    (hmem : m ∈ targets.filterMap (fun target =>
      if Rules.destinationFriendlyFree gs { piece := p, fromSq := sq, toSq := target } then
        match gs.board target with
        | some _ => some { piece := p, fromSq := sq, toSq := target, isCapture := true }
        | none => some { piece := p, fromSq := sq, toSq := target }
      else none)) :
    m.isEnPassant = false := by
  obtain ⟨target, _, hfm⟩ := List.mem_filterMap.mp hmem
  by_cases hdest : Rules.destinationFriendlyFree gs { piece := p, fromSq := sq, toSq := target } = true
  · simp only [hdest, ↓reduceIte] at hfm
    split at hfm <;> (injection hfm with h; subst h; rfl)
  · simp only [hdest, Bool.false_eq_true, ↓reduceIte] at hfm; simp at hfm

-- Helper: promotionMoves preserves isEnPassant
private theorem promotionMoves_ep (m m' : Move)
    (hm : m.isEnPassant = false) :
    m' ∈ Rules.promotionMoves m → m'.isEnPassant = false := by
  intro hmem; unfold Rules.promotionMoves at hmem
  split at hmem
  · simp only [List.mem_map] at hmem; obtain ⟨_, _, heq⟩ := hmem; subst heq; exact hm
  · simp only [List.mem_singleton] at hmem; subst hmem; exact hm

-- Helper: pawn forward moves: isEnPassant = false
private theorem pawn_fwd_ep_false (gs : GameState) (src : Square) (p : Piece) (m : Move)
    (hmem : m ∈ (match Movement.squareFromInts src.fileInt (src.rankInt + Movement.pawnDirection p.color) with
      | some target =>
          if Rules.isEmpty gs.board target then
            [{ piece := p, fromSq := src, toSq := target : Move }] ++
            (if src.rankNat = Rules.pawnStartRank p.color then
              match Movement.squareFromInts src.fileInt (src.rankInt + 2 * Movement.pawnDirection p.color) with
              | some target2 =>
                  if Rules.isEmpty gs.board target2 then
                    [{ piece := p, fromSq := src, toSq := target2 : Move }]
                  else []
              | none => []
            else [])
          else []
      | none => [])) :
    m.isEnPassant = false := by
  cases h1 : Movement.squareFromInts src.fileInt (src.rankInt + Movement.pawnDirection p.color) with
  | none => simp only [h1] at hmem; simp at hmem
  | some target =>
    simp only [h1] at hmem
    by_cases he : Rules.isEmpty gs.board target = true
    · simp only [he, ↓reduceIte] at hmem
      rw [List.mem_append] at hmem
      rcases hmem with hb | hd
      · simp only [List.mem_singleton] at hb; subst hb; rfl
      · by_cases hr : src.rankNat = Rules.pawnStartRank p.color
        · simp only [hr, ↓reduceIte] at hd
          cases h2 : Movement.squareFromInts src.fileInt (src.rankInt + 2 * Movement.pawnDirection p.color) with
          | none => simp only [h2] at hd; simp at hd
          | some t2 =>
            simp only [h2] at hd
            by_cases he2 : Rules.isEmpty gs.board t2 = true
            · simp only [he2, ↓reduceIte, List.mem_singleton] at hd; subst hd; rfl
            · simp only [he2, Bool.false_eq_true, ↓reduceIte, List.not_mem_nil] at hd
        · simp only [hr, ↓reduceIte, List.not_mem_nil] at hd
    · simp only [he, Bool.false_eq_true, ↓reduceIte, List.not_mem_nil] at hmem

-- Helper: pawn EP moves from capture generation have empty target
private theorem pawn_cap_ep_board_empty (gs : GameState) (src : Square) (p : Piece) (m : Move)
    (hmem : m ∈ ([-1, 1] : List Int).foldr
        (fun df acc =>
          match Movement.squareFromInts (src.fileInt + df) (src.rankInt + Movement.pawnDirection p.color) with
          | some target =>
              if Rules.isEnemyAt gs.board p.color target then
                Rules.promotionMoves { piece := p, fromSq := src, toSq := target, isCapture := true } ++ acc
              else if gs.enPassantTarget = some target ∧ Rules.isEmpty gs.board target then
                { piece := p, fromSq := src, toSq := target, isCapture := true, isEnPassant := true } :: acc
              else acc
          | none => acc)
        [])
    (hep : m.isEnPassant = true) :
    Rules.isEmpty gs.board m.toSq = true := by
  simp only [List.foldr_cons, List.foldr_nil] at hmem
  -- Process df = -1 and df = 1
  cases h1 : Movement.squareFromInts (src.fileInt + (-1)) (src.rankInt + Movement.pawnDirection p.color) with
  | none =>
    simp only [h1] at hmem
    cases h2 : Movement.squareFromInts (src.fileInt + 1) (src.rankInt + Movement.pawnDirection p.color) with
    | none => simp only [h2] at hmem; simp at hmem
    | some t2 =>
      simp only [h2] at hmem
      by_cases he2 : Rules.isEnemyAt gs.board p.color t2 = true
      · simp only [he2, ↓reduceIte, List.append_nil] at hmem
        have := promotionMoves_ep _ m rfl hmem; rw [this] at hep; exact absurd hep (by decide)
      · simp only [he2, Bool.false_eq_true, ↓reduceIte] at hmem
        by_cases hep2 : gs.enPassantTarget = some t2 ∧ Rules.isEmpty gs.board t2
        · rw [if_pos hep2] at hmem; simp only [List.mem_singleton] at hmem; subst hmem; exact hep2.2
        · rw [if_neg hep2] at hmem; simp at hmem
  | some t1 =>
    simp only [h1] at hmem
    by_cases he1 : Rules.isEnemyAt gs.board p.color t1 = true
    · simp only [he1, ↓reduceIte] at hmem
      rw [List.mem_append] at hmem
      rcases hmem with hp1 | hrest
      · have := promotionMoves_ep _ m rfl hp1; rw [this] at hep; exact absurd hep (by decide)
      · -- Process df = 1
        cases h2 : Movement.squareFromInts (src.fileInt + 1) (src.rankInt + Movement.pawnDirection p.color) with
        | none => simp only [h2] at hrest; simp at hrest
        | some t2 =>
          simp only [h2] at hrest
          by_cases he2 : Rules.isEnemyAt gs.board p.color t2 = true
          · simp only [he2, ↓reduceIte, List.append_nil] at hrest
            have := promotionMoves_ep _ m rfl hrest; rw [this] at hep; exact absurd hep (by decide)
          · simp only [he2, Bool.false_eq_true, ↓reduceIte] at hrest
            by_cases hep2 : gs.enPassantTarget = some t2 ∧ Rules.isEmpty gs.board t2
            · rw [if_pos hep2] at hrest; simp only [List.mem_singleton] at hrest; subst hrest; exact hep2.2
            · rw [if_neg hep2] at hrest; simp at hrest
    · simp only [he1, Bool.false_eq_true, ↓reduceIte] at hmem
      by_cases hep1 : gs.enPassantTarget = some t1 ∧ Rules.isEmpty gs.board t1
      · rw [if_pos hep1] at hmem
        rw [List.mem_cons] at hmem
        rcases hmem with rfl | hrest
        · exact hep1.2
        · -- Process df = 1
          cases h2 : Movement.squareFromInts (src.fileInt + 1) (src.rankInt + Movement.pawnDirection p.color) with
          | none => simp only [h2] at hrest; simp at hrest
          | some t2 =>
            simp only [h2] at hrest
            by_cases he2 : Rules.isEnemyAt gs.board p.color t2 = true
            · simp only [he2, ↓reduceIte, List.append_nil] at hrest
              have := promotionMoves_ep _ m rfl hrest; rw [this] at hep; exact absurd hep (by decide)
            · simp only [he2, Bool.false_eq_true, ↓reduceIte] at hrest
              by_cases hep2 : gs.enPassantTarget = some t2 ∧ Rules.isEmpty gs.board t2
              · rw [if_pos hep2] at hrest; simp only [List.mem_singleton] at hrest; subst hrest; exact hep2.2
              · rw [if_neg hep2] at hrest; simp at hrest
      · rw [if_neg hep1] at hmem
        -- Process df = 1
        cases h2 : Movement.squareFromInts (src.fileInt + 1) (src.rankInt + Movement.pawnDirection p.color) with
        | none => simp only [h2] at hmem; simp at hmem
        | some t2 =>
          simp only [h2] at hmem
          by_cases he2 : Rules.isEnemyAt gs.board p.color t2 = true
          · simp only [he2, ↓reduceIte, List.append_nil] at hmem
            have := promotionMoves_ep _ m rfl hmem; rw [this] at hep; exact absurd hep (by decide)
          · simp only [he2, Bool.false_eq_true, ↓reduceIte] at hmem
            by_cases hep2 : gs.enPassantTarget = some t2 ∧ Rules.isEmpty gs.board t2
            · rw [if_pos hep2] at hmem; simp only [List.mem_singleton] at hmem; subst hmem; exact hep2.2
            · rw [if_neg hep2] at hmem; simp at hmem

-- Helper: foldr of promotionMoves preserves ep=false
private theorem foldr_promotionMoves_ep_false (moves : List Move) (m : Move)
    (hbase : ∀ mb ∈ moves, mb.isEnPassant = false)
    (hmem : m ∈ moves.foldr (fun mv acc => Rules.promotionMoves mv ++ acc) []) :
    m.isEnPassant = false := by
  induction moves with
  | nil => simp at hmem
  | cons x xs ih =>
    simp only [List.foldr_cons] at hmem
    rw [List.mem_append] at hmem
    rcases hmem with hp | hrest
    · exact promotionMoves_ep x m (hbase x (List.mem_cons_self)) hp
    · exact ih (fun mb hm => hbase mb (List.mem_cons.mpr (Or.inr hm))) hrest

-- Helper: castleMoveIfLegal produces moves with isEnPassant = false
private theorem castleMoveIfLegal_ep_false (gs : GameState) (kingSide : Bool) (m : Move) :
    castleMoveIfLegal gs kingSide = some m → m.isEnPassant = false := by
  intro h; unfold castleMoveIfLegal at h
  simp only [Bool.and_eq_true] at h
  split at h
  case isTrue =>
    split at h
    case h_1 k r _ _ =>
      split at h
      case isTrue => split at h
                     case isTrue => injection h with h; subst h; rfl
                     case isFalse => simp at h
      case isFalse => simp at h
    case h_2 => simp at h
  case isFalse => simp at h

-- Helper: pieceTargets EP moves have empty target
private theorem pieceTargets_ep_board_empty (gs : GameState) (sq : Square) (p : Piece) (m : Move)
    (hmem : m ∈ Rules.pieceTargets gs sq p)
    (hep : m.isEnPassant = true) :
    Rules.isEmpty gs.board m.toSq = true := by
  unfold Rules.pieceTargets at hmem
  cases hp : p.pieceType with
  | King =>
    simp only [hp] at hmem
    rw [List.mem_append] at hmem
    rcases hmem with hstd | hcastle
    · exact absurd (filterMap_ep_false gs sq p _ m hstd) (by rw [hep]; decide)
    · obtain ⟨opt, hopt_mem, hopt_eq⟩ := List.mem_filterMap.mp hcastle
      simp only [id_eq] at hopt_eq
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hopt_mem
      rcases hopt_mem with rfl | rfl
      · exact absurd (castleMoveIfLegal_ep_false gs true m hopt_eq) (by rw [hep]; decide)
      · exact absurd (castleMoveIfLegal_ep_false gs false m hopt_eq) (by rw [hep]; decide)
  | Queen =>
    simp only [hp] at hmem; unfold Rules.slidingTargets at hmem
    exact absurd (foldr_walk_ep_false sq p gs.board p.color 7 _ m hmem) (by rw [hep]; decide)
  | Rook =>
    simp only [hp] at hmem; unfold Rules.slidingTargets at hmem
    exact absurd (foldr_walk_ep_false sq p gs.board p.color 7 _ m hmem) (by rw [hep]; decide)
  | Bishop =>
    simp only [hp] at hmem; unfold Rules.slidingTargets at hmem
    exact absurd (foldr_walk_ep_false sq p gs.board p.color 7 _ m hmem) (by rw [hep]; decide)
  | Knight =>
    simp only [hp] at hmem
    exact absurd (filterMap_ep_false gs sq p _ m hmem) (by rw [hep]; decide)
  | Pawn =>
    simp only [hp] at hmem
    rw [List.mem_append] at hmem
    rcases hmem with hfwd | hcap
    · exact absurd (foldr_promotionMoves_ep_false _ m
        (fun mb hm => pawn_fwd_ep_false gs sq p mb hm) hfwd) (by rw [hep]; decide)
    · exact pawn_cap_ep_board_empty gs sq p m hcap hep

-- Helper: legal EP moves have empty target
private theorem legal_ep_board_empty (gs : GameState) (m : Move)
    (hmem : m ∈ Rules.allLegalMoves gs) (hep : m.isEnPassant = true) :
    Rules.isEmpty gs.board m.toSq = true := by
  unfold Rules.allLegalMoves at hmem
  have ⟨sq, _, hsq⟩ := mem_foldr_append
    (fun sq => Rules.legalMovesForCached gs sq (Rules.pinnedSquares gs gs.toMove))
    allSquares m hmem
  unfold Rules.legalMovesForCached at hsq
  cases hbd : gs.board sq with
  | none => simp only [hbd, List.not_mem_nil] at hsq
  | some p =>
    simp only [hbd] at hsq
    by_cases hcolor : p.color ≠ gs.toMove
    · rw [if_pos hcolor] at hsq; simp at hsq
    · rw [if_neg hcolor] at hsq
      have h1 := List.mem_filter.mp hsq
      have h2 := List.mem_filter.mp h1.1
      exact pieceTargets_ep_board_empty gs sq p m h2.1 hep

-- Helper: legal moves satisfy captureFlagConsistent
private theorem legal_captureFlagConsistent (gs : GameState) (m : Move)
    (hmem : m ∈ Rules.allLegalMoves gs) :
    Rules.captureFlagConsistent gs m = true := by
  unfold Rules.allLegalMoves at hmem
  have ⟨sq, _, hsq⟩ := mem_foldr_append
    (fun sq => Rules.legalMovesForCached gs sq (Rules.pinnedSquares gs gs.toMove))
    allSquares m hmem
  unfold Rules.legalMovesForCached at hsq
  cases hbd : gs.board sq with
  | none => simp only [hbd, List.not_mem_nil] at hsq
  | some p =>
    simp only [hbd] at hsq
    by_cases hcolor : p.color ≠ gs.toMove
    · rw [if_pos hcolor] at hsq; simp at hsq
    · rw [if_neg hcolor] at hsq
      have hmem' := List.mem_filter.mp hsq
      have hblas := hmem'.2
      have hbml := Rules.basicLegalAndSafe_implies_basicMoveLegalBool gs m hblas
      unfold Rules.basicMoveLegalBool at hbml
      simp only [Bool.and_eq_true] at hbml
      obtain ⟨⟨⟨⟨_, _⟩, _⟩, hcfc⟩, _⟩ := hbml
      exact hcfc

/-- Two legal moves to the same square with the same capture-or-ep flag
    have the same isCapture and isEnPassant fields individually.
    This follows from move generation: isCapture and isEnPassant are determined
    by the board state at the target square. -/
private theorem legal_same_toSq_implies_same_capture_ep (gs : GameState) (m1 m2 : Move)
    (h1 : m1 ∈ Rules.allLegalMoves gs) (h2 : m2 ∈ Rules.allLegalMoves gs)
    (htoSq : m1.toSq = m2.toSq)
    (hcap_or : (m1.isCapture || m1.isEnPassant) = (m2.isCapture || m2.isEnPassant)) :
    m1.isCapture = m2.isCapture ∧ m1.isEnPassant = m2.isEnPassant := by
  have hcfc1 := legal_captureFlagConsistent gs m1 h1
  have hcfc2 := legal_captureFlagConsistent gs m2 h2
  -- captureFlagConsistent: ep=T → cap=T; ep=F → (board some → cap=T, board none → cap=F)
  -- First eliminate (cap=F,ep=T) cases using captureFlagConsistent
  have hep1_cap1 : m1.isEnPassant = true → m1.isCapture = true := by
    intro hep; unfold Rules.captureFlagConsistent at hcfc1; rw [hep] at hcfc1
    simp at hcfc1; exact hcfc1
  have hep2_cap2 : m2.isEnPassant = true → m2.isCapture = true := by
    intro hep; unfold Rules.captureFlagConsistent at hcfc2; rw [hep] at hcfc2
    simp at hcfc2; exact hcfc2
  -- For non-EP captures, board determines capture flag
  have hnoep1_board : m1.isEnPassant = false → m1.isCapture = true →
      ∃ p, gs.board m1.toSq = some p := by
    intro hep hcap; unfold Rules.captureFlagConsistent at hcfc1; rw [hep] at hcfc1
    simp at hcfc1; cases hbd : gs.board m1.toSq with
    | none => simp [hbd] at hcfc1; rw [hcfc1] at hcap; exact absurd hcap (by decide)
    | some p => exact ⟨p, rfl⟩
  have hnoep2_board : m2.isEnPassant = false → m2.isCapture = true →
      ∃ p, gs.board m2.toSq = some p := by
    intro hep hcap; unfold Rules.captureFlagConsistent at hcfc2; rw [hep] at hcfc2
    simp at hcfc2; cases hbd : gs.board m2.toSq with
    | none => simp [hbd] at hcfc2; rw [hcfc2] at hcap; exact absurd hcap (by decide)
    | some p => exact ⟨p, rfl⟩
  cases hc1 : m1.isCapture <;> cases he1 : m1.isEnPassant <;>
  cases hc2 : m2.isCapture <;> cases he2 : m2.isEnPassant
  -- 16 cases, most eliminated by hcap_or or captureFlagConsistent
  · exact ⟨rfl, rfl⟩  -- (F,F,F,F)
  · simp [hc1, he1, hc2, he2] at hcap_or  -- (F,F,F,T): OR mismatch
  · simp [hc1, he1, hc2, he2] at hcap_or  -- (F,F,T,F): OR mismatch
  · simp [hc1, he1, hc2, he2] at hcap_or  -- (F,F,T,T): OR mismatch
  · exact absurd hc1 (by rw [hep1_cap1 he1]; decide)  -- (F,T,...): cap=F but ep=T→cap=T
  · exact absurd hc1 (by rw [hep1_cap1 he1]; decide)  -- (F,T,...): cap=F but ep=T→cap=T
  · exact absurd hc1 (by rw [hep1_cap1 he1]; decide)  -- (F,T,...): cap=F but ep=T→cap=T
  · exact absurd hc1 (by rw [hep1_cap1 he1]; decide)  -- (F,T,...): cap=F but ep=T→cap=T
  · simp [hc1, he1, hc2, he2] at hcap_or  -- (T,F,F,F): OR mismatch
  · exact absurd hc2 (by rw [hep2_cap2 he2]; decide)  -- (...,F,T): cap=F but ep=T→cap=T
  · exact ⟨rfl, rfl⟩  -- (T,F,T,F)
  · -- (T,F,T,T): m1 ep=F,cap=T → board occupied; m2 ep=T → board empty. Contradiction.
    exfalso
    have ⟨p, hbd⟩ := hnoep1_board he1 hc1
    have hemp := legal_ep_board_empty gs m2 h2 he2
    rw [← htoSq] at hemp; simp [Rules.isEmpty, hbd] at hemp
  · simp [hc1, he1, hc2, he2] at hcap_or  -- (T,T,F,F): OR mismatch
  · exact absurd hc2 (by rw [hep2_cap2 he2]; decide)  -- (...,F,T): cap=F but ep=T→cap=T
  · -- (T,T,T,F): m2 ep=F,cap=T → board occupied; m1 ep=T → board empty. Contradiction.
    exfalso
    have ⟨p, hbd⟩ := hnoep2_board he2 hc2
    have hemp := legal_ep_board_empty gs m1 h1 he1
    rw [htoSq] at hemp; simp [Rules.isEmpty, hbd] at hemp
  · exact ⟨rfl, rfl⟩  -- (T,T,T,T)

-- ============================================================================
-- SECTION 9: COLOR FROM LEGALITY
-- ============================================================================

/-- Legal moves have piece color = toMove.
    Follows from basicMoveLegalBool which includes turnMatches. -/
private theorem legal_move_color (gs : GameState) (m : Move)
    (hmem : m ∈ Rules.allLegalMoves gs) :
    m.piece.color = gs.toMove := by
  -- Extract basicLegalAndSafe from allLegalMoves membership
  unfold Rules.allLegalMoves at hmem
  have ⟨sq, _, hsq⟩ := mem_foldr_append
    (fun sq => Rules.legalMovesForCached gs sq (Rules.pinnedSquares gs gs.toMove))
    allSquares m hmem
  unfold Rules.legalMovesForCached at hsq
  cases hbd : gs.board sq with
  | none => simp only [hbd, List.not_mem_nil] at hsq
  | some p =>
    simp only [hbd] at hsq
    by_cases hcolor : p.color ≠ gs.toMove
    · rw [if_pos hcolor] at hsq; simp at hsq
    · simp only [ne_eq, Decidable.not_not] at hcolor
      rw [if_neg (by simp [hcolor])] at hsq
      -- m passes basicLegalAndSafe filter, which includes turnMatches
      have hmem' := List.mem_filter.mp hsq
      have hblas := hmem'.2
      -- basicLegalAndSafe includes basicMoveLegalBool
      have hbml := Rules.basicLegalAndSafe_implies_basicMoveLegalBool gs m hblas
      -- basicMoveLegalBool includes turnMatches
      unfold Rules.basicMoveLegalBool at hbml
      simp only [Bool.and_eq_true] at hbml
      obtain ⟨⟨⟨⟨_, hturn⟩, _⟩, _⟩, _⟩ := hbml
      unfold Rules.turnMatches at hturn
      simp only [decide_eq_true_eq] at hturn
      exact hturn

-- ============================================================================
-- SECTION 9b: PAWN fromSq GEOMETRY
-- ============================================================================

/-- For pawn capture moves from the capture generation code, toSq.rankInt = fromSq.rankInt + pawnDirection -/
private theorem pawn_cap_rank_constraint (gs : GameState) (src : Square) (p : Piece) (m : Move)
    (hmem : m ∈ ([-1, 1] : List Int).foldr
        (fun df acc =>
          match Movement.squareFromInts (src.fileInt + df) (src.rankInt + Movement.pawnDirection p.color) with
          | some target =>
              if Rules.isEnemyAt gs.board p.color target then
                Rules.promotionMoves { piece := p, fromSq := src, toSq := target, isCapture := true } ++ acc
              else if gs.enPassantTarget = some target ∧ Rules.isEmpty gs.board target then
                { piece := p, fromSq := src, toSq := target, isCapture := true, isEnPassant := true } :: acc
              else acc
          | none => acc)
        []) :
    m.fromSq = src := by
  simp only [List.foldr_cons, List.foldr_nil] at hmem
  -- Process df = -1 and df = 1
  -- Helper function to handle each df case
  suffices ∀ (df : Int) (rest : List Move),
    (match Movement.squareFromInts (src.fileInt + df) (src.rankInt + Movement.pawnDirection p.color) with
     | some target =>
         if Rules.isEnemyAt gs.board p.color target then
           Rules.promotionMoves { piece := p, fromSq := src, toSq := target, isCapture := true } ++ rest
         else if gs.enPassantTarget = some target ∧ Rules.isEmpty gs.board target then
           { piece := p, fromSq := src, toSq := target, isCapture := true, isEnPassant := true } :: rest
         else rest
     | none => rest) = rest ∨ m ∈ rest ∨ m.fromSq = src by
    sorry -- placeholder for now
  sorry

/-- For pawn forward moves, fromSq = src -/
private theorem pawn_fwd_fromSq (gs : GameState) (src : Square) (p : Piece) (m : Move)
    (hmem : m ∈ (match Movement.squareFromInts src.fileInt (src.rankInt + Movement.pawnDirection p.color) with
      | some target =>
          if Rules.isEmpty gs.board target then
            [{ piece := p, fromSq := src, toSq := target : Move }] ++
            (if src.rankNat = Rules.pawnStartRank p.color then
              match Movement.squareFromInts src.fileInt (src.rankInt + 2 * Movement.pawnDirection p.color) with
              | some target2 =>
                  if Rules.isEmpty gs.board target2 then
                    [{ piece := p, fromSq := src, toSq := target2 : Move }]
                  else []
              | none => []
            else [])
          else []
      | none => [])) :
    m.fromSq = src := by
  cases h1 : Movement.squareFromInts src.fileInt (src.rankInt + Movement.pawnDirection p.color) with
  | none => simp only [h1] at hmem; simp at hmem
  | some target =>
    simp only [h1] at hmem
    by_cases he : Rules.isEmpty gs.board target = true
    · simp only [he, ↓reduceIte] at hmem
      rw [List.mem_append] at hmem
      rcases hmem with hb | hd
      · simp only [List.mem_singleton] at hb; subst hb; rfl
      · by_cases hr : src.rankNat = Rules.pawnStartRank p.color
        · simp only [hr, ↓reduceIte] at hd
          cases h2 : Movement.squareFromInts src.fileInt (src.rankInt + 2 * Movement.pawnDirection p.color) with
          | none => simp only [h2] at hd; simp at hd
          | some t2 =>
            simp only [h2] at hd
            by_cases he2 : Rules.isEmpty gs.board t2 = true
            · simp only [he2, ↓reduceIte, List.mem_singleton] at hd; subst hd; rfl
            · simp only [he2, Bool.false_eq_true, ↓reduceIte, List.not_mem_nil] at hd
        · simp only [hr, ↓reduceIte, List.not_mem_nil] at hd
    · simp only [he, Bool.false_eq_true, ↓reduceIte, List.not_mem_nil] at hmem

/-- For all pawn pieceTargets moves, fromSq = src -/
private theorem pawn_pieceTargets_fromSq (gs : GameState) (sq : Square) (p : Piece) (m : Move)
    (hp : p.pieceType = PieceType.Pawn)
    (hmem : m ∈ Rules.pieceTargets gs sq p) :
    m.fromSq = sq := by
  unfold Rules.pieceTargets at hmem
  simp only [hp] at hmem
  rw [List.mem_append] at hmem
  rcases hmem with hfwd | hcap
  · -- Forward moves go through promotionMoves, but fromSq is preserved
    have : m ∈ (Rules.pieceTargets gs sq p).filter (fun _ => true) ∨ m.fromSq = sq := by
      right
      -- Trace through foldr of promotionMoves to extract the base move's fromSq
      induction (match Movement.squareFromInts sq.fileInt (sq.rankInt + Movement.pawnDirection p.color) with
        | some target =>
            if Rules.isEmpty gs.board target then
              [{ piece := p, fromSq := sq, toSq := target : Move }] ++
              (if sq.rankNat = Rules.pawnStartRank p.color then
                match Movement.squareFromInts sq.fileInt (sq.rankInt + 2 * Movement.pawnDirection p.color) with
                | some target2 =>
                    if Rules.isEmpty gs.board target2 then
                      [{ piece := p, fromSq := sq, toSq := target2 : Move }]
                    else []
                | none => []
              else [])
            else []
        | none => []) with
      | nil => simp at hfwd
      | cons x xs ih => sorry
    exact this.elim (fun _ => sorry) id
  · -- Capture moves
    sorry

/-- Legal pawn moves have fromSq determined by the source square in pieceTargets -/
private theorem legal_pawn_fromSq_eq (gs : GameState) (m : Move)
    (hmem : m ∈ Rules.allLegalMoves gs)
    (hp : m.piece.pieceType = PieceType.Pawn) :
    ∃ sq p, gs.board sq = some p ∧ p.pieceType = PieceType.Pawn ∧
    m ∈ Rules.pieceTargets gs sq p ∧ m.fromSq = sq := by
  sorry

-- ============================================================================
-- SECTION 10: MAIN THEOREM
-- ============================================================================

/-- Main theorem: If two non-castle legal moves produce the same moveToSanBase,
    then they are MoveEquivFull (all 9 fields equal).

    The proof structure:
    1. isCastle: both false by hypothesis
    2. castleRookFrom/To: both none (Section 5, fully proven)
    3. pieceType, toSq, capture flag, promotion: from string decomposition (Section 6)
    4. fromSq: from disambiguation + legality (Section 7) or file char (pawns)
    5. isCapture, isEnPassant: from toSq + legality (Section 8)
    6. piece.color: both = gs.toMove (Section 9) -/
private theorem non_castle_moveEquiv (gs : GameState) (m1 m2 : Move)
    (h1 : m1 ∈ Rules.allLegalMoves gs) (h2 : m2 ∈ Rules.allLegalMoves gs)
    (hbase : moveToSanBase gs m1 = moveToSanBase gs m2)
    (hnc1 : m1.isCastle = false) (hnc2 : m2.isCastle = false) :
    MoveEquivFull m1 m2 := by
  obtain ⟨hpt, htoSq, hcap_or, hpromo, hdis, hpawn_file⟩ :=
    moveToSanBase_eq_implies_fields gs m1 m2 h1 h2 hbase hnc1 hnc2
  have hrf1 := noncastle_legal_castle_none gs m1 h1 hnc1
  have hrf2 := noncastle_legal_castle_none gs m2 h2 hnc2
  have hcolor1 := legal_move_color gs m1 h1
  have hcolor2 := legal_move_color gs m2 h2
  have hcolor : m1.piece.color = m2.piece.color := hcolor1.trans hcolor2.symm
  have ⟨hcap, hep⟩ := legal_same_toSq_implies_same_capture_ep gs m1 m2 h1 h2 htoSq hcap_or
  have hfromSq : m1.fromSq = m2.fromSq := by
    by_cases hp : m1.piece.pieceType = PieceType.Pawn
    · -- Pawn: fromSq from file char (capture) or from toSq constraint (non-capture)
      sorry
    · exact same_disambiguation_implies_same_fromSq gs m1 m2 h1 h2 hpt hcolor htoSq hdis hp
  have hpiece : m1.piece = m2.piece := by
    cases hp1 : m1.piece; cases hp2 : m2.piece
    simp only [Piece.mk.injEq]
    constructor
    · simp only [hp1, hp2] at hpt; exact hpt
    · simp only [hp1, hp2] at hcolor; exact hcolor
  exact ⟨hpiece, hfromSq, htoSq, hcap, hpromo,
         hnc1.trans hnc2.symm, hep,
         hrf1.1.trans hrf2.1.symm, hrf1.2.trans hrf2.2.symm⟩

end Parsing
end Chess
