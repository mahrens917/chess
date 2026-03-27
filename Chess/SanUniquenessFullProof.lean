import Chess.Parsing
import Chess.Rules

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
      sorry
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
    · -- Both pieces: string decomposition
      sorry

-- ============================================================================
-- SECTION 7: DISAMBIGUATION UNIQUENESS
-- ============================================================================

/-- If two legal non-pawn moves of the same piece type to the same target have
    the same sanDisambiguation string, they have the same fromSq.
    This follows from the construction of sanDisambiguation which encodes
    file, rank, or both of fromSq to distinguish peers. -/
private theorem same_disambiguation_implies_same_fromSq (gs : GameState) (m1 m2 : Move)
    (h1 : m1 ∈ Rules.allLegalMoves gs) (h2 : m2 ∈ Rules.allLegalMoves gs)
    (hpt : m1.piece.pieceType = m2.piece.pieceType)
    (hcolor : m1.piece.color = m2.piece.color)
    (htoSq : m1.toSq = m2.toSq)
    (hdis : sanDisambiguation gs m1 = sanDisambiguation gs m2)
    (hnp : m1.piece.pieceType ≠ PieceType.Pawn) :
    m1.fromSq = m2.fromSq := by
  -- If fromSq1 = fromSq2 we're done. Otherwise derive contradiction from disambiguation.
  -- m2 would be a peer of m1 (same type, color, target, different source),
  -- so both disambiguations would be non-empty and encode different source info.
  sorry

-- ============================================================================
-- SECTION 8: CAPTURE/EP FLAGS FROM LEGALITY
-- ============================================================================

/-- Two legal moves to the same square with the same capture-or-ep flag
    have the same isCapture and isEnPassant fields individually.
    This follows from move generation: isCapture and isEnPassant are determined
    by the board state at the target square. -/
private theorem legal_same_toSq_implies_same_capture_ep (gs : GameState) (m1 m2 : Move)
    (h1 : m1 ∈ Rules.allLegalMoves gs) (h2 : m2 ∈ Rules.allLegalMoves gs)
    (htoSq : m1.toSq = m2.toSq)
    (hcap_or : (m1.isCapture || m1.isEnPassant) = (m2.isCapture || m2.isEnPassant)) :
    m1.isCapture = m2.isCapture ∧ m1.isEnPassant = m2.isEnPassant := by
  -- For legal moves, isCapture and isEnPassant are determined by the board state
  -- at the target square. Two legal moves to the same square in the same position
  -- see the same board, so they get the same flags.
  -- The formal proof requires tracing through move generation to show that
  -- the capture/EP classification is determined by toSq + board state.
  sorry

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
