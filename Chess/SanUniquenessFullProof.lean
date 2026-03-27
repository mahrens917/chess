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
      sorry -- Full proof uses x_mem_piece_san_iff for capture, pieceLetter for type,
            -- sanDisambiguation_chars for disambiguation, and list cancellation for the rest.
            -- See pawn case above for the analogous fully-proven decomposition.
      /-  -- Step 1: piece type from first char
      have hpt : m1.piece.pieceType = m2.piece.pieceType := by
        obtain ⟨c1, hc1_list, _⟩ := pieceLetter_first_upper m1.piece.pieceType hp1
        obtain ⟨c2, hc2_list, _⟩ := pieceLetter_first_upper m2.piece.pieceType hp2
        unfold moveToSanBase at hbase
        simp only [hnc1, hnc2, hp1, hp2, ↓reduceIte] at hbase
        have hlist := congrArg String.toList hbase
        simp only [String.toList_append] at hlist
        rw [hc1_list, hc2_list] at hlist
        simp only [List.singleton_append, List.cons_append] at hlist
        have := (List.cons.inj hlist).1
        apply pieceLetter_injective
        exact String.toList_inj.mp (by rw [hc1_list, hc2_list, this])
      -- Step 2: same capture flag from 'x' membership
      have hcap_eq : (m1.isCapture || m1.isEnPassant) = (m2.isCapture || m2.isEnPassant) := by
        have h1x := x_mem_piece_san_iff gs m1 hnc1 hp1
        have h2x := x_mem_piece_san_iff gs m2 hnc2 hp2
        cases hc1 : m1.isCapture || m1.isEnPassant <;> cases hc2 : m2.isCapture || m2.isEnPassant
        · rfl
        · -- m1 no cap, m2 cap: 'x' ∈ san2 but 'x' ∉ san1
          exfalso
          have : 'x' ∈ (moveToSanBase gs m2).toList := h2x.mpr rfl
          rw [← hbase] at this
          have : (m1.isCapture || m1.isEnPassant) = true := h1x.mp this
          rw [hc1] at this; exact absurd this (by decide)
        · -- m1 cap, m2 no cap: symmetric
          exfalso
          have : 'x' ∈ (moveToSanBase gs m1).toList := h1x.mpr rfl
          rw [hbase] at this
          have : (m2.isCapture || m2.isEnPassant) = true := h2x.mp this
          rw [hc2] at this; exact absurd this (by decide)
        · rfl
      -- Step 3: unfold to get the tail after piece letter
      -- san = pl ++ dis ++ cap_str ++ alg ++ prom
      -- With same pl (1 char), stripping gives: dis ++ cap_str ++ alg ++ prom
      -- With same cap_str (determined by cap_eq), the structure is:
      --   dis ++ cap_str ++ alg ++ prom
      -- where cap_str, alg, prom have known lengths, so we can extract dis too
      unfold moveToSanBase at hbase
      simp only [hnc1, hnc2, hp1, hp2, ↓reduceIte] at hbase
      -- hbase : pl1 ++ dis1 ++ cap1 ++ alg1 ++ prom1 = pl2 ++ dis2 ++ cap2 ++ alg2 ++ prom2
      -- Since prom is at the right end and alg has fixed length, strip from the right
      -- Step 3a: total list equality
      have hlist := congrArg String.toList hbase
      simp only [String.toList_append] at hlist
      -- Step 3b: strip piece letter (1 char)
      obtain ⟨c1, hc1_list, _⟩ := pieceLetter_first_upper m1.piece.pieceType hp1
      obtain ⟨c2, hc2_list, _⟩ := pieceLetter_first_upper m2.piece.pieceType hp2
      rw [hc1_list, hc2_list] at hlist
      simp only [List.singleton_append, List.cons_append] at hlist
      have htail := (List.cons.inj hlist).2
      -- htail : dis1 ++ cap1 ++ alg1 ++ prom1 = dis2 ++ cap2 ++ alg2 ++ prom2
      -- Step 3c: the right end is alg ++ prom. With same cap, we can show alg and prom match.
      -- Since cap1 = cap2 (from hcap_eq), cap_str1 = cap_str2 (same 0 or 1 char)
      -- So dis1 ++ cap_str ++ alg1 ++ prom1 = dis2 ++ cap_str ++ alg2 ++ prom2
      -- The right parts (cap_str ++ alg ++ prom) have the SAME total length for both
      -- So we can use total length to determine that dis lengths match
      -- Then use list_append_cancel_left
      -- However, we don't know prom lengths match yet.
      -- Key insight: the string equality + same cap → same structure
      -- Let's just extract: overall tail is equal, and sanDisambiguation equality follows
      -- from the overall string equality
      -- The 6 conclusions:
      -- (1) hpt ✓
      -- (5) disambiguation: after stripping pl, cap, alg, prom, what remains is dis
      --     Since we can show alg ++ prom match (from the right end), dis must match too
      -- But we need alg and prom individually too.
      -- Let's just try: from the tail equality, extract everything by working with string
      -- representation. The tail is:
      -- sanDisambiguation gs m1 ++ cap_str1 ++ algebraic1 ++ prom1 =
      -- sanDisambiguation gs m2 ++ cap_str2 ++ algebraic2 ++ prom2
      -- Since the FULL string (tail) is equal, and we need all subparts equal,
      -- just note that the FULL string determines all parts (since the concatenation IS the tail).
      -- In particular, sanDisambiguation gs m1 ++ cap_str1 ++ alg1 ++ prom1 is equal to
      -- sanDisambiguation gs m2 ++ cap_str2 ++ alg2 ++ prom2.
      -- This IS the statement that the tail (after piece letter) is equal.
      -- We need to extract: toSq, promotion, disambiguation.
      -- Since both cap flags are the same, cap_str1 = cap_str2.
      -- Then: dis1 ++ cap_str ++ alg1 ++ prom1 = dis2 ++ cap_str ++ alg2 ++ prom2
      -- From the right: alg1 ++ prom1 vs alg2 ++ prom2
      -- alg has length 2, prom has length 0 or 2
      -- If prom lengths differ (0 vs 2), total right part lengths differ by 2
      -- But both tails have same total length, so dis lengths differ by 2
      -- dis has length 0-2, so dis lengths can only differ by 0, 1, or 2
      -- If prom1 = 0, prom2 = 2: dis1 must be 2 longer than dis2
      -- If prom1 = 2, prom2 = 0: dis2 must be 2 longer than dis1
      -- These are possible but the CHARACTER content constrains things.
      -- Actually, let me just use the overall TAIL equality + promotionSuffix_injective.
      -- The tail = dis ++ cap_str ++ alg ++ prom.
      -- Both are STRINGS, and the string equality is just htail (as lists).
      -- Convert back to string equality:
      have htail_str : sanDisambiguation gs m1 ++ (if (m1.isCapture || m1.isEnPassant) = true then "x" else "") ++ m1.toSq.algebraic ++ promotionSuffix m1 =
                       sanDisambiguation gs m2 ++ (if (m2.isCapture || m2.isEnPassant) = true then "x" else "") ++ m2.toSq.algebraic ++ promotionSuffix m2 := by
        have := congrArg String.toList hbase
        simp only [String.toList_append] at this
        rw [hc1_list, hc2_list] at this
        simp only [List.singleton_append, List.cons_append] at this
        exact String.toList_inj.mp (List.cons.inj this).2
      -- With same cap flag, the cap_str parts are the same string
      have hcap_str : (if (m1.isCapture || m1.isEnPassant) = true then "x" else ("" : String)) =
                      (if (m2.isCapture || m2.isEnPassant) = true then "x" else "") := by
        rw [hcap_eq]
      rw [hcap_str] at htail_str
      -- Now: dis1 ++ cap_str ++ alg1 ++ prom1 = dis2 ++ cap_str ++ alg2 ++ prom2
      -- This is: (dis1 ++ cap_str) ++ (alg1 ++ prom1) = (dis2 ++ cap_str) ++ (alg2 ++ prom2)
      -- The conclusion includes dis1 = dis2, alg1 = alg2, prom1 = prom2
      -- We can't directly cancel because dis has unknown length.
      -- But we CAN use the congrArg to get the string equality and then observe:
      -- The sanDisambiguation + cap_str is the LEFT part, and alg + prom is the RIGHT part.
      -- We need both parts to match.
      -- Instead of trying to separate them formally, let's observe that:
      -- (a) the WHOLE tail string is equal → sanDisambiguation equality follows from the conclusion
      -- (b) for toSq: we can use algebraic_injective
      -- (c) for promotion: we can use promotionSuffix_injective
      -- But we need to EXTRACT alg and prom from the tail.
      -- SIMPLEST APPROACH: the 6 conclusions are:
      refine ⟨hpt, ?_, hcap_eq, ?_, ?_, fun h _ => absurd h hp1⟩
      -- Remaining goals: toSq, promotion, disambiguation
      -- From htail_str, we know the tail strings are equal.
      -- The tail has structure: dis ++ cap_str ++ alg ++ prom = dis ++ cap_str ++ alg ++ prom
      -- But we can't easily decompose this. Let me try a different approach:
      -- Use the ORIGINAL hbase (string equality) to derive toSq by showing
      -- that algebraic determines a unique position in the string.
      -- Actually, I'll take the approach of showing all fields are determined by the string:
      all_goals sorry -/

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
  -- From (cap1 || ep1) = (cap2 || ep2) and both to the same square,
  -- the individual flags must match.
  -- Key insight: for legal moves in this engine, isEnPassant = true → isCapture = true
  -- (from the move generation code) and the board state at the target determines
  -- whether a capture/EP is possible.
  -- Simple proof: case split on the 4 bools, use hcap_or to eliminate mismatched OR cases,
  -- and the remaining problematic cases are impossible for legal moves.
  -- For this proof, we observe that from the OR equality:
  -- If OR = false: both false → cap1=cap2=F, ep1=ep2=F
  -- If OR = true: both true
  --   The problematic case is when individual bools differ despite same OR.
  --   But since isEnPassant and isCapture are not independent for legal moves,
  --   the case analysis reduces to matching.
  -- We use a simple Boolean analysis: if cap || ep = true for both,
  -- and the moves target the same square, the flags must match because:
  -- (a) ep=T → cap=T in move generation (en passant always sets isCapture)
  -- (b) Two legal moves to same square have same board occupancy observation
  -- For now, the proof handles the purely Boolean cases:
  cases hc1 : m1.isCapture <;> cases he1 : m1.isEnPassant <;>
  cases hc2 : m2.isCapture <;> cases he2 : m2.isEnPassant <;>
  simp_all
  -- Remaining cases involve (cap=F,ep=T) which is impossible for legal moves,
  -- or (cap=T,ep=F) vs (cap=T,ep=T) to the same square.
  -- These require move generation invariants. We use sorry for now.
  all_goals sorry

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
