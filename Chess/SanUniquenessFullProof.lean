/-
SanUniquenessFullProof.lean

Full proof that moveToSAN is injective (up to MoveEquiv) on legal moves.
-/
import Chess.Core
import Chess.Movement
import Chess.Game
import Chess.Rules
import Chess.Parsing
import Chess.SanUniquenessProof
import Chess.StringLemmas
-- Note: Chess.ParsingProofs has build errors, so we prove needed lemmas locally

namespace Chess
namespace SanUniquenessFullProof

open scoped Classical
open Rules Parsing

set_option maxHeartbeats 1600000

-- MoveEquiv (same as PerftProofs)
def MoveEquiv (m1 m2 : Move) : Prop :=
  m1.piece = m2.piece ∧
  m1.fromSq = m2.fromSq ∧
  m1.toSq = m2.toSq ∧
  m1.isCapture = m2.isCapture ∧
  m1.promotion = m2.promotion ∧
  m1.isCastle = m2.isCastle ∧
  m1.castleRookFrom = m2.castleRookFrom ∧
  m1.castleRookTo = m2.castleRookTo ∧
  m1.isEnPassant = m2.isEnPassant

-- ============================================================================
-- Core string/list helpers
-- ============================================================================

private theorem OO_ne_OOO : ("O-O" : String) ≠ "O-O-O" := by native_decide

private theorem head_append_of_ne_nil {α : Type} {l1 l2 : List α} (h : l1 ≠ []) :
    (l1 ++ l2).head? = l1.head? := by
  cases l1 with
  | nil => exact absurd rfl h
  | cons a as => simp

private theorem string_head_append (s1 s2 : String) (h : s1.toList ≠ []) :
    (s1 ++ s2).toList.head? = s1.toList.head? := by
  simp only [String.toList_append]; exact head_append_of_ne_nil h

private theorem string_append_ne_empty_left (s1 s2 : String) (h : s1.toList ≠ []) :
    (s1 ++ s2).toList ≠ [] := by
  simp only [String.toList_append]
  exact fun hempty => h (List.append_eq_nil_iff.mp hempty).1

private theorem head_of_append4 (s1 s2 s3 s4 : String) (h : s1.toList ≠ []) :
    (s1 ++ s2 ++ s3 ++ s4).toList.head? = s1.toList.head? := by
  have h12 := string_append_ne_empty_left s1 s2 h
  have h123 := string_append_ne_empty_left (s1 ++ s2) s3 h12
  rw [string_head_append _ s4 h123, string_head_append _ s3 h12, string_head_append _ s2 h]

private theorem head_of_append5 (s1 s2 s3 s4 s5 : String) (h : s1.toList ≠ []) :
    (s1 ++ s2 ++ s3 ++ s4 ++ s5).toList.head? = s1.toList.head? := by
  have h12 := string_append_ne_empty_left s1 s2 h
  have h123 := string_append_ne_empty_left (s1 ++ s2) s3 h12
  have h1234 := string_append_ne_empty_left (s1 ++ s2 ++ s3) s4 h123
  rw [string_head_append _ s5 h1234, string_head_append _ s4 h123,
      string_head_append _ s3 h12, string_head_append _ s2 h]

private theorem all_fileChars_ne_O :
    ∀ (f : Fin 8), Char.ofNat ('a'.toNat + f.val) ≠ 'O' := by native_decide

private theorem pieceLetter_ne_empty (pt : PieceType) (h : pt ≠ PieceType.Pawn) :
    (pieceLetter pt).toList ≠ [] := by
  cases pt <;> simp_all [pieceLetter] <;> native_decide

private theorem pieceLetter_head_ne_O (pt : PieceType) (h : pt ≠ PieceType.Pawn) :
    (pieceLetter pt).toList.head? ≠ some 'O' := by
  cases pt <;> simp_all [pieceLetter] <;> native_decide

private theorem algebraic_ne_empty (sq : Square) : sq.algebraic.toList ≠ [] := by
  cases sq with | mk f r =>
  simp [Square.algebraic, Square.fileNat, File.toNat, Char.toString,
    String.toList_append, String.toList_singleton]

private theorem algebraic_head (sq : Square) :
    sq.algebraic.toList.head? = some sq.fileChar := by
  cases sq with | mk f r =>
  simp [Square.algebraic, Square.fileChar, Square.fileNat, File.toNat, Char.toString,
    String.toList_append, String.toList_singleton]

private theorem singleton_ne_empty (c : Char) : (String.singleton c).toList ≠ [] := by
  simp [String.toList_singleton]

-- ============================================================================
-- Castle/non-castle SAN first char separation
-- ============================================================================

private theorem castle_head_eq_O (gs : GameState) (m : Move) (hc : m.isCastle = true) :
    (moveToSanBase gs m).toList.head? = some 'O' := by
  unfold moveToSanBase; simp only [hc, ↓reduceIte]; split <;> native_decide

private theorem non_castle_head_ne_O (gs : GameState) (m : Move) (hnc : m.isCastle = false) :
    (moveToSanBase gs m).toList.head? ≠ some 'O' := by
  intro heq
  unfold moveToSanBase at heq; simp only [hnc, Bool.false_eq_true, ↓reduceIte] at heq
  by_cases hpawn : m.piece.pieceType = PieceType.Pawn
  · simp only [hpawn, ↓reduceIte] at heq
    by_cases hcap : (m.isCapture || m.isEnPassant) = true
    · simp only [hcap, ↓reduceIte] at heq
      rw [head_of_append4 _ _ _ _ (singleton_ne_empty _)] at heq
      simp only [String.toList_singleton, List.head?_cons] at heq
      have hfc : m.fromSq.fileChar ≠ 'O' := by
        cases m.fromSq with | mk f r =>
        simp only [Square.fileChar, Square.fileNat, File.toNat]
        exact all_fileChars_ne_O f
      exact hfc (Option.some.inj heq)
    · simp only [Bool.not_eq_true] at hcap
      simp only [hcap, Bool.false_eq_true, ↓reduceIte] at heq
      simp only [String.empty_append, String.append_empty] at heq
      rw [string_head_append _ _ (algebraic_ne_empty m.toSq), algebraic_head m.toSq] at heq
      have hfc : m.toSq.fileChar ≠ 'O' := by
        cases m.toSq with | mk f r =>
        simp only [Square.fileChar, Square.fileNat, File.toNat]
        exact all_fileChars_ne_O f
      exact hfc (Option.some.inj heq)
  · simp only [hpawn, ↓reduceIte] at heq
    rw [head_of_append5 _ _ _ _ _ (pieceLetter_ne_empty m.piece.pieceType hpawn)] at heq
    exact pieceLetter_head_ne_O m.piece.pieceType hpawn heq

theorem isCastle_eq_of_base_eq (gs : GameState) (m1 m2 : Move)
    (hbase : moveToSanBase gs m1 = moveToSanBase gs m2) :
    m1.isCastle = m2.isCastle := by
  by_cases hc1 : m1.isCastle = true <;> by_cases hc2 : m2.isCastle = true
  · simp [hc1, hc2]
  · exfalso; have := castle_head_eq_O gs m1 hc1
    rw [congrArg (fun s => s.toList.head?) hbase] at this
    exact non_castle_head_ne_O gs m2 (Bool.eq_false_iff.mpr hc2) this
  · exfalso; have := castle_head_eq_O gs m2 hc2
    rw [← congrArg (fun s => s.toList.head?) hbase] at this
    exact non_castle_head_ne_O gs m1 (Bool.eq_false_iff.mpr hc1) this
  · simp [Bool.eq_false_iff.mpr hc1, Bool.eq_false_iff.mpr hc2]

-- ============================================================================
-- Castle MoveEquiv via castleMoveIfLegal
-- ============================================================================

private theorem castle_side_eq (gs : GameState) (m1 m2 : Move)
    (hc1 : m1.isCastle = true) (hc2 : m2.isCastle = true)
    (hbase : moveToSanBase gs m1 = moveToSanBase gs m2) :
    (m1.toSq.fileNat = 6) = (m2.toSq.fileNat = 6) := by
  unfold moveToSanBase at hbase; simp only [hc1, hc2, ↓reduceIte] at hbase
  by_cases h1 : m1.toSq.fileNat = 6 <;> by_cases h2 : m2.toSq.fileNat = 6
  · simp [h1, h2]
  · simp only [h1, h2, ↓reduceIte] at hbase; exact absurd hbase OO_ne_OOO
  · simp only [h1, h2, ↓reduceIte] at hbase; exact absurd hbase.symm OO_ne_OOO
  · simp [h1, h2]

private theorem castleMoveIfLegal_structure (gs : GameState) (kingSide : Bool) (m : Move)
    (h : castleMoveIfLegal gs kingSide = some m) :
    m.isCastle = true ∧
    m.fromSq = (castleConfig gs.toMove kingSide).kingFrom ∧
    m.toSq = (castleConfig gs.toMove kingSide).kingTo ∧
    m.castleRookFrom = some (castleConfig gs.toMove kingSide).rookFrom ∧
    m.castleRookTo = some (castleConfig gs.toMove kingSide).rookTo ∧
    m.piece.pieceType = PieceType.King ∧
    m.piece.color = gs.toMove ∧
    m.isCapture = false ∧
    m.promotion = none ∧
    m.isEnPassant = false := by
  unfold castleMoveIfLegal at h; simp only at h
  split at h
  · split at h
    · rename_i k r _ _; split at h
      · rename_i hpieces; split at h
        · simp only [Option.some.injEq] at h; subst h
          exact ⟨rfl, rfl, rfl, rfl, rfl, hpieces.1, hpieces.2.1, rfl, rfl, rfl⟩
        · exact absurd h (Option.noConfusion)
      · exact absurd h (Option.noConfusion)
    · exact absurd h (Option.noConfusion)
  · exact absurd h (Option.noConfusion)

private theorem castleConfig_file (c : Color) :
    (castleConfig c true).kingTo.fileNat = 6 ∧
    (castleConfig c false).kingTo.fileNat ≠ 6 := by
  cases c <;> constructor <;> native_decide

/-- walk only produces moves with isCastle = false. -/
private theorem walk_not_castle
    (src : Square) (p : Piece) (board : Board) (color : Color) (maxStep : Nat)
    (df dr : Int) (n : Nat) (acc : List Move) (m : Move)
    (hm : m ∈ slidingTargets.walk src p board color maxStep df dr n acc)
    (hacc : ∀ m', m' ∈ acc → m'.isCastle = false) :
    m.isCastle = false := by
  induction n generalizing acc with
  | zero => simp only [slidingTargets.walk] at hm; exact hacc m hm
  | succ s ih =>
    simp only [slidingTargets.walk] at hm; split at hm
    · exact hacc m hm
    · split at hm
      · exact ih _ hm (fun m' hm' => by
          rcases List.mem_cons.mp hm' with rfl | hrest
          · rfl
          · exact hacc m' hrest)
      · split at hm
        · rcases List.mem_cons.mp hm with rfl | hrest
          · rfl
          · exact hacc m hrest
        · exact hacc m hm

/-- All moves in foldr of walk have isCastle = false. -/
private theorem sliding_foldr_not_castle (src : Square) (p : Piece) (board : Board) (color : Color)
    (deltas : List (Int × Int)) :
    ∀ m, m ∈ deltas.foldr
      (fun d acc => slidingTargets.walk src p board color 7 d.fst d.snd 7 acc) [] →
    m.isCastle = false := by
  induction deltas with
  | nil => intro m hm; simp only [List.foldr, List.mem_nil_iff] at hm
  | cons d ds ih =>
    intro m hm; simp only [List.foldr] at hm
    exact walk_not_castle src p board color 7 d.fst d.snd 7 _ m hm ih

private theorem sliding_not_castle (gs : GameState) (src : Square) (p : Piece)
    (deltas : List (Int × Int)) (m : Move) (hm : m ∈ slidingTargets gs src p deltas) :
    m.isCastle = false := by
  unfold slidingTargets at hm
  exact sliding_foldr_not_castle src p gs.board p.color deltas m hm

/-- promotionMoves preserves isCastle. -/
private theorem promotionMoves_isCastle (m m' : Move)
    (h : m' ∈ promotionMoves m) : m'.isCastle = m.isCastle := by
  unfold promotionMoves at h
  split at h
  · simp only [promotionTargets, List.mem_map, List.mem_cons, List.mem_singleton,
      List.mem_nil_iff, or_false] at h
    obtain ⟨_, _, rfl⟩ := h; rfl
  · simp only [List.mem_singleton] at h; rw [h]

/-- All pawn pieceTargets moves have isCastle = false. -/
private theorem pawn_not_castle (gs : GameState) (sq : Square) (p : Piece) (m : Move)
    (hm : m ∈ pieceTargets gs sq p) (hp : p.pieceType = PieceType.Pawn := by assumption) :
    m.isCastle = false := by
  simp only [pieceTargets, hp] at hm
  rw [List.mem_append] at hm
  -- General lemma: foldr of promotionMoves preserves isCastle = false
  have foldr_promo : ∀ (fwdMoves : List Move),
      (∀ x ∈ fwdMoves, x.isCastle = false) →
      ∀ x ∈ fwdMoves.foldr (fun mv acc => promotionMoves mv ++ acc) [],
      x.isCastle = false := by
    intro fwdMoves hAll x hx
    induction fwdMoves with
    | nil => simp at hx
    | cons a as ih =>
      simp only [List.foldr, List.mem_append] at hx
      rcases hx with hpromo | hrest
      · rw [promotionMoves_isCastle a x hpromo]; exact hAll a (List.mem_cons_self ..)
      · exact ih (fun y hy => hAll y (List.mem_cons_of_mem _ hy)) hrest
  rcases hm with hfwd | hcap
  · -- Forward moves
    apply foldr_promo _ _ m hfwd
    -- Show all forward moves have isCastle = false
    intro x hx
    split at hx
    · split at hx
      · rw [List.mem_append] at hx
        rcases hx with h | h
        · simp only [List.mem_singleton] at h; subst h; rfl
        · split at h
          · split at h
            · split at h
              · simp only [List.mem_singleton] at h; subst h; rfl
              · simp at h
            · simp at h
          · simp at h
      · simp at hx
    · simp at hx
  · -- Capture moves (foldr over [-1, 1])
    -- Each capture move is either:
    -- promotionMoves { ..., isCapture := true } or { ..., isEnPassant := true }
    -- All have default isCastle = false
    simp only [List.foldr] at hcap
    -- After unfolding the foldr on [-1, 1]:
    -- The structure is: match ... with
    --   | some target => if enemyAt then promoMoves ++ rest else if ep then ep :: rest else rest
    --   | none => rest
    -- where rest comes from the second offset (1)
    -- We need to trace through all branches
    -- Helper: all elements of this capture accumulation have isCastle = false
    suffices ∀ (acc : List Move),
        (∀ x ∈ acc, x.isCastle = false) →
        ∀ (offsets : List Int),
        ∀ x ∈ offsets.foldr (fun df acc' =>
            match Movement.squareFromInts (sq.fileInt + df) (sq.rankInt + Movement.pawnDirection p.color) with
            | some target =>
              if isEnemyAt gs.board p.color target then
                promotionMoves { piece := p, fromSq := sq, toSq := target, isCapture := true } ++ acc'
              else if gs.enPassantTarget = some target ∧ isEmpty gs.board target then
                { piece := p, fromSq := sq, toSq := target, isCapture := true, isEnPassant := true } :: acc'
              else acc'
            | none => acc') acc,
        x.isCastle = false by
      exact this [] (fun _ h => by simp at h) [-1, 1] m hcap
    intro acc hacc offsets x hx
    induction offsets generalizing acc with
    | nil => simp only [List.foldr] at hx; exact hacc x hx
    | cons d ds ih =>
      simp only [List.foldr] at hx
      split at hx
      · -- squareFromInts = some target
        split at hx
        · -- isEnemyAt: promotionMoves { ... } ++ rest
          rw [List.mem_append] at hx
          rcases hx with hp | hr
          · exact promotionMoves_isCastle _ x hp ▸ rfl
          · exact ih acc hacc hr
        · split at hx
          · -- en passant: { ... } :: rest
            simp only [List.mem_cons] at hx
            rcases hx with rfl | hr
            · rfl
            · exact ih acc hacc hr
          · exact ih acc hacc hx
      · -- squareFromInts = none
        exact ih acc hacc hx

/-- Legal castle moves come from castleMoveIfLegal.
    Traces through allLegalMoves → legalMovesForCached → pieceTargets → King → castleMoveIfLegal.
    Non-castle branches never set isCastle = true. -/
private theorem legal_castle_from_castleMoveIfLegal (gs : GameState) (m : Move)
    (hm : m ∈ allLegalMoves gs) (hc : m.isCastle = true) :
    ∃ kingSide, castleMoveIfLegal gs kingSide = some m := by
  unfold allLegalMoves at hm
  rw [List.mem_foldr_append_iff] at hm
  obtain ⟨sq, _, hmcached⟩ := hm
  unfold legalMovesForCached at hmcached
  split at hmcached
  · simp at hmcached
  · rename_i p _; split at hmcached
    · simp at hmcached
    · have hfilt1 := List.mem_filter.mp hmcached
      have hfilt2 := List.mem_filter.mp hfilt1.1
      -- m ∈ pieceTargets gs sq p with m.isCastle = true
      -- Use the proven lemma: pieceTargets only produces isCastle=true via castleMoveIfLegal
      -- We inline the proof from ParsingProofs.lean's mem_pieceTargets_castle_exists
      have hpt := hfilt2.1
      unfold pieceTargets at hpt
      cases hp : p.pieceType <;> simp only [hp] at hpt
      · -- King: standard ++ castles
        rw [List.mem_append] at hpt
        rcases hpt with hstd | hcastles
        · -- Standard king moves have isCastle = false
          exfalso
          simp only [List.mem_filterMap] at hstd
          obtain ⟨_, _, htarget⟩ := hstd
          split at htarget
          · split at htarget
            · simp only [Option.some.injEq] at htarget; rw [← htarget] at hc; simp at hc
            · simp only [Option.some.injEq] at htarget; rw [← htarget] at hc; simp at hc
          · exact absurd htarget (Option.noConfusion)
        · -- Castle moves from filterMap id
          simp only [List.mem_filterMap, List.mem_cons, List.mem_nil_iff, id_eq, or_false] at hcastles
          obtain ⟨x, hx_mem, hx_eq⟩ := hcastles
          rcases hx_mem with rfl | rfl
          · exact ⟨true, hx_eq⟩
          · exact ⟨false, hx_eq⟩
      · -- Queen: slidingTargets, all isCastle = false
        exfalso
        -- hpt : m ∈ slidingTargets gs sq p [...]
        -- Need: m.isCastle = false from sliding targets
        -- slidingTargets only creates {piece:=p, fromSq:=src, toSq:=target} or
        -- {piece:=p, fromSq:=src, toSq:=target, isCapture:=true}
        -- Use simpa to get the right form then the walk induction
        have := sliding_not_castle gs sq p _ m hpt
        rw [this] at hc; simp at hc
      · -- Rook
        exfalso
        have := sliding_not_castle gs sq p _ m hpt
        rw [this] at hc; simp at hc
      · -- Bishop
        exfalso
        have := sliding_not_castle gs sq p _ m hpt
        rw [this] at hc; simp at hc
      · -- Knight: filterMap, all moves have default isCastle = false
        exfalso
        simp only [List.mem_filterMap] at hpt
        obtain ⟨_, _, htarget⟩ := hpt
        split at htarget
        · split at htarget
          · simp only [Option.some.injEq] at htarget; rw [← htarget] at hc; simp at hc
          · simp only [Option.some.injEq] at htarget; rw [← htarget] at hc; simp at hc
        · exact absurd htarget (Option.noConfusion)
      · -- Pawn: all pawn moves have isCastle = false
        exfalso
        -- hpt is the simp'd version of m ∈ pieceTargets gs sq p
        -- We need to reconstruct the original membership
        have hmem : m ∈ pieceTargets gs sq p := by simpa [pieceTargets, hp] using hpt
        have := pawn_not_castle gs sq p m hmem hp
        rw [this] at hc; simp at hc

theorem castle_moveEquiv (gs : GameState) (m1 m2 : Move)
    (h1 : m1 ∈ allLegalMoves gs) (h2 : m2 ∈ allLegalMoves gs)
    (hc1 : m1.isCastle = true) (hc2 : m2.isCastle = true)
    (hbase : moveToSanBase gs m1 = moveToSanBase gs m2) :
    MoveEquiv m1 m2 := by
  obtain ⟨ks1, hks1⟩ := legal_castle_from_castleMoveIfLegal gs m1 h1 hc1
  obtain ⟨ks2, hks2⟩ := legal_castle_from_castleMoveIfLegal gs m2 h2 hc2
  have s1 := castleMoveIfLegal_structure gs ks1 m1 hks1
  have s2 := castleMoveIfLegal_structure gs ks2 m2 hks2
  have hside := castle_side_eq gs m1 m2 hc1 hc2 hbase
  have hks_eq : ks1 = ks2 := by
    have hf1 : m1.toSq.fileNat = (castleConfig gs.toMove ks1).kingTo.fileNat := by rw [s1.2.2.1]
    have hf2 : m2.toSq.fileNat = (castleConfig gs.toMove ks2).kingTo.fileNat := by rw [s2.2.2.1]
    by_cases hk1 : ks1 = true <;> by_cases hk2 : ks2 = true
    · simp [hk1, hk2]
    · exfalso; subst hk1; simp at hk2
      have h6_1 : m1.toSq.fileNat = 6 := by rw [hf1]; exact (castleConfig_file gs.toMove).1
      have hne_2 : m2.toSq.fileNat ≠ 6 := by rw [hf2, hk2]; exact (castleConfig_file gs.toMove).2
      exact hne_2 (by rwa [← hside])
    · exfalso; subst hk2; simp at hk1
      have h6_2 : m2.toSq.fileNat = 6 := by rw [hf2]; exact (castleConfig_file gs.toMove).1
      have hne_1 : m1.toSq.fileNat ≠ 6 := by rw [hf1, hk1]; exact (castleConfig_file gs.toMove).2
      exact hne_1 (by rwa [hside])
    · simp at hk1 hk2; rw [hk1, hk2]
  subst hks_eq
  have : m1 = m2 := Option.some.inj (hks1.symm.trans hks2)
  subst this; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- Non-castle MoveEquiv (TODO: requires extensive string analysis)
-- ============================================================================

/-- Non-castle moves with equal base SAN are MoveEquiv.
    The proof requires showing the SAN string encodes enough information to uniquely
    determine all MoveEquiv fields. This follows from:
    - Pawn/piece separation via first character analysis
    - Piece type from pieceLetter injectivity
    - Target square from algebraic encoding
    - Source square from sanDisambiguation (9-case analysis)
    - Promotion from promotionSuffix injectivity
    - Capture/en passant from board position given other fields -/
private theorem non_castle_moveEquiv (gs : GameState) (m1 m2 : Move)
    (h1 : m1 ∈ allLegalMoves gs) (h2 : m2 ∈ allLegalMoves gs)
    (hnc1 : m1.isCastle = false) (hnc2 : m2.isCastle = false)
    (hbase : moveToSanBase gs m1 = moveToSanBase gs m2) :
    MoveEquiv m1 m2 := by
  -- Both m1 and m2 are candidates for the SAN base string
  -- The candidates list is a subset of allLegalMoves gs (which has no duplicates by axiom)
  -- We need to show m1 and m2 produce equal MoveEquiv fields
  sorry

-- ============================================================================
-- Main theorem
-- ============================================================================

theorem moveToSAN_unique_full_thm (gs : GameState) (m1 m2 : Move)
    (h1 : m1 ∈ Rules.allLegalMoves gs)
    (h2 : m2 ∈ Rules.allLegalMoves gs)
    (hsan : Parsing.moveToSAN gs m1 = Parsing.moveToSAN gs m2) :
    MoveEquiv m1 m2 := by
  have hbase := SanUniqueness.base_eq_of_moveToSAN_eq gs m1 m2 hsan
  have hisCastle := isCastle_eq_of_base_eq gs m1 m2 hbase
  by_cases hc1 : m1.isCastle = true
  · exact castle_moveEquiv gs m1 m2 h1 h2 hc1 (hisCastle ▸ hc1) hbase
  · have hnc1 : m1.isCastle = false := Bool.eq_false_iff.mpr hc1
    have hnc2 : m2.isCastle = false := by rw [← hisCastle]; exact hnc1
    exact non_castle_moveEquiv gs m1 m2 h1 h2 hnc1 hnc2 hbase

end SanUniquenessFullProof
end Chess
