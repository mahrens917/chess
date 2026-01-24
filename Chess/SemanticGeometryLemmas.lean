import Chess.Spec
import Chess.ParsingProofs

namespace Chess
namespace Rules

open Movement

-- Helper: castleMoveIfLegal always produces moves with isCastle = true
private theorem castleMoveIfLegal_isCastle_true (gs : GameState) (kingSide : Bool) (m : Move) :
    castleMoveIfLegal gs kingSide = some m → m.isCastle = true := by
  intro h
  simp only [castleMoveIfLegal] at h
  -- Split on outer if (castleRight check)
  split at h
  case isTrue hRight =>
    -- Split on match (king and rook presence)
    split at h
    case h_1 k r heqK heqR =>
      -- Split on piece condition if
      split at h
      case isTrue hPieces =>
        -- Split on pathEmpty && safe
        split at h
        case isTrue hPath =>
          -- This is the only case that returns some m
          simp only [Option.some.injEq] at h
          subst h
          rfl
        case isFalse hPath => simp at h
      case isFalse hPieces => simp at h
    case h_2 => simp at h
  case isFalse hRight => simp at h

-- Helper: castleMoveIfLegal produces moves with correct castle config geometry
private theorem castleMoveIfLegal_config (gs : GameState) (kingSide : Bool) (m : Move) :
    castleMoveIfLegal gs kingSide = some m →
    m.fromSq = (castleConfig gs.toMove kingSide).kingFrom ∧
    m.toSq = (castleConfig gs.toMove kingSide).kingTo ∧
    m.piece.color = gs.toMove := by
  intro h
  simp only [castleMoveIfLegal] at h
  split at h
  case isTrue hRight =>
    split at h
    case h_1 k r heqK heqR =>
      split at h
      case isTrue hPieces =>
        split at h
        case isTrue hPath =>
          simp only [Option.some.injEq] at h
          subst h
          exact ⟨rfl, rfl, hPieces.2.1⟩
        case isFalse hPath => simp at h
      case isFalse hPieces => simp at h
    case h_2 => simp at h
  case isFalse hRight => simp at h

-- Helper: moves from the castle list have isCastle = true
private theorem mem_castle_list_isCastle_true (gs : GameState) (m : Move) :
    m ∈ ([castleMoveIfLegal gs true, castleMoveIfLegal gs false].filterMap id) →
    m.isCastle = true := by
  intro h
  simp only [List.mem_filterMap, List.mem_cons, id_eq] at h
  obtain ⟨opt, hOpt, hSome⟩ := h
  rcases hOpt with hKS | hQS | hNil
  · rw [hKS] at hSome
    exact castleMoveIfLegal_isCastle_true gs true m hSome
  · rw [hQS] at hSome
    exact castleMoveIfLegal_isCastle_true gs false m hSome
  · simp at hNil

theorem mem_pieceTargets_king_isKingStep_of_not_castle
    (gs : GameState) (src : Square) (p : Piece) (m : Move)
    (hKing : p.pieceType = PieceType.King) :
    m ∈ pieceTargets gs src p →
    m.isCastle = false →
    Movement.isKingStep src m.toSq := by
  intro hMem hNotCastle
  -- Unfold pieceTargets for King case
  unfold pieceTargets at hMem
  simp only [hKing] at hMem
  -- hMem : m ∈ standard ++ castles
  -- Split into standard or castles
  rw [List.mem_append] at hMem
  cases hMem with
  | inl hStandard =>
    -- m is from standard = kingTargets src |>.filterMap ...
    -- Extract that m.toSq was in kingTargets src
    simp only [List.mem_filterMap] at hStandard
    obtain ⟨target, hTarget, hOpt⟩ := hStandard
    -- hTarget : target ∈ kingTargets src
    -- hOpt : (if ... then match ... else none) = some m
    -- From the filterMap, m.toSq = target
    split at hOpt
    · rename_i hFree
      split at hOpt
      · -- Board has some piece at target (capture case)
        injection hOpt with hm
        rw [← hm]
        simp only
        exact (Movement.mem_kingTargets_iff src target).1 hTarget
      · -- Board is empty at target (non-capture case)
        injection hOpt with hm
        rw [← hm]
        simp only
        exact (Movement.mem_kingTargets_iff src target).1 hTarget
    · simp at hOpt
  | inr hCastles =>
    -- m is from castles, but m.isCastle = false, contradiction
    have hTrue := mem_castle_list_isCastle_true gs m hCastles
    simp [hTrue] at hNotCastle

theorem mem_pieceTargets_knight_isKnightMove
    (gs : GameState) (src : Square) (p : Piece) (m : Move)
    (hKnight : p.pieceType = PieceType.Knight) :
    m ∈ pieceTargets gs src p →
    Movement.isKnightMove src m.toSq := by
  intro hMem
  -- Unfold pieceTargets for Knight case
  unfold pieceTargets at hMem
  simp only [hKnight] at hMem
  -- hMem : m ∈ knightTargets src |>.filterMap ...
  simp only [List.mem_filterMap] at hMem
  obtain ⟨target, hTarget, hOpt⟩ := hMem
  -- hTarget : target ∈ knightTargets src
  -- Extract that m.toSq = target
  split at hOpt
  · rename_i hFree
    split at hOpt
    · -- Board has some piece at target (capture case)
      injection hOpt with hm
      rw [← hm]
      simp only
      exact (Movement.mem_knightTargets_iff src target).1 hTarget
    · -- Board is empty at target (non-capture case)
      injection hOpt with hm
      rw [← hm]
      simp only
      exact (Movement.mem_knightTargets_iff src target).1 hTarget
  · simp at hOpt

-- Helper: standard king moves have m.piece = p and m.fromSq = src
private theorem mem_standard_king_filterMap
    (gs : GameState) (src : Square) (p : Piece) (m : Move) (target : Square)
    (hOpt : (if destinationFriendlyFree gs { piece := p, fromSq := src, toSq := target }
             then match gs.board target with
               | some _ => some { piece := p, fromSq := src, toSq := target, isCapture := true }
               | none => some { piece := p, fromSq := src, toSq := target }
             else none) = some m) :
    m.piece = p ∧ m.fromSq = src ∧ m.toSq = target := by
  split at hOpt
  · split at hOpt
    · injection hOpt with hm; rw [← hm]; exact ⟨rfl, rfl, rfl⟩
    · injection hOpt with hm; rw [← hm]; exact ⟨rfl, rfl, rfl⟩
  · simp at hOpt

-- Helper: standard king moves have isCastle = false
private theorem mem_standard_king_filterMap_not_castle
    (gs : GameState) (src : Square) (p : Piece) (m : Move) (target : Square)
    (hOpt : (if destinationFriendlyFree gs { piece := p, fromSq := src, toSq := target }
             then match gs.board target with
               | some _ => some { piece := p, fromSq := src, toSq := target, isCapture := true }
               | none => some { piece := p, fromSq := src, toSq := target }
             else none) = some m) :
    m.isCastle = false := by
  split at hOpt
  · split at hOpt
    · simp only [Option.some.injEq] at hOpt; subst hOpt; rfl
    · simp only [Option.some.injEq] at hOpt; subst hOpt; rfl
  · simp at hOpt

-- Helper: castle list membership implies castleMoveIfLegal for some side
private theorem mem_castle_list_exists_kingSide (gs : GameState) (m : Move) :
    m ∈ ([castleMoveIfLegal gs true, castleMoveIfLegal gs false].filterMap id) →
    (castleMoveIfLegal gs true = some m) ∨ (castleMoveIfLegal gs false = some m) := by
  intro h
  simp only [List.mem_filterMap, List.mem_cons, id_eq] at h
  obtain ⟨opt, hOpt, hSome⟩ := h
  rcases hOpt with hKS | hQS | hNil
  · left; rw [hKS] at hSome; exact hSome
  · right; rw [hQS] at hSome; exact hSome
  · simp at hNil

theorem respectsGeometry_of_pieceTargets_king_not_castle
    (gs : GameState) (src : Square) (p : Piece) (m : Move)
    (hKing : p.pieceType = PieceType.King) :
    m ∈ pieceTargets gs src p →
    m.isCastle = false →
    respectsGeometry gs m := by
  intro hMem hNotCastle
  have hStep := mem_pieceTargets_king_isKingStep_of_not_castle gs src p m hKing hMem hNotCastle
  -- Unfold pieceTargets for King case
  unfold pieceTargets at hMem
  simp only [hKing] at hMem
  rw [List.mem_append] at hMem
  cases hMem with
  | inl hStandard =>
    -- m is from standard = kingTargets src |>.filterMap ...
    simp only [List.mem_filterMap] at hStandard
    obtain ⟨target, _, hOpt⟩ := hStandard
    have ⟨hPiece, hFrom, _⟩ := mem_standard_king_filterMap gs src p m target hOpt
    unfold respectsGeometry
    simp only [hPiece, hKing, hNotCastle, hFrom]
    exact hStep
  | inr hCastles =>
    -- m from castles but isCastle = false - contradiction
    have hTrue := mem_castle_list_isCastle_true gs m hCastles
    simp [hTrue] at hNotCastle

theorem respectsGeometry_of_pieceTargets_king_castle
    (gs : GameState) (src : Square) (p : Piece) (m : Move)
    (hKing : p.pieceType = PieceType.King) :
    m ∈ pieceTargets gs src p →
    m.isCastle = true →
    respectsGeometry gs m := by
  intro hMem hCastle
  -- Unfold pieceTargets for King case
  unfold pieceTargets at hMem
  simp only [hKing] at hMem
  rw [List.mem_append] at hMem
  cases hMem with
  | inl hStandard =>
    -- m is from standard moves, but standard moves have isCastle = false
    simp only [List.mem_filterMap] at hStandard
    obtain ⟨target, _, hOpt⟩ := hStandard
    have hFalse := mem_standard_king_filterMap_not_castle gs src p m target hOpt
    simp [hFalse] at hCastle
  | inr hCastles =>
    -- m is from castle list
    have hExists := mem_castle_list_exists_kingSide gs m hCastles
    unfold respectsGeometry
    -- Get m.piece.pieceType from the castle list membership
    -- First extract m.piece.color and geometry from whichever side
    rcases hExists with hKS | hQS
    · -- King side castle
      have ⟨hFrom, hTo, hColor⟩ := castleMoveIfLegal_config gs true m hKS
      -- Need to show m.piece.pieceType = King
      -- From castleMoveIfLegal, the piece is the king at cfg.kingFrom
      simp only [castleMoveIfLegal] at hKS
      split at hKS
      case isTrue hRight =>
        split at hKS
        case h_1 k r heqK heqR =>
          split at hKS
          case isTrue hPieces =>
            split at hKS
            case isTrue hPath =>
              simp only [Option.some.injEq] at hKS
              subst hKS
              simp only [hPieces.1, ↓reduceIte]
              -- k.color = gs.toMove from hPieces.2.1
              rw [← hPieces.2.1]
              exact ⟨castleConfig k.color true, rfl, rfl, Or.inl rfl⟩
            case isFalse hPath => simp at hKS
          case isFalse hPieces => simp at hKS
        case h_2 => simp at hKS
      case isFalse hRight => simp at hKS
    · -- Queen side castle
      have ⟨hFrom, hTo, hColor⟩ := castleMoveIfLegal_config gs false m hQS
      simp only [castleMoveIfLegal] at hQS
      split at hQS
      case isTrue hRight =>
        split at hQS
        case h_1 k r heqK heqR =>
          split at hQS
          case isTrue hPieces =>
            split at hQS
            case isTrue hPath =>
              simp only [Option.some.injEq] at hQS
              subst hQS
              simp only [hPieces.1, ↓reduceIte]
              rw [← hPieces.2.1]
              exact ⟨castleConfig k.color false, rfl, rfl, Or.inr rfl⟩
            case isFalse hPath => simp at hQS
          case isFalse hPieces => simp at hQS
        case h_2 => simp at hQS
      case isFalse hRight => simp at hQS

-- Helper: standard knight moves have m.piece = p and m.fromSq = src
private theorem mem_standard_knight_filterMap
    (gs : GameState) (src : Square) (p : Piece) (m : Move) (target : Square)
    (hOpt : (if destinationFriendlyFree gs { piece := p, fromSq := src, toSq := target }
             then match gs.board target with
               | some _ => some { piece := p, fromSq := src, toSq := target, isCapture := true }
               | none => some { piece := p, fromSq := src, toSq := target }
             else none) = some m) :
    m.piece = p ∧ m.fromSq = src ∧ m.toSq = target := by
  split at hOpt
  · split at hOpt
    · injection hOpt with hm; rw [← hm]; exact ⟨rfl, rfl, rfl⟩
    · injection hOpt with hm; rw [← hm]; exact ⟨rfl, rfl, rfl⟩
  · simp at hOpt

theorem respectsGeometry_of_pieceTargets_knight
    (gs : GameState) (src : Square) (p : Piece) (m : Move)
    (hKnight : p.pieceType = PieceType.Knight) :
    m ∈ pieceTargets gs src p →
    respectsGeometry gs m := by
  intro hMem
  have hMove := mem_pieceTargets_knight_isKnightMove gs src p m hKnight hMem
  -- Extract m.piece.pieceType = Knight and m.fromSq = src from pieceTargets structure
  unfold pieceTargets at hMem
  simp only [hKnight] at hMem
  simp only [List.mem_filterMap] at hMem
  obtain ⟨target, _, hOpt⟩ := hMem
  have ⟨hPiece, hFrom, _⟩ := mem_standard_knight_filterMap gs src p m target hOpt
  -- Prove respectsGeometry
  unfold respectsGeometry
  simp only [hPiece, hKnight, hFrom]
  exact hMove

end Rules
end Chess
