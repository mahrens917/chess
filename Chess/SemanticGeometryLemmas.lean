import Chess.Spec
import Chess.ParsingProofs

namespace Chess
namespace Rules

open Movement

theorem mem_pieceTargets_king_isKingStep_of_not_castle
    (gs : GameState) (src : Square) (p : Piece) (m : Move)
    (hKing : p.pieceType = PieceType.King) :
    m ∈ pieceTargets gs src p →
    m.isCastle = false →
    Movement.isKingStep src m.toSq := by
  intro hMem hNoCastle
  have hMem' :
      m ∈
        (Movement.kingTargets src).filterMap (fun target =>
          if destinationFriendlyFree gs { piece := p, fromSq := src, toSq := target } then
            match gs.board target with
            | some _ => some { piece := p, fromSq := src, toSq := target, isCapture := true }
            | none => some { piece := p, fromSq := src, toSq := target }
          else
            none) ++
        ([castleMoveIfLegal gs true, castleMoveIfLegal gs false]).filterMap id := by
    simpa [pieceTargets, hKing] using hMem
  cases List.mem_append.1 hMem' with
  | inl hStd =>
      rcases (List.mem_filterMap.1 hStd) with ⟨target, hTargetMem, hSome⟩
      cases hFree : destinationFriendlyFree gs { piece := p, fromSq := src, toSq := target } with
      | false =>
          have : False := by
            simp [hFree] at hSome
          cases this
      | true =>
          cases hBoard : gs.board target <;> simp [hFree, hBoard] at hSome
          · have hEq : m = { piece := p, fromSq := src, toSq := target } := by
              simpa using hSome.symm
            subst hEq
            exact (Movement.mem_kingTargets_iff src target).1 hTargetMem
          · have hEq : m = { piece := p, fromSq := src, toSq := target, isCapture := true } := by
              simpa using hSome.symm
            subst hEq
            exact (Movement.mem_kingTargets_iff src target).1 hTargetMem
  | inr hCastles =>
      -- If this move came from the castle list, it must be a castle move.
      rcases (List.mem_filterMap.1 hCastles) with ⟨opt, hOptMem, hOptEq⟩
      have hOptSome : opt = some m := by
        simpa using hOptEq
      have hOptCases : opt = castleMoveIfLegal gs true ∨ opt = castleMoveIfLegal gs false := by
        simpa using hOptMem
      cases hOptCases with
      | inl hOpt =>
          subst hOpt
          have hCM : castleMoveIfLegal gs true = some m := by
            simpa using hOptSome
          have hIs : m.isCastle = true :=
            Chess.Parsing.castleMoveIfLegal_isCastle_true gs true m hCM
          have : False := by
            simp [hNoCastle] at hIs
          cases this
      | inr hOpt =>
          subst hOpt
          have hCM : castleMoveIfLegal gs false = some m := by
            simpa using hOptSome
          have hIs : m.isCastle = true :=
            Chess.Parsing.castleMoveIfLegal_isCastle_true gs false m hCM
          have : False := by
            simp [hNoCastle] at hIs
          cases this

theorem mem_pieceTargets_knight_isKnightMove
    (gs : GameState) (src : Square) (p : Piece) (m : Move)
    (hKnight : p.pieceType = PieceType.Knight) :
    m ∈ pieceTargets gs src p →
    Movement.isKnightMove src m.toSq := by
  intro hMem
  have hMem' :
      m ∈
        (Movement.knightTargets src).filterMap (fun target =>
          if destinationFriendlyFree gs { piece := p, fromSq := src, toSq := target } then
            match gs.board target with
            | some _ => some { piece := p, fromSq := src, toSq := target, isCapture := true }
            | none => some { piece := p, fromSq := src, toSq := target }
          else
            none) := by
    simpa [pieceTargets, hKnight] using hMem
  rcases (List.mem_filterMap.1 hMem') with ⟨target, hTargetMem, hSome⟩
  cases hFree : destinationFriendlyFree gs { piece := p, fromSq := src, toSq := target } with
  | false =>
      have : False := by
        simp [hFree] at hSome
      cases this
  | true =>
      cases hBoard : gs.board target <;> simp [hFree, hBoard] at hSome
      · have hEq : m = { piece := p, fromSq := src, toSq := target } := by
          simpa using hSome.symm
        subst hEq
        exact (Movement.mem_knightTargets_iff src target).1 hTargetMem
      · have hEq : m = { piece := p, fromSq := src, toSq := target, isCapture := true } := by
          simpa using hSome.symm
        subst hEq
        exact (Movement.mem_knightTargets_iff src target).1 hTargetMem

theorem respectsGeometry_of_pieceTargets_king_not_castle
    (gs : GameState) (src : Square) (p : Piece) (m : Move)
    (hKing : p.pieceType = PieceType.King) :
    m ∈ pieceTargets gs src p →
    m.isCastle = false →
    respectsGeometry gs m := by
  intro hMem hNoCastle
  have hStep : Movement.isKingStep src m.toSq :=
    mem_pieceTargets_king_isKingStep_of_not_castle gs src p m hKing hMem hNoCastle
  have hPieceFrom : m.piece = p ∧ m.fromSq = src :=
    Chess.Parsing.mem_pieceTargets_piece_fromSq_of_not_castle gs src p m hMem hNoCastle
  rcases hPieceFrom with ⟨hPieceEq, hFromEq⟩
  subst hPieceEq
  subst hFromEq
  simp [respectsGeometry, hKing, hNoCastle, hStep]

theorem respectsGeometry_of_pieceTargets_king_castle
    (gs : GameState) (src : Square) (p : Piece) (m : Move)
    (_hKing : p.pieceType = PieceType.King) :
    m ∈ pieceTargets gs src p →
    m.isCastle = true →
    respectsGeometry gs m := by
  intro hMem hCastle
  have hEx := Chess.Parsing.mem_pieceTargets_castle_exists gs src p m hMem hCastle
  rcases hEx with ⟨kingSide, hCM⟩
  have hPieceType : m.piece.pieceType = PieceType.King :=
    Chess.Parsing.castleMoveIfLegal_pieceType gs kingSide m hCM
  have hColor : m.piece.color = gs.toMove :=
    Chess.Parsing.castleMoveIfLegal_pieceColor gs kingSide m hCM
  let cfg : CastleConfig := castleConfig m.piece.color kingSide
  have hTo : m.toSq = cfg.kingTo := by
    -- `castleMoveIfLegal_toSq` uses `gs.toMove`; rewrite with `m.piece.color`.
    have hTo0 := Chess.Parsing.castleMoveIfLegal_toSq gs kingSide m hCM
    simpa [cfg, hColor] using hTo0
  have hFrom : m.fromSq = cfg.kingFrom := by
    have hFrom0 := Chess.Parsing.castleMoveIfLegal_fromSq gs kingSide m hCM
    simpa [cfg, hColor] using hFrom0
  -- Now `respectsGeometry` is immediate from the king/castle branch.
  have hSide :
      cfg = castleConfig m.piece.color true ∨ cfg = castleConfig m.piece.color false := by
    cases kingSide <;> simp [cfg]
  -- Rewrite to the king branch and discharge the existential.
  have hPt : m.piece.pieceType = PieceType.King := hPieceType
  unfold respectsGeometry
  simp [hPt, hCastle]
  refine ⟨cfg, ?_, ?_, hSide⟩
  · exact hFrom.symm
  · exact hTo.symm

theorem respectsGeometry_of_pieceTargets_knight
    (gs : GameState) (src : Square) (p : Piece) (m : Move)
    (hKnight : p.pieceType = PieceType.Knight) :
    m ∈ pieceTargets gs src p →
    respectsGeometry gs m := by
  intro hMem
  have hMove : Movement.isKnightMove src m.toSq :=
    mem_pieceTargets_knight_isKnightMove gs src p m hKnight hMem
  have hPieceFrom : m.piece = p ∧ m.fromSq = src :=
    Chess.Parsing.mem_pieceTargets_piece_fromSq_of_not_castle gs src p m hMem (by
      -- Knights never generate castles.
      have : m.isCastle = false :=
        Chess.Parsing.mem_standardFilterMap_isCastle_false gs src p (Movement.knightTargets src) m (by
          simpa [pieceTargets, hKnight] using hMem)
      exact this)
  rcases hPieceFrom with ⟨hPieceEq, hFromEq⟩
  subst hPieceEq
  subst hFromEq
  simp [respectsGeometry, hKnight, hMove]

end Rules
end Chess
