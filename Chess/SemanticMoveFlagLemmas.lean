import Chess.ParsingProofs
import Chess.Rules

namespace Chess
namespace Rules

theorem mem_pieceTargets_isCastle_implies_king
    (gs : GameState) (src : Square) (p : Piece) (m : Move) :
    m ∈ pieceTargets gs src p →
    m.isCastle = true →
    m.piece.pieceType = PieceType.King := by
  intro hMem hCastle
  cases hPt : p.pieceType with
  | King =>
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
        simpa [pieceTargets, hPt] using hMem
      cases List.mem_append.1 hMem' with
      | inl hStd =>
          have : m.isCastle = false :=
            Chess.Parsing.mem_standardFilterMap_isCastle_false gs src p (Movement.kingTargets src) m hStd
          cases (show False by simpa [hCastle] using this)
      | inr hCastles =>
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
              exact Chess.Parsing.castleMoveIfLegal_pieceType gs true m hCM
          | inr hOpt =>
              subst hOpt
              have hCM : castleMoveIfLegal gs false = some m := by
                simpa using hOptSome
              exact Chess.Parsing.castleMoveIfLegal_pieceType gs false m hCM
  | Queen =>
      have hMem' :
          m ∈
            slidingTargets gs src p
              [(1, 0), (-1, 0), (0, 1), (0, -1), (1, 1), (-1, -1), (1, -1), (-1, 1)] := by
        simpa [pieceTargets, hPt] using hMem
      have : m.isCastle = false :=
        Chess.Parsing.mem_slidingTargets_isCastle_false gs src p _ m hMem'
      cases (show False by simpa [hCastle] using this)
  | Rook =>
      have hMem' :
          m ∈
            slidingTargets gs src p [(1, 0), (-1, 0), (0, 1), (0, -1)] := by
        simpa [pieceTargets, hPt] using hMem
      have : m.isCastle = false :=
        Chess.Parsing.mem_slidingTargets_isCastle_false gs src p _ m hMem'
      cases (show False by simpa [hCastle] using this)
  | Bishop =>
      have hMem' :
          m ∈
            slidingTargets gs src p [(1, 1), (-1, -1), (1, -1), (-1, 1)] := by
        simpa [pieceTargets, hPt] using hMem
      have : m.isCastle = false :=
        Chess.Parsing.mem_slidingTargets_isCastle_false gs src p _ m hMem'
      cases (show False by simpa [hCastle] using this)
  | Knight =>
      have hMem' :
          m ∈
            (Movement.knightTargets src).filterMap (fun target =>
                if destinationFriendlyFree gs { piece := p, fromSq := src, toSq := target } then
                  match gs.board target with
                  | some _ => some { piece := p, fromSq := src, toSq := target, isCapture := true }
                  | none => some { piece := p, fromSq := src, toSq := target }
                else
                  none) := by
        simpa [pieceTargets, hPt] using hMem
      have : m.isCastle = false :=
        Chess.Parsing.mem_standardFilterMap_isCastle_false gs src p (Movement.knightTargets src) m hMem'
      cases (show False by simpa [hCastle] using this)
  | Pawn =>
      have hPawn : p.pieceType = PieceType.Pawn := by simp [hPt]
      have : m.isCastle = false :=
        Chess.Parsing.mem_pawn_pieceTargets_isCastle_false gs src p m hPawn hMem
      cases (show False by simpa [hCastle] using this)

theorem mem_allLegalMoves_isCastle_implies_king (gs : GameState) (m : Move) :
    m ∈ allLegalMoves gs →
    m.isCastle = true →
    m.piece.pieceType = PieceType.King := by
  intro hMem hCastle
  -- Peel `allLegalMoves` back to the generating square and piece.
  unfold allLegalMoves at hMem
  let pins := pinnedSquares gs gs.toMove
  have hFold :
      m ∈ (Square.all).foldr (fun sq acc => legalMovesForCached gs sq pins ++ acc) [] := by
    simpa [allSquares, pins] using hMem
  have hExists :=
    (Chess.Parsing.List.mem_foldr_append_iff (f := fun sq => legalMovesForCached gs sq pins) (b := m) Square.all).1
      hFold
  rcases hExists with ⟨sq, _hSqMem, hInCached⟩
  unfold legalMovesForCached at hInCached
  cases hBoard : gs.board sq with
  | none =>
      simp [hBoard] at hInCached
  | some p =>
      by_cases hTurn : p.color ≠ gs.toMove
      · simp [hBoard, hTurn] at hInCached
      · simp [hBoard, hTurn] at hInCached
        rcases hInCached with ⟨hInTargets, _hSafe, _hPin⟩
        exact mem_pieceTargets_isCastle_implies_king gs sq p m hInTargets hCastle

theorem mem_pieceTargets_isEnPassant_implies_pawn
    (gs : GameState) (src : Square) (p : Piece) (m : Move) :
    m ∈ pieceTargets gs src p →
    m.isEnPassant = true →
    m.piece.pieceType = PieceType.Pawn := by
  intro hMem hEP
  cases hPt : p.pieceType with
  | Pawn =>
      have hPawn : p.pieceType = PieceType.Pawn := by simp [hPt]
      have hPieceFrom := Chess.Parsing.mem_pawn_pieceTargets_piece_fromSq gs src p m hPawn hMem
      have hPiece : m.piece = p := hPieceFrom.1
      simp [hPiece, hPt]
  | King =>
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
        simpa [pieceTargets, hPt] using hMem
      cases List.mem_append.1 hMem' with
      | inl hStd =>
          have : m.isEnPassant = false :=
            Chess.Parsing.mem_standardFilterMap_isEnPassant_false gs src p (Movement.kingTargets src) m hStd
          cases (show False by simpa [hEP] using this)
      | inr hCastles =>
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
              have : m.isEnPassant = false :=
                Chess.Parsing.castleMoveIfLegal_isEnPassant_false gs true m hCM
              cases (show False by simpa [hEP] using this)
          | inr hOpt =>
              subst hOpt
              have hCM : castleMoveIfLegal gs false = some m := by
                simpa using hOptSome
              have : m.isEnPassant = false :=
                Chess.Parsing.castleMoveIfLegal_isEnPassant_false gs false m hCM
              cases (show False by simpa [hEP] using this)
  | Queen =>
      have hMem' :
          m ∈
            slidingTargets gs src p
              [(1, 0), (-1, 0), (0, 1), (0, -1), (1, 1), (-1, -1), (1, -1), (-1, 1)] := by
        simpa [pieceTargets, hPt] using hMem
      have : m.isEnPassant = false :=
        Chess.Parsing.mem_slidingTargets_isEnPassant_false gs src p _ m hMem'
      cases (show False by simpa [hEP] using this)
  | Rook =>
      have hMem' :
          m ∈
            slidingTargets gs src p [(1, 0), (-1, 0), (0, 1), (0, -1)] := by
        simpa [pieceTargets, hPt] using hMem
      have : m.isEnPassant = false :=
        Chess.Parsing.mem_slidingTargets_isEnPassant_false gs src p _ m hMem'
      cases (show False by simpa [hEP] using this)
  | Bishop =>
      have hMem' :
          m ∈
            slidingTargets gs src p [(1, 1), (-1, -1), (1, -1), (-1, 1)] := by
        simpa [pieceTargets, hPt] using hMem
      have : m.isEnPassant = false :=
        Chess.Parsing.mem_slidingTargets_isEnPassant_false gs src p _ m hMem'
      cases (show False by simpa [hEP] using this)
  | Knight =>
      have hMem' :
          m ∈
            (Movement.knightTargets src).filterMap (fun target =>
                if destinationFriendlyFree gs { piece := p, fromSq := src, toSq := target } then
                  match gs.board target with
                  | some _ => some { piece := p, fromSq := src, toSq := target, isCapture := true }
                  | none => some { piece := p, fromSq := src, toSq := target }
                else
                  none) := by
        simpa [pieceTargets, hPt] using hMem
      have : m.isEnPassant = false :=
        Chess.Parsing.mem_standardFilterMap_isEnPassant_false gs src p (Movement.knightTargets src) m hMem'
      cases (show False by simpa [hEP] using this)

theorem mem_allLegalMoves_isEnPassant_implies_pawn (gs : GameState) (m : Move) :
    m ∈ allLegalMoves gs →
    m.isEnPassant = true →
    m.piece.pieceType = PieceType.Pawn := by
  intro hMem hEP
  -- Peel `allLegalMoves` back to the generating square and piece.
  unfold allLegalMoves at hMem
  let pins := pinnedSquares gs gs.toMove
  have hFold :
      m ∈ (Square.all).foldr (fun sq acc => legalMovesForCached gs sq pins ++ acc) [] := by
    simpa [allSquares, pins] using hMem
  have hExists :=
    (Chess.Parsing.List.mem_foldr_append_iff (f := fun sq => legalMovesForCached gs sq pins) (b := m) Square.all).1
      hFold
  rcases hExists with ⟨sq, _hSqMem, hInCached⟩
  unfold legalMovesForCached at hInCached
  cases hBoard : gs.board sq with
  | none =>
      simp [hBoard] at hInCached
  | some p =>
      by_cases hTurn : p.color ≠ gs.toMove
      · simp [hBoard, hTurn] at hInCached
      · simp [hBoard, hTurn] at hInCached
        rcases hInCached with ⟨hInTargets, _hSafe, _hPin⟩
        exact mem_pieceTargets_isEnPassant_implies_pawn gs sq p m hInTargets hEP

end Rules
end Chess
