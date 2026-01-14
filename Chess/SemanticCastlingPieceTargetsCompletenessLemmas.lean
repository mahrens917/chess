import Init.Omega
import Chess.Spec
import Chess.SemanticPawnLemmas

namespace Chess
namespace Rules

open Movement

private theorem decide_not_eq_true_eq_not (b : Bool) : decide (¬b = true) = (!b) := by
  cases b <;> decide

theorem fideLegalSemantic_implies_mem_pieceTargets_king_castle (gs : GameState) (m : Move) :
    fideLegalSemantic gs m →
    m.isCastle = true →
    m ∈ pieceTargets gs m.fromSq m.piece := by
  intro hSem hIsCastle
  rcases hSem with
    ⟨hTurn, hFrom, hGeom, _hDest, hCapSpec, _hNotCheck, _hPromoFwd, hPromoBack, hCastleClause, hEPFlag,
      hCastleFlag, _hRookFields⟩

  have hCastle : m.isCastle := by
    simp [hIsCastle]
  have hKing : m.piece.pieceType = PieceType.King := hCastleFlag hCastle
  have hEPFalse : m.isEnPassant = false := by
    cases hEP : m.isEnPassant with
    | false => rfl
    | true =>
        have hPawn : m.piece.pieceType = PieceType.Pawn := hEPFlag (by simp [hEP])
        have : False := by
          have : (PieceType.King : PieceType) = PieceType.Pawn := by simpa [hKing] using hPawn.symm
          cases this
        cases this
  have hPromoNone : m.promotion = none := by
    cases hProm : m.promotion with
    | none => rfl
    | some pt =>
        have hSome : m.promotion.isSome = true := by simp [hProm]
        have hPawn : m.piece.pieceType = PieceType.Pawn := (hPromoBack hSome).1
        have : False := by
          have : (PieceType.King : PieceType) = PieceType.Pawn := by simpa [hKing] using hPawn.symm
          cases this
        cases this

  rcases hCastleClause hCastle with ⟨kingSide, hAll⟩
  dsimp at hAll
  rcases hAll with
    ⟨hCfgFrom, hCfgTo, hRookFromField, hRookToField, hRight, hKingOn, hRookEx, hEmpty, hSafe⟩

  let cfg : CastleConfig := castleConfig m.piece.color kingSide

  have hRightEq : castleRight gs.castlingRights gs.toMove kingSide = true := by
    have hRight' : castleRight gs.castlingRights m.piece.color kingSide = true := by
      cases hR : castleRight gs.castlingRights m.piece.color kingSide with
      | false =>
          cases (show False by simpa [hR] using hRight)
      | true => rfl
    simpa [hTurn] using hRight'

  have hKingOn' : gs.board (castleConfig gs.toMove kingSide).kingFrom = some m.piece := by
    simpa [hTurn] using hKingOn

  rcases hRookEx with ⟨rook, hRookOn, hRookType, hRookColor⟩
  have hRookOn' : gs.board (castleConfig gs.toMove kingSide).rookFrom = some rook := by
    simpa [hTurn] using hRookOn

  have hPieces :
      m.piece.pieceType = PieceType.King ∧ m.piece.color = gs.toMove ∧
        rook.pieceType = PieceType.Rook ∧ rook.color = gs.toMove := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact hKing
    · exact hTurn
    · exact hRookType
    · simpa [hTurn] using hRookColor

  have hPathEmpty : (castleConfig gs.toMove kingSide).emptySquares.all (isEmpty gs.board) = true := by
    simpa [hTurn] using (show (castleConfig m.piece.color kingSide).emptySquares.all (isEmpty gs.board) = true from hEmpty)

  have hSafeSquares :
      (castleConfig gs.toMove kingSide).checkSquares.all (fun sq =>
          !(inCheck (gs.board.update (castleConfig gs.toMove kingSide).kingFrom none |>.update sq (some m.piece))
                gs.toMove)) =
        true := by
    have hSafe0 :
        (castleConfig m.piece.color kingSide).checkSquares.all (fun sq =>
            decide
                (¬inCheck
                      (gs.board.update (castleConfig m.piece.color kingSide).kingFrom none |>.update sq (some m.piece))
                      m.piece.color =
                    true)) =
          true := by
      simpa using (show (castleConfig m.piece.color kingSide).checkSquares.all (fun sq =>
            ¬(inCheck
                  (gs.board.update (castleConfig m.piece.color kingSide).kingFrom none |>.update sq (some m.piece))
                  m.piece.color)) = true from hSafe)
    have hSafe1 :
        (castleConfig m.piece.color kingSide).checkSquares.all (fun sq =>
            !(inCheck
                  (gs.board.update (castleConfig m.piece.color kingSide).kingFrom none |>.update sq (some m.piece))
                  m.piece.color)) =
          true := by
      -- Rewrite the predicate pointwise from `decide (¬b = true)` to `!b`.
      have hPoint :
          ∀ sq,
            decide
                (¬inCheck
                      (gs.board.update (castleConfig m.piece.color kingSide).kingFrom none |>.update sq (some m.piece))
                      m.piece.color =
                    true) =
              !(inCheck
                    (gs.board.update (castleConfig m.piece.color kingSide).kingFrom none |>.update sq (some m.piece))
                    m.piece.color) := by
        intro sq
        simpa using
          (decide_not_eq_true_eq_not
              (inCheck
                (gs.board.update (castleConfig m.piece.color kingSide).kingFrom none |>.update sq (some m.piece))
                m.piece.color))
      have := List.all_congr (l₁ := (castleConfig m.piece.color kingSide).checkSquares)
        (l₂ := (castleConfig m.piece.color kingSide).checkSquares) rfl hPoint
      simpa using (Eq.mp (by simpa using this) hSafe0)
    simpa [hTurn] using hSafe1

  have hCapFalse : m.isCapture = false := by
    -- Target square is in `emptySquares`, so `board m.toSq = none`.
    have hToSq' : m.toSq = (castleConfig gs.toMove kingSide).kingTo := by
      simpa [cfg, hTurn] using hCfgTo.symm
    have hKingToMem :
        (castleConfig gs.toMove kingSide).kingTo ∈ (castleConfig gs.toMove kingSide).emptySquares := by
      cases gs.toMove <;> cases kingSide <;> decide
    have hEmptyKingTo : isEmpty gs.board (castleConfig gs.toMove kingSide).kingTo = true := by
      exact (List.all_eq_true.1 hPathEmpty) _ hKingToMem
    have hBoardTo : gs.board m.toSq = none := by
      simpa [isEmpty, hToSq'] using hEmptyKingTo
    have hNoEnemy :
        ¬(∃ p, gs.board m.toSq = some p ∧ p.color ≠ m.piece.color) := by
      intro hEx
      rcases hEx with ⟨p, hAt, _hNe⟩
      cases (show False by simpa [hBoardTo] using hAt)
    have hNoEP : ¬m.isEnPassant := by simp [hEPFalse]
    cases hCap : m.isCapture with
    | false => rfl
    | true =>
        have hRhs : (∃ p, gs.board m.toSq = some p ∧ p.color ≠ m.piece.color) ∨ m.isEnPassant := by
          have := (hCapSpec.1 hCap)
          simpa using this
        cases hRhs with
        | inl hEnemy => cases hNoEnemy hEnemy
        | inr hEP => cases hNoEP hEP

  have hCastleMoveIfLegal : castleMoveIfLegal gs kingSide = some m := by
    -- Unfold and solve the successful branch.
    have hFromSq' : m.fromSq = (castleConfig gs.toMove kingSide).kingFrom := by
      simpa [cfg, hTurn] using hCfgFrom.symm
    have hToSq' : m.toSq = (castleConfig gs.toMove kingSide).kingTo := by
      simpa [cfg, hTurn] using hCfgTo.symm
    have hRookFrom' : m.castleRookFrom = some (castleConfig gs.toMove kingSide).rookFrom := by
      simpa [cfg, hTurn] using hRookFromField
    have hRookTo' : m.castleRookTo = some (castleConfig gs.toMove kingSide).rookTo := by
      simpa [cfg, hTurn] using hRookToField
    have hMoveEq :
        ({ piece := m.piece
           fromSq := (castleConfig gs.toMove kingSide).kingFrom
           toSq := (castleConfig gs.toMove kingSide).kingTo
           isCastle := true
           castleRookFrom := some (castleConfig gs.toMove kingSide).rookFrom
           castleRookTo := some (castleConfig gs.toMove kingSide).rookTo } : Move) =
          m := by
      apply Move.ext <;> simp [hFromSq', hToSq', hCapFalse, hPromoNone, hIsCastle, hRookFrom', hRookTo', hEPFalse]
    -- Now unfold `castleMoveIfLegal` and `simp` to the successful branch.
    unfold castleMoveIfLegal
    simp [hRightEq, hKingOn', hRookOn', hPieces, hPathEmpty, hSafeSquares, hMoveEq]

  -- Finish: `pieceTargets` for king includes `castleMoveIfLegal` outputs.
  unfold pieceTargets
  simp [hKing]
  refine Or.inr ?_
  cases kingSide <;> simp [hCastleMoveIfLegal]

end Rules
end Chess
