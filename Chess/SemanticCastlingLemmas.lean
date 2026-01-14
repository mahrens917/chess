import Chess.Spec
import Chess.ParsingProofs

namespace Chess
namespace Rules

open Parsing

theorem castleMoveIfLegal_implies_semantic_clause (gs : GameState) (kingSide : Bool) (m : Move) :
    castleMoveIfLegal gs kingSide = some m →
    ∃ ks : Bool,
      let cfg := castleConfig m.piece.color ks
      cfg.kingFrom = m.fromSq ∧
      cfg.kingTo = m.toSq ∧
      m.castleRookFrom = some cfg.rookFrom ∧
      m.castleRookTo = some cfg.rookTo ∧
      castleRight gs.castlingRights m.piece.color ks ∧
      gs.board cfg.kingFrom = some m.piece ∧
      (∃ rook : Piece,
        gs.board cfg.rookFrom = some rook ∧
        rook.pieceType = PieceType.Rook ∧
        rook.color = m.piece.color) ∧
      cfg.emptySquares.all (isEmpty gs.board) ∧
      cfg.checkSquares.all (fun sq =>
        ¬(inCheck (gs.board.update cfg.kingFrom none |>.update sq (some m.piece)) m.piece.color)) := by
  intro hCM
  have hColor : m.piece.color = gs.toMove :=
    Chess.Parsing.castleMoveIfLegal_pieceColor gs kingSide m hCM
  have hKingFrom : gs.board (castleConfig gs.toMove kingSide).kingFrom = some m.piece :=
    Chess.Parsing.castleMoveIfLegal_kingFrom_piece gs kingSide m hCM
  -- Unfold the definition and extract the successful branch.
  let c := gs.toMove
  let cfg0 := castleConfig c kingSide
  have h0 :
      (if castleRight gs.castlingRights c kingSide then
          match gs.board cfg0.kingFrom, gs.board cfg0.rookFrom with
          | some k, some r =>
              if k.pieceType = PieceType.King ∧ k.color = c ∧ r.pieceType = PieceType.Rook ∧ r.color = c then
                let pathEmpty := cfg0.emptySquares.all (isEmpty gs.board)
                let safe := cfg0.checkSquares.all (fun sq =>
                  !(inCheck (gs.board.update cfg0.kingFrom none |>.update sq (some k)) c))
                if pathEmpty && safe then
                  some
                    { piece := k
                      fromSq := cfg0.kingFrom
                      toSq := cfg0.kingTo
                      isCastle := true
                      castleRookFrom := some cfg0.rookFrom
                      castleRookTo := some cfg0.rookTo }
                else
                  none
              else
                none
          | _, _ => none
        else
          none) = some m := by
    simpa [castleMoveIfLegal, c, cfg0] using hCM
  cases hRight : castleRight gs.castlingRights c kingSide with
  | false =>
      cases (show False by simpa [hRight] using h0)
  | true =>
      have h1 :
          (match gs.board cfg0.kingFrom, gs.board cfg0.rookFrom with
          | some k, some r =>
              if k.pieceType = PieceType.King ∧ k.color = c ∧ r.pieceType = PieceType.Rook ∧ r.color = c then
                let pathEmpty := cfg0.emptySquares.all (isEmpty gs.board)
                let safe := cfg0.checkSquares.all (fun sq =>
                  !(inCheck (gs.board.update cfg0.kingFrom none |>.update sq (some k)) c))
                if pathEmpty && safe then
                  some
                    { piece := k
                      fromSq := cfg0.kingFrom
                      toSq := cfg0.kingTo
                      isCastle := true
                      castleRookFrom := some cfg0.rookFrom
                      castleRookTo := some cfg0.rookTo }
                else
                  none
              else
                none
          | _, _ => none) = some m := by
        simpa [hRight] using h0
      revert h1
      cases hK : gs.board cfg0.kingFrom with
      | none =>
          intro h1
          cases (show False by simpa [hK] using h1)
      | some k =>
          cases hR : gs.board cfg0.rookFrom with
          | none =>
              intro h1
              cases (show False by simpa [hK, hR] using h1)
          | some r =>
              intro h1
              by_cases hPieces :
                  k.pieceType = PieceType.King ∧ k.color = c ∧ r.pieceType = PieceType.Rook ∧ r.color = c
              · have h2 :
                    (let pathEmpty := cfg0.emptySquares.all (isEmpty gs.board)
                    let safe := cfg0.checkSquares.all (fun sq =>
                      !(inCheck (gs.board.update cfg0.kingFrom none |>.update sq (some k)) c))
                    if pathEmpty && safe then
                      some
                        { piece := k
                          fromSq := cfg0.kingFrom
                          toSq := cfg0.kingTo
                          isCastle := true
                          castleRookFrom := some cfg0.rookFrom
                          castleRookTo := some cfg0.rookTo }
                    else
                      none) = some m := by
                  simpa [hK, hR, hPieces] using h1
                revert h2
                let pathEmpty := cfg0.emptySquares.all (isEmpty gs.board)
                let safe := cfg0.checkSquares.all (fun sq =>
                  !(inCheck (gs.board.update cfg0.kingFrom none |>.update sq (some k)) c))
                cases hOk : (pathEmpty && safe) with
                | false =>
                    intro h2
                    cases (show False by simpa [pathEmpty, safe, hOk] using h2)
                | true =>
                    intro h2
                    have hMove :
                        { piece := k
                          fromSq := cfg0.kingFrom
                          toSq := cfg0.kingTo
                          isCastle := true
                          castleRookFrom := some cfg0.rookFrom
                          castleRookTo := some cfg0.rookTo } = m := by
                      simpa [pathEmpty, safe, hOk] using h2
                    have hPiece : m.piece = k := by
                      simpa using congrArg Move.piece hMove.symm
                    have hFromSq : m.fromSq = cfg0.kingFrom := by
                      simpa using congrArg Move.fromSq hMove.symm
                    have hToSq : m.toSq = cfg0.kingTo := by
                      simpa using congrArg Move.toSq hMove.symm
                    have hRookFrom : m.castleRookFrom = some cfg0.rookFrom := by
                      simpa using congrArg Move.castleRookFrom hMove.symm
                    have hRookTo : m.castleRookTo = some cfg0.rookTo := by
                      simpa using congrArg Move.castleRookTo hMove.symm
                    -- Discharge the semantic clause by choosing this `kingSide`.
                    refine ⟨kingSide, ?_⟩
                    -- Rewrite `cfg` to use `m.piece.color`, which is `c`.
                    have hCfgColor : m.piece.color = c := hColor
                    -- Provide the required fields.
                    dsimp
                    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
                    · -- cfg.kingFrom matches m.fromSq
                      -- Use the move equality facts and rewrite `cfg` color.
                      simpa [hCfgColor, cfg0, c] using hFromSq.symm
                    · -- cfg.kingTo matches m.toSq
                      simpa [hCfgColor, cfg0, c] using hToSq.symm
                    · -- rook-from field matches config
                      simpa [hCfgColor, cfg0, c] using hRookFrom
                    · -- rook-to field matches config
                      simpa [hCfgColor, cfg0, c] using hRookTo
                    · -- castling right
                      simpa [hCfgColor, c] using hRight
                    · -- king is on the start square
                      -- `cfg0.kingFrom = castleConfig c kingSide`.kingFrom.
                      have : gs.board cfg0.kingFrom = some m.piece := by
                        simpa [cfg0] using hKingFrom
                      simpa [hCfgColor, cfg0, c] using this
                    · -- rook exists and matches
                      refine ⟨r, ?_, ?_, ?_⟩
                      ·
                        have : gs.board cfg0.rookFrom = some r := by
                          simpa [cfg0] using hR
                        simpa [cfg0, hCfgColor, c] using this
                      · exact hPieces.2.2.1
                      · -- rook color equals king color (= c)
                        have : r.color = c := hPieces.2.2.2
                        simpa [hCfgColor, c] using this
                    · -- pathEmpty
                      have : cfg0.emptySquares.all (isEmpty gs.board) = true := by
                        -- `pathEmpty && safe = true` implies `pathEmpty = true`.
                        have : pathEmpty = true := by
                          have : (pathEmpty && safe) = true := by simpa using hOk
                          have hPair : pathEmpty = true ∧ safe = true :=
                            Eq.mp (Bool.and_eq_true pathEmpty safe) this
                          exact hPair.1
                        exact this
                      simpa [hCfgColor, cfg0, c] using this
                    · -- safe squares (convert `!inCheck = true` to `¬ inCheck`)
                      have : safe = true := by
                        have : (pathEmpty && safe) = true := by simpa using hOk
                        have hPair : pathEmpty = true ∧ safe = true :=
                          Eq.mp (Bool.and_eq_true pathEmpty safe) this
                        exact hPair.2
                      -- Expand `safe` and rewrite.
                      -- `simp` turns `!(inCheck ...) = true` into `inCheck ... = false`,
                      -- which is definitionally `¬ inCheck ...`.
                      -- We also rewrite `k` to `m.piece`.
                      have hk : k = m.piece := by
                        simpa [hPiece] using rfl
                      subst hk
                      simpa [safe, hCfgColor, cfg0, c] using this
              ·
                cases (show False by simpa [hK, hR, hPieces] using h1)

end Rules
end Chess
