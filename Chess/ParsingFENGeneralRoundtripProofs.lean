import Chess.Game
import Chess.Parsing
import Chess.ParsingFENSplitProofs
import Chess.ParsingFieldRoundtripProofs
import Chess.ParsingNatFieldRoundtripProofs
import Chess.ParsingPlacementGeneralRoundtripProofs

namespace Chess
namespace Parsing

open Chess

theorem parseFEN_toFEN_of_validate_of_split (gs : GameState)
    (hValid :
      validateFEN gs.board gs.toMove gs.castlingRights gs.enPassantTarget gs.halfMoveClock = .ok ()) :
    parseFEN (toFEN gs) = seedHistoryFromFEN { gs with result := none } := by
  -- Unfold and parse fields.
  unfold parseFEN
  have hFields := splitFenFields_toFEN gs
  -- Rewrite the field split to the expected 6-tuple.
  simp [hFields]
  -- Placement: parse then rebuild the board.
  have hPlacement :
      Except.map Board.fromList (parsePlacement (boardToFenPlacement gs.board)) = .ok gs.board :=
    parsePlacement_boardToFenPlacement_roundtrip gs.board
  -- Convert that into the shape used by `parseFEN`.
  cases hPieces : parsePlacement (boardToFenPlacement gs.board) with
  | error e =>
      -- Contradiction: mapping `Board.fromList` would also be an error.
      have hMap : Except.map Board.fromList (parsePlacement (boardToFenPlacement gs.board)) = .error e := by
        simp [hPieces, Except.map]
      have : False := by
        have hEq : (.error e : Except String Board) = .ok gs.board := by
          simpa [hMap] using hPlacement
        cases hEq
      cases this
  | ok pieces =>
      have hBoard : Board.fromList pieces = gs.board := by
        have : Except.map Board.fromList (Except.ok pieces : Except String (List (Square × Piece))) = .ok gs.board := by
          simpa [hPieces] using hPlacement
        simpa using congrArg (fun t =>
          match t with
          | Except.ok b => b
          | Except.error _ => Board.empty) this
      -- Discharge field roundtrips and the validation call.
      have hActive : parseActiveColor (if gs.toMove = Color.White then "w" else "b") = .ok gs.toMove :=
        parseActiveColor_roundtrip gs.toMove
      have hCastling : parseCastlingRights (castlingToFen gs.castlingRights) = gs.castlingRights :=
        parseCastlingRights_roundtrip gs.castlingRights
      have hEp :
          parseEnPassant (gs.enPassantTarget.map (fun sq => sq.algebraic) |>.getD "-") =
            .ok gs.enPassantTarget := by
        cases h : gs.enPassantTarget with
        | none =>
            simpa [h] using parseEnPassant_dash_roundtrip
        | some sq =>
            simpa [h] using parseEnPassant_algebraic_roundtrip sq
      -- The `validateFEN` call matches the assumption after rewriting `board`.
      have hValid' :
          validateFEN (Board.fromList pieces) gs.toMove gs.castlingRights gs.enPassantTarget gs.halfMoveClock =
            .ok () := by
        simpa [hBoard] using hValid
      -- Normalize the post-parse seeded state, noting `toFEN` does not serialize `result` and `seedHistory`
      -- overwrites any existing `history`.
      let gsParsed : GameState :=
        { board := Board.fromList pieces
          toMove := gs.toMove
          halfMoveClock := gs.halfMoveClock
          fullMoveNumber := gs.fullMoveNumber
          enPassantTarget := gs.enPassantTarget
          castlingRights := gs.castlingRights
          history := []
          result := none }
      have hSeed : seedHistoryFromFEN gsParsed = seedHistoryFromFEN { gs with result := none } := by
        simp [gsParsed, seedHistoryFromFEN, seedHistory, positionSnapshot, hBoard]
      -- Reduce the `do`-block and discharge `validateFEN`.
      simp (config := { failIfUnchanged := false })
        [Except.instMonad, Except.bind, Except.map, hActive, hEp,
          parseNatField_toString_roundtrip, hCastling, hValid', gsParsed]
      exact hSeed

end Parsing
end Chess
