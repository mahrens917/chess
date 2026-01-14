import Chess.Parsing
import Chess.Game

namespace Chess
namespace Parsing

open Chess

def start_e4_expectedMove : Move :=
  { piece := { pieceType := PieceType.Pawn, color := Color.White }
    fromSq := Square.mkUnsafe 4 1  -- e2
    toSq := Square.mkUnsafe 4 3    -- e4
    isCapture := false
    promotion := none
    isCastle := false
    castleRookFrom := none
    castleRookTo := none
    isEnPassant := false }

def start_after_e4_expectedFEN : String :=
  "rnbqkbnr/pppppppp/8/8/4P3/8/PPPP1PPP/RNBQKBNR b KQkq e3 0 1"

theorem moveFromSAN_start_e4 :
    moveFromSAN buildStartingState "e4" = .ok start_e4_expectedMove := by
  native_decide

theorem applySAN_start_e4_toFEN :
    Except.map toFEN (applySAN buildStartingState "e4") = .ok start_after_e4_expectedFEN := by
  native_decide

end Parsing
end Chess
