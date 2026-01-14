import Chess.Parsing

namespace Chess
namespace Parsing

open Chess

theorem parsePlacement_boardToFenPlacement_startingBoard :
    Except.map Board.fromList (parsePlacement (boardToFenPlacement startingBoard)) =
      .ok startingBoard := by
  native_decide

end Parsing
end Chess

