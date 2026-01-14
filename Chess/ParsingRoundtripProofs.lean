import Chess.Parsing
import Chess.Game

namespace Chess
namespace Parsing

open Chess

theorem toFEN_buildStartingState_eq_startFEN :
    toFEN buildStartingState = startFEN := by
  native_decide

theorem parseFEN_startFEN_eq_buildStartingState :
    parseFEN startFEN = .ok buildStartingState := by
  native_decide

theorem parseFEN_toFEN_buildStartingState :
    parseFEN (toFEN buildStartingState) = .ok buildStartingState := by
  simpa [toFEN_buildStartingState_eq_startFEN] using parseFEN_startFEN_eq_buildStartingState

end Parsing
end Chess
