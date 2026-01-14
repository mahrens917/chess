import Chess.Parsing

namespace Chess
namespace Parsing

open Chess

def fenAfterSAN (fen san : String) : Except String String := do
  let gs ← parseFEN fen
  let gs' ← applySAN gs san
  return toFEN gs'

def epFixtureFen : String :=
  "k7/8/8/3pP3/8/8/8/4K3 w - d6 0 1"

def epFixtureSan : String :=
  "exd6"

def epFixtureExpectedFEN : String :=
  "k7/8/3P4/8/8/8/8/4K3 b - - 0 1"

theorem fenAfterSAN_enPassant_fixture :
    fenAfterSAN epFixtureFen epFixtureSan = .ok epFixtureExpectedFEN := by
  native_decide

def castleFixtureFen : String :=
  "4k3/8/8/8/8/8/8/R3K2R w KQ - 0 1"

def castleFixtureSan : String :=
  "O-O"

def castleFixtureExpectedFEN : String :=
  "4k3/8/8/8/8/8/8/R4RK1 b - - 1 1"

theorem fenAfterSAN_castle_fixture :
    fenAfterSAN castleFixtureFen castleFixtureSan = .ok castleFixtureExpectedFEN := by
  native_decide

def promoFixtureFen : String :=
  "k7/4P3/8/8/8/8/8/4K3 w - - 0 1"

def promoFixtureSan : String :=
  "e8=Q"

def promoFixtureExpectedFEN : String :=
  "k3Q3/8/8/8/8/8/8/4K3 b - - 0 1"

theorem fenAfterSAN_promotion_fixture :
    fenAfterSAN promoFixtureFen promoFixtureSan = .ok promoFixtureExpectedFEN := by
  native_decide

end Parsing
end Chess

