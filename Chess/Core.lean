import Init.Data.List
import Init.Data.Char

namespace Chess

abbrev File := Fin 8
abbrev Rank := Fin 8

def File.toNat (f : File) : Nat := f.val
def Rank.toNat (r : Rank) : Nat := r.val

structure Square where
  file : File
  rank : Rank
deriving DecidableEq, Repr, Inhabited

namespace Square

  def fileNat (s : Square) : Nat := s.file.toNat
  def rankNat (s : Square) : Nat := s.rank.toNat
  def sumNat (s : Square) : Nat := s.file.toNat + s.rank.toNat

  def fileInt (s : Square) : Int := Int.ofNat s.file.toNat
  def rankInt (s : Square) : Int := Int.ofNat s.rank.toNat

  def algebraic (s : Square) : String :=
    let fileChar := Char.ofNat ('a'.toNat + s.fileNat)
    fileChar.toString ++ toString (s.rankNat + 1)

  def mk? (file rank : Nat) : Option Square :=
    if hf : file < 8 then
      if hr : rank < 8 then
        some { file := ⟨file, hf⟩, rank := ⟨rank, hr⟩ }
      else
        none
    else
      none

  def mkUnsafe (file rank : Nat) : Square :=
    match mk? file rank with
    | some sq => sq
    | none => panic! "Square.mkUnsafe: index out of range"

  def all : List Square :=
    (List.range 8).foldr
      (fun file acc =>
        (List.range 8).foldr
          (fun rank inner => Square.mkUnsafe file rank :: inner)
          acc)
      []

end Square

def allSquares : List Square := Square.all

inductive Color where
  | White
  | Black
deriving DecidableEq, Repr, Inhabited

namespace Color

  def opposite : Color → Color
    | White => Black
    | Black => White

  theorem opposite_opposite (c : Color) : opposite (opposite c) = c := by
    cases c <;> rfl

end Color

inductive PieceType where
  | King
  | Queen
  | Rook
  | Bishop
  | Knight
  | Pawn
deriving DecidableEq, Repr

structure Piece where
  pieceType : PieceType
  color : Color
deriving Repr, DecidableEq

namespace Piece

  instance : Inhabited Piece :=
    ⟨{ pieceType := PieceType.King, color := Color.White }⟩

end Piece

abbrev Board := Square → Option Piece

def emptyBoard : Board := fun _ => none

namespace Board

  def update (b : Board) (sq : Square) (p : Option Piece) : Board :=
    fun target => if target = sq then p else b target

  theorem update_eq (b : Board) (sq : Square) (p : Option Piece) :
      (b.update sq p) sq = p := by
    simp [update]

  theorem update_ne (b : Board) (sq : Square) (p : Option Piece) {target : Square}
      (h : target ≠ sq) : (b.update sq p) target = b target := by
    simp [update, h]

end Board

instance : Inhabited Board := ⟨emptyBoard⟩

structure GameState where
  board : Board := emptyBoard
  toMove : Color := Color.White
  halfMoveClock : Nat := 0
  fullMoveNumber : Nat := 1
deriving Inhabited

structure Move where
  piece : Piece
  fromSq : Square
  toSq : Square
  isCapture : Bool := false
  promotion : Option PieceType := none
deriving Repr

end Chess
