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

  /-- File coordinate is bounded by 8 (from Fin 8) -/
  theorem fileInt_lt_8 (s : Square) : s.fileInt < 8 := by
    show Int.ofNat s.file.toNat < 8
    exact Int.ofNat_lt.mpr s.file.isLt

  /-- Rank coordinate is bounded by 8 (from Fin 8) -/
  theorem rankInt_lt_8 (s : Square) : s.rankInt < 8 := by
    show Int.ofNat s.rank.toNat < 8
    exact Int.ofNat_lt.mpr s.rank.isLt

  /-- File coordinate is non-negative -/
  theorem fileInt_nonneg (s : Square) : 0 ≤ s.fileInt := by
    unfold fileInt
    exact Int.natCast_nonneg _

  /-- Rank coordinate is non-negative -/
  theorem rankInt_nonneg (s : Square) : 0 ≤ s.rankInt := by
    unfold rankInt
    exact Int.natCast_nonneg _

  /-- Convert square to array index (0-63) -/
  def toIndex (s : Square) : Fin 64 :=
    ⟨s.rank.val * 8 + s.file.val, by
      have hr := s.rank.isLt
      have hf := s.file.isLt
      omega⟩

  /-- Convert array index back to square -/
  def fromIndex (i : Fin 64) : Square :=
    { file := ⟨i.val % 8, Nat.mod_lt _ (by decide)⟩
      rank := ⟨i.val / 8, by omega⟩ }

  theorem fromIndex_toIndex (s : Square) : fromIndex (toIndex s) = s := by
    simp only [fromIndex, toIndex]
    have hf := s.file.isLt
    have hr := s.rank.isLt
    congr 1 <;> apply Fin.ext <;> simp <;> omega

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

  def fileChar (s : Square) : Char :=
    Char.ofNat ('a'.toNat + s.fileNat)

  def rankChar (s : Square) : Char :=
    Char.ofNat ('1'.toNat + s.rankNat)

  def fromAlgebraic? (coord : String) : Option Square :=
    match coord.toList with
    | f :: r :: [] =>
        let file := f.toNat - 'a'.toNat
        let rank := r.toNat - '1'.toNat
        if file < 8 ∧ rank < 8 then
          mk? file rank
        else
          none
    | _ => none

  def all : List Square :=
    (List.range 8).foldr
      (fun file acc =>
        (List.range 8).foldr
          (fun rank inner => Square.mkUnsafe file rank :: inner)
          acc)
      []

  /--
  Every valid square is in the `all` list.
  -/
  theorem mem_all (sq : Square) : sq ∈ all := by
    -- Square is finite (64 elements), so we can use native decidability
    -- We use the fact that Fin 8 is bounded and DecidableEq
    have : ∀ f : Fin 8, ∀ r : Fin 8, { file := f, rank := r : Square } ∈ all := by
      native_decide
    exact this sq.file sq.rank

end Square

def allSquares : List Square := Square.all

def whiteKingStart : Square := Square.mkUnsafe 4 0
def whiteQueenRookStart : Square := Square.mkUnsafe 0 0
def whiteKingRookStart : Square := Square.mkUnsafe 7 0
def blackKingStart : Square := Square.mkUnsafe 4 7
def blackQueenRookStart : Square := Square.mkUnsafe 0 7
def blackKingRookStart : Square := Square.mkUnsafe 7 7

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

/-- Array-based board representation for O(1) access -/
structure Board where
  data : Array (Option Piece)
  size_eq : data.size = 64 := by rfl

namespace Board

  /-- Create an empty board with all squares empty -/
  def empty : Board where
    data := (Array.range 64).map (fun _ => none)
    size_eq := by simp [Array.size_map, Array.size_range]

  private def indexValid (b : Board) (sq : Square) : sq.toIndex.val < b.data.size := by
    rw [b.size_eq]; exact sq.toIndex.isLt

  /-- Get the piece at a square -/
  def get (b : Board) (sq : Square) : Option Piece :=
    b.data[sq.toIndex.val]'(indexValid b sq)

  /-- Set the piece at a square -/
  def set (b : Board) (sq : Square) (p : Option Piece) : Board where
    data := b.data.setIfInBounds sq.toIndex.val p
    size_eq := by simp [Array.size_setIfInBounds, b.size_eq]

  /-- Update is an alias for set (for compatibility) -/
  def update (b : Board) (sq : Square) (p : Option Piece) : Board :=
    b.set sq p

  theorem get_set_eq (b : Board) (sq : Square) (p : Option Piece) :
      (b.set sq p).get sq = p := by
    unfold get set
    rw [Array.getElem_setIfInBounds_self]

  theorem get_set_ne (b : Board) (sq : Square) (p : Option Piece) {target : Square}
      (h : target ≠ sq) : (b.set sq p).get target = b.get target := by
    unfold get set
    have hne : sq.toIndex.val ≠ target.toIndex.val := by
      intro heq
      apply h
      have := congrArg Square.fromIndex (Fin.ext heq.symm)
      simp [Square.fromIndex_toIndex] at this
      exact this
    have hj : target.toIndex.val < b.data.size := indexValid b target
    rw [Array.getElem_setIfInBounds hj]
    simp [hne]

  -- Compatibility aliases
  theorem update_eq (b : Board) (sq : Square) (p : Option Piece) :
      (b.update sq p).get sq = p := get_set_eq b sq p

  theorem update_ne (b : Board) (sq : Square) (p : Option Piece) {target : Square}
      (h : target ≠ sq) : (b.update sq p).get target = b.get target := get_set_ne b sq p h

  /-- Build a board from a list of (square, piece) pairs -/
  def fromList (ps : List (Square × Piece)) : Board :=
    ps.foldl (fun b entry => b.update entry.fst (some entry.snd)) empty

  /-- Convert board to list of occupied squares -/
  def toList (b : Board) : List (Square × Piece) :=
    allSquares.filterMap fun sq =>
      match b.get sq with
      | some p => some (sq, p)
      | none => none

end Board

/-- Allow using board as a function: b sq -/
instance : CoeFun Board (fun _ => Square → Option Piece) where
  coe b sq := b.get sq

def emptyBoard : Board := Board.empty

instance : Inhabited Board := ⟨emptyBoard⟩

structure CastlingRights where
  whiteKingSide : Bool := true
  whiteQueenSide : Bool := true
  blackKingSide : Bool := true
  blackQueenSide : Bool := true
deriving Inhabited, DecidableEq

structure PositionSnapshot where
  pieces : List (Square × Piece)
  toMove : Color
  castlingRights : CastlingRights
  enPassantTarget : Option Square
deriving DecidableEq

structure GameState where
  board : Board := emptyBoard
  toMove : Color := Color.White
  halfMoveClock : Nat := 0
  fullMoveNumber : Nat := 1
  enPassantTarget : Option Square := none
  castlingRights : CastlingRights := {}
  history : List PositionSnapshot := []
  result : Option String := none
deriving Inhabited

structure Move where
  piece : Piece
  fromSq : Square
  toSq : Square
  isCapture : Bool := false
  promotion : Option PieceType := none
  isCastle : Bool := false
  castleRookFrom : Option Square := none
  castleRookTo : Option Square := none
  isEnPassant : Bool := false
deriving Repr, DecidableEq

def startingPieces : List (Square × Piece) :=
  let mk (f r : Nat) (pt : PieceType) (c : Color) : Square × Piece :=
    (Square.mkUnsafe f r, { pieceType := pt, color := c })
  let backRank (r : Nat) (c : Color) : List (Square × Piece) :=
    [ (0, PieceType.Rook), (1, PieceType.Knight), (2, PieceType.Bishop), (3, PieceType.Queen),
      (4, PieceType.King), (5, PieceType.Bishop), (6, PieceType.Knight), (7, PieceType.Rook) ]
      |>.map (fun (f, pt) => mk f r pt c)
  let pawns (r : Nat) (c : Color) : List (Square × Piece) :=
    (List.range 8).map (fun f => mk f r PieceType.Pawn c)
  backRank 0 Color.White ++ pawns 1 Color.White ++ backRank 7 Color.Black ++ pawns 6 Color.Black

def startingBoard : Board :=
  Board.fromList startingPieces

def standardGameState : GameState :=
  { board := startingBoard
    toMove := Color.White
    halfMoveClock := 0
    fullMoveNumber := 1
    enPassantTarget := none
    castlingRights := {}
    history := [] }

end Chess
