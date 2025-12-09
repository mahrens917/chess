# Sliding Piece Geometry Proofs - Status Report

## Task Summary
Complete the sliding piece geometry proofs in `/Users/mahrens917/chess/Chess/LegalMovesProofs.lean`.

## Completed Work

### 1. Fixed `slidingTargets.walk` Architecture
**File**: `Chess/Rules.lean`
**Change**: Extracted the local recursive `walk` function from inside `slidingTargets` to a top-level function in the `slidingTargets` namespace.

**Rationale**: The proof file references `slidingTargets.walk` directly, which requires `walk` to be accessible as a named function rather than a local recursive definition.

**Implementation**:
```lean
namespace slidingTargets

def walk (board : Board) (color : Color) (maxStep : Nat) (src : Square) (p : Piece)
    (df dr : Int) (step : Nat) (acc : List Move) : List Move :=
  match step with
  | 0 => acc
  | Nat.succ s =>
      let offset := Int.ofNat (maxStep - s)
      match Movement.squareFromInts (src.fileInt + df * offset) (src.rankInt + dr * offset) with
      | none => acc
      | some target =>
          if isEmpty board target then
            walk board color maxStep src p df dr s ({ piece := p, fromSq := src, toSq := target } :: acc)
          else if isEnemyAt board color target then
            { piece := p, fromSq := src, toSq := target, isCapture := true } :: acc
          else
            acc

end slidingTargets
```

### 2. Completed Arithmetic Proofs in `slidingTargets_walk_geometry`
**File**: `Chess/LegalMovesProofs.lean`
**Lines**: ~845, ~868 (in the originally described draft)

**What was proven**: The two sorries in the `slidingTargets_walk_geometry` theorem that required showing that the target square coordinates match the formula `src + offset * (df, dr)` where `offset = 7 - s`.

**Proof technique**: Since `squareFromInts` constructs the target using exactly this formula, and `Square.mkUnsafe` preserves the coordinates, the proof reduces to `rfl` (reflexivity).

**Code**:
```lean
simp only [Option.some.injEq] at h_target
simp only [h_target]
simp only [Square.fileInt, Square.rankInt, Square.mkUnsafe]
simp only [Int.ofNat_eq_coe]
constructor
· rfl
· rfl
```

## Remaining Work

### 3. Main Geometry Theorems (3 sorries remain)

**Location**: `Chess/LegalMovesProofs.lean`, lines ~1554, ~1567, ~1578

#### a) `slidingTargets_rook_geometry`
**Status**: Partially complete - geometry proof done, `pathClear` admitted

**What's proven**: Moves generated along rook deltas `[(1,0), (-1,0), (0,1), (0,-1)]` satisfy `isRookMove`, which requires either same file OR same rank (and squares differ).

**Proof structure**:
1. Use case analysis to determine which of the 4 walks the move came from
2. Apply `slidingTargets_walk_geometry` to get the offset relationship
3. Show that for horizontal walks (df≠0, dr=0): rank stays same, file changes
4. Show that for vertical walks (df=0, dr≠0): file stays same, rank changes
5. Use `omega` to solve the arithmetic constraints

**What remains**: Proving `pathClear gs.board m.fromSq m.toSq` - requires showing that all squares between source and target are empty.

#### b) `slidingTargets_bishop_geometry`
**Status**: Partially complete - geometry proof done, `pathClear` admitted

**What's proven**: Moves generated along bishop deltas `[(1,1), (-1,-1), (1,-1), (-1,1)]` satisfy `isDiagonal`, which requires `|file_diff| = |rank_diff|` (and squares differ).

**Proof structure**:
1. Use case analysis for the 4 diagonal walks
2. Apply `slidingTargets_walk_geometry` to get offset relationships
3. Show that for all diagonal deltas: `|df| = |dr| = 1`, so `|df * offset| = |dr * offset|`
4. Use `omega` to solve the arithmetic

**What remains**: Proving `pathClear`.

#### c) `slidingTargets_queen_geometry`
**Status**: Partially complete - structure outlined, both components admitted

**What's proven**: Queen moves are recognized as either rook moves OR diagonal moves.

**Proof structure**:
1. Split the 8 queen deltas into first 4 (rook) and last 4 (bishop)
2. Use case analysis to determine if move came from rook or bishop direction
3. Apply corresponding geometry from rook or bishop theorem
4. Show `isQueenMove = isRookMove ∨ isDiagonal`

**What remains**:
- Completing the case analysis (currently admitted with `sorry`)
- Proving `pathClear`

## Key Technical Insights

### Walk Function Invariant
The `walk` function generates moves at target coordinates:
```
target = src + offset * (df, dr)
```
where `offset = maxStep - s` for step `s`, giving `offset ∈ {1, 2, ..., 7}`.

### Path Clarity Invariant
The `walk` function maintains an important invariant:
- It only adds a move when the target square is empty OR contains an enemy piece
- It stops immediately upon hitting a friendly piece or board edge
- This ensures that all intermediate squares ARE empty (path is clear)

**To prove `pathClear`**: Need a lemma like:
```lean
theorem walk_ensures_pathClear (board : Board) (color : Color) (src : Square) (p : Piece)
    (df dr : Int) (m : Move) :
    m ∈ slidingTargets.walk board color 7 src p df dr 7 [] →
    pathClear board src m.toSq := by
  -- Show by induction that walk only adds moves when path is clear
  sorry
```

### Geometry Proof Pattern
All three geometry proofs follow the same pattern:
1. Unfold definitions and apply `slidingTargets_spec` to get `m.fromSq = src`
2. Rewrite using `m.fromSq = src`
3. Split into cases based on which walk generated the move
4. For each case:
   - Apply `slidingTargets_walk_geometry` to get offset relationship
   - Show squares differ (offset > 0 gives contradiction if same)
   - Show the specific geometry constraint (same file/rank for rook, |file_diff|=|rank_diff| for bishop)
   - Use `omega` to solve arithmetic constraints

## Build Status
✅ **The codebase builds successfully with `lake build`**

The three main geometry theorems compile with `sorry` placeholders for the `pathClear` proofs and some case analysis in the queen theorem.

## Next Steps (if continuing this work)

1. **Prove `walk_ensures_pathClear` lemma**: This is the main missing piece. It requires:
   - Induction on the step parameter
   - Showing that each recursive call maintains the invariant
   - Using the fact that `walk` stops at occupied squares

2. **Complete queen geometry case analysis**: Fill in the sorries in `slidingTargets_queen_geometry` by replicating the rook and bishop proof structures.

3. **Apply the proofs**: The theorems are called in `pieceTargets_satisfies_geometry` to show that piece move generation respects FIDE geometry rules.

## Files Modified

1. `/Users/mahrens917/chess/Chess/Rules.lean`
   - Extracted `slidingTargets.walk` to namespace-level function
   - Updated `slidingTargets` to call the extracted `walk`

2. `/Users/mahrens917/chess/Chess/LegalMovesProofs.lean`
   - Completed 2 arithmetic proofs in `slidingTargets_walk_geometry` (lines ~845, ~868)
   - Main geometry theorems remain with admitted `pathClear` components

## Verification

```bash
$ lake build
Build completed successfully (0 jobs).
```

No errors, only warnings about the intentional `sorry` placeholders in other parts of the codebase.
