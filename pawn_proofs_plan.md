# Pawn Geometry Proofs Plan

## Context
We need to prove that pawn moves from `pieceTargets` satisfy `respectsGeometry`.

## Three Cases to Handle

### Case 1: En Passant (line 1749, 1750)
- **Given**: `m.isCapture = true`, `m.isEnPassant = true`, `m ∈ captureMoves`
- **Need to prove**:
  1. `Movement.isPawnCapture p.color sq m.toSq`
  2. `gs.enPassantTarget = some m.toSq`

**Approach**:
- En passant moves come from: `{... toSq := target, isCapture := true, isEnPassant := true }`
- Where `target` from `squareFromInts (sq.fileInt + df) (sq.rankInt + dir)` with `df ∈ {-1,1}`
- And condition: `gs.enPassantTarget = some target`
- Use `squareFromInts_pawn_capture` helper to show isPawnCapture
- Extract `gs.enPassantTarget = some target` from the foldr condition

### Case 2: Normal Capture (line 1760, 1761)
- **Given**: `m.isCapture = true`, `m.isEnPassant = false`, `m ∈ captureMoves`
- **Need to prove**:
  1. `Movement.isPawnCapture p.color sq m.toSq`
  2. `isEnemyAt gs.board p.color m.toSq`

**Approach**:
- Normal captures from: `{... toSq := target, isCapture := true }`
- Where `target` from `squareFromInts (sq.fileInt + df) (sq.rankInt + dir)` with `df ∈ {-1,1}`
- And condition: `isEnemyAt board color target`
- Use `squareFromInts_pawn_capture` helper
- Extract `isEnemyAt` from foldr condition

### Case 3: Advance (line 1768, 1769)
- **Given**: `m.isCapture = false`, `m ∈ forwardMoves`
- **Need to prove**:
  1. `Movement.isPawnAdvance p.color sq m.toSq`
  2. `pathClear gs.board sq m.toSq`

**Approach**:
- Forward moves from oneStep or twoStep
- oneStep: `squareFromInts sq.fileInt (sq.rankInt + dir)`
- twoStep: `squareFromInts sq.fileInt (sq.rankInt + 2 * dir)`
- Use `squareFromInts_pawn_advance_one` or `squareFromInts_pawn_advance_two`
- For pathClear: analyze isEmpty conditions in forwardMoves

## Additional Helper Lemmas Needed

1. Lemma to extract from captureMoves foldr that en passant moves have `gs.enPassantTarget = some m.toSq`
2. Lemma to extract from captureMoves foldr that normal captures have `isEnemyAt`
3. Lemma to extract from forwardMoves that pathClear holds
4. Lemma that forward moves have `isCapture = false`
5. Lemma that capture moves have `isCapture = true`
