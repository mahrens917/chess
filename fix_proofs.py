#!/usr/bin/env python3

import re

# Read the file
with open('/Users/mahrens917/chess/Chess/LegalMovesProofs.lean', 'r') as f:
    content = f.read()

# Replacement 1: slidingTargets_rook_geometry
rook_sorry = """  intro h_mem
  have h_props := slidingTargets_spec gs src p deltas m h_mem
  -- The move has fromSq = src, so we need to show isRookMove src m.toSq
  rw [h_props.2]
  -- The deltas are (±1, 0) or (0, ±1) which generate rook moves
  -- This requires tracing through the walk function
  sorry"""

rook_proof = """  intro h_mem
  have h_props := slidingTargets_spec gs src p deltas m h_mem
  rw [h_props.2]
  constructor
  · -- Show isRookMove
    unfold Movement.isRookMove Movement.fileDiff Movement.rankDiff
    unfold slidingTargets at h_mem
    subst h_deltas
    simp only [List.foldr_cons, List.foldr_nil] at h_mem
    by_cases h1 : m ∈ slidingTargets.walk gs.board p.color 7 1 0 7 []
    · have h_geom := slidingTargets_walk_geometry gs src p 1 0 7 [] m h1 (by simp)
      obtain ⟨offset, h_pos, _, h_file, h_rank⟩ := h_geom
      constructor
      · intro h_eq; simp only [← h_eq] at h_file h_rank
        have : src.fileInt + 1 * offset = src.fileInt := by rw [← h_file, Square.fileInt, h_eq]
        omega
      · right; constructor; · simp [h_rank]; · simp [h_file]; omega
    · by_cases h2 : m ∈ slidingTargets.walk gs.board p.color 7 (-1) 0 7
          (slidingTargets.walk gs.board p.color 7 1 0 7 [])
      · have h_geom := slidingTargets_walk_geometry gs src p (-1) 0 7 _ m h2 h1
        obtain ⟨offset, h_pos, _, h_file, h_rank⟩ := h_geom
        constructor
        · intro h_eq; simp only [← h_eq] at h_file h_rank
          have : src.fileInt + (-1) * offset = src.fileInt := by rw [← h_file, Square.fileInt, h_eq]
          omega
        · right; constructor; · simp [h_rank]; · simp [h_file]; omega
      · by_cases h3 : m ∈ slidingTargets.walk gs.board p.color 7 0 1 7
            (slidingTargets.walk gs.board p.color 7 (-1) 0 7
              (slidingTargets.walk gs.board p.color 7 1 0 7 []))
        · have h_geom := slidingTargets_walk_geometry gs src p 0 1 7 _ m h3 h2
          obtain ⟨offset, h_pos, _, h_file, h_rank⟩ := h_geom
          constructor
          · intro h_eq; simp only [← h_eq] at h_file h_rank
            have : src.rankInt + 1 * offset = src.rankInt := by rw [← h_rank, Square.rankInt, h_eq]
            omega
          · left; constructor; · simp [h_file]; · simp [h_rank]; omega
        · have h_geom := slidingTargets_walk_geometry gs src p 0 (-1) 7 _ m h_mem h3
          obtain ⟨offset, h_pos, _, h_file, h_rank⟩ := h_geom
          constructor
          · intro h_eq; simp only [← h_eq] at h_file h_rank
            have : src.rankInt + (-1) * offset = src.rankInt := by rw [← h_rank, Square.rankInt, h_eq]
            omega
          · left; constructor; · simp [h_file]; · simp [h_rank]; omega
  · -- pathClear: walk ensures all intermediate squares are empty (admitted)
    sorry"""

content = content.replace(rook_sorry, rook_proof)

# Replacement 2: slidingTargets_bishop_geometry
bishop_sorry = """  intro h_mem
  have h_props := slidingTargets_spec gs src p deltas m h_mem
  rw [h_props.2]
  sorry"""

bishop_proof = """  intro h_mem
  have h_props := slidingTargets_spec gs src p deltas m h_mem
  rw [h_props.2]
  constructor
  · -- Show isDiagonal
    unfold Movement.isDiagonal Movement.fileDiff Movement.rankDiff Movement.absInt
    unfold slidingTargets at h_mem
    subst h_deltas
    simp only [List.foldr_cons, List.foldr_nil] at h_mem
    by_cases h1 : m ∈ slidingTargets.walk gs.board p.color 7 1 1 7 []
    · have h_geom := slidingTargets_walk_geometry gs src p 1 1 7 [] m h1 (by simp)
      obtain ⟨offset, h_pos, _, h_file, h_rank⟩ := h_geom
      constructor
      · intro h_eq; simp only [← h_eq] at h_file h_rank
        have : src.fileInt + 1 * offset = src.fileInt := by rw [← h_file, Square.fileInt, h_eq]
        omega
      · simp [h_file, h_rank]; omega
    · by_cases h2 : m ∈ slidingTargets.walk gs.board p.color 7 (-1) (-1) 7
          (slidingTargets.walk gs.board p.color 7 1 1 7 [])
      · have h_geom := slidingTargets_walk_geometry gs src p (-1) (-1) 7 _ m h2 h1
        obtain ⟨offset, h_pos, _, h_file, h_rank⟩ := h_geom
        constructor
        · intro h_eq; simp only [← h_eq] at h_file h_rank
          have : src.fileInt + (-1) * offset = src.fileInt := by rw [← h_file, Square.fileInt, h_eq]
          omega
        · simp [h_file, h_rank]; omega
      · by_cases h3 : m ∈ slidingTargets.walk gs.board p.color 7 1 (-1) 7
            (slidingTargets.walk gs.board p.color 7 (-1) (-1) 7
              (slidingTargets.walk gs.board p.color 7 1 1 7 []))
        · have h_geom := slidingTargets_walk_geometry gs src p 1 (-1) 7 _ m h3 h2
          obtain ⟨offset, h_pos, _, h_file, h_rank⟩ := h_geom
          constructor
          · intro h_eq; simp only [← h_eq] at h_file h_rank
            have : src.fileInt + 1 * offset = src.fileInt := by rw [← h_file, Square.fileInt, h_eq]
            omega
          · simp [h_file, h_rank]; omega
        · have h_geom := slidingTargets_walk_geometry gs src p (-1) 1 7 _ m h_mem h3
          obtain ⟨offset, h_pos, _, h_file, h_rank⟩ := h_geom
          constructor
          · intro h_eq; simp only [← h_eq] at h_file h_rank
            have : src.fileInt + (-1) * offset = src.fileInt := by rw [← h_file, Square.fileInt, h_eq]
            omega
          · simp [h_file, h_rank]; omega
  · -- pathClear: walk ensures all intermediate squares are empty (admitted)
    sorry"""

# Find and replace bishop proof - need to be more specific
# Let's find the exact location
bishop_start = content.find("theorem slidingTargets_bishop_geometry")
if bishop_start != -1:
    # Find the sorry after this
    sorry_start = content.find(bishop_sorry, bishop_start)
    if sorry_start != -1:
        content = content[:sorry_start] + bishop_proof + content[sorry_start + len(bishop_sorry):]

# Replacement 3: slidingTargets_queen_geometry - admit with reference to previous proofs
queen_sorry_pattern = re.compile(
    r'(theorem slidingTargets_queen_geometry.*?m ∈ slidingTargets.*?\n\s+intro h_mem\n\s+have h_props.*?\n\s+rw \[h_props\.2\]\n)\s+sorry',
    re.DOTALL
)

queen_proof_replacement = r'\1  constructor\n  · -- Show isQueenMove = isRookMove ∨ isDiagonal\n    unfold Movement.isQueenMove\n    -- Queen moves are either rook moves or diagonal moves\n    -- This follows from queen deltas being union of rook and bishop deltas\n    sorry\n  · -- pathClear: walk ensures all intermediate squares are empty (admitted)\n    sorry'

content = queen_sorry_pattern.sub(queen_proof_replacement, content)

# Write back
with open('/Users/mahrens917/chess/Chess/LegalMovesProofs.lean', 'w') as f:
    f.write(content)

print("Proofs updated successfully")
