import Chess.Rules
import Chess.Movement
import Chess.Core

namespace Chess.Rules

/--
Helper: promotionMoves preserves isCapture.
-/
theorem promotionMoves_preserves_isCapture (m : Move) (m' : Move) :
    m' ∈ promotionMoves m → m'.isCapture = m.isCapture := by
  intro h_mem
  unfold promotionMoves at h_mem
  split at h_mem
  · -- Promotion case: m' is in the map
    simp only [List.mem_map] at h_mem
    obtain ⟨pt, _, h_eq⟩ := h_mem
    subst h_eq
    rfl
  · -- Non-promotion case: m' = m
    simp only [List.mem_singleton] at h_mem
    subst h_mem
    rfl

/--
Helper: moves from forwardMoves.foldr promotionMoves have isCapture = false.
-/
theorem pawnForwardMoves_not_capture (gs : GameState) (src : Square) (p : Piece) (m : Move) :
    let dir := Movement.pawnDirection p.color
    let oneStep := Movement.squareFromInts src.fileInt (src.rankInt + dir)
    let twoStep := Movement.squareFromInts src.fileInt (src.rankInt + 2 * dir)
    let forwardMoves : List Move :=
      match oneStep with
      | some target =>
          if isEmpty gs.board target then
            let base : List Move := [{ piece := p, fromSq := src, toSq := target }]
            let doubleStep : List Move :=
              if src.rankNat = pawnStartRank p.color then
                match twoStep with
                | some target2 =>
                    if isEmpty gs.board target2 then
                      [{ piece := p, fromSq := src, toSq := target2 }]
                    else
                      []
                | none => []
              else
                []
            base ++ doubleStep
          else
            []
      | none => []
    m ∈ forwardMoves.foldr (fun mv acc => promotionMoves mv ++ acc) [] →
    m.isCapture = false := by
  intro h_mem
  -- forwardMoves contains only moves with isCapture = false (default)
  simp only [List.foldr] at h_mem
  split at h_mem
  · simp at h_mem
  · next target =>
    split at h_mem
    · simp only [List.foldr_cons, List.mem_append] at h_mem
      cases h_mem with
      | inl h_prom =>
        -- m comes from promotionMoves of base move
        have h_pres := promotionMoves_preserves_isCapture _ _ h_prom
        rw [h_pres]
        rfl
      | inr h_rest =>
        -- m comes from doubleStep.foldr
        split at h_rest
        · split at h_rest
          · split at h_rest
            · simp only [List.foldr_cons, List.foldr_nil, List.mem_append] at h_rest
              cases h_rest with
              | inl h_prom =>
                have h_pres := promotionMoves_preserves_isCapture _ _ h_prom
                rw [h_pres]
                rfl
              | inr h_empty =>
                simp at h_empty
            · simp at h_rest
          · simp at h_rest
        · simp at h_rest
    · simp at h_mem

/--
Helper: moves from captureMoves have isCapture = true.
-/
theorem pawnCaptureMoves_is_capture (gs : GameState) (src : Square) (p : Piece) (m : Move) :
    let dir := Movement.pawnDirection p.color
    let captureOffsets : List Int := [-1, 1]
    let captureMoves :=
      captureOffsets.foldr
        (fun df acc =>
          match Movement.squareFromInts (src.fileInt + df) (src.rankInt + dir) with
          | some target =>
              if isEnemyAt gs.board p.color target then
                promotionMoves { piece := p, fromSq := src, toSq := target, isCapture := true } ++ acc
              else if gs.enPassantTarget = some target ∧ isEmpty gs.board target then
                { piece := p, fromSq := src, toSq := target, isCapture := true, isEnPassant := true } :: acc
              else
                acc
          | none => acc)
        []
    m ∈ captureMoves →
    m.isCapture = true := by
  intro h_mem
  simp only [List.foldr_cons, List.foldr_nil] at h_mem
  -- Handle first offset (-1)
  split at h_mem
  · -- None case for first offset, try second
    split at h_mem
    · simp at h_mem -- None case for second offset
    · next target2 =>
      split at h_mem
      · -- Enemy capture with promotion
        simp only [List.mem_append] at h_mem
        cases h_mem with
        | inl h_prom =>
          have h_pres := promotionMoves_preserves_isCapture _ _ h_prom
          rw [h_pres]
          rfl
        | inr h_rest => simp at h_rest
      · split at h_mem
        · simp only [List.mem_cons] at h_mem
          cases h_mem with
          | inl heq => subst heq; rfl
          | inr h_rest => simp at h_rest
        · simp at h_mem
  · next target1 =>
    split at h_mem
    · -- Enemy capture on first offset
      simp only [List.mem_append] at h_mem
      cases h_mem with
      | inl h_prom =>
        have h_pres := promotionMoves_preserves_isCapture _ _ h_prom
        rw [h_pres]
        rfl
      | inr h_rest =>
        -- Check second offset
        split at h_rest
        · simp at h_rest
        · next target2 =>
          split at h_rest
          · simp only [List.mem_append] at h_rest
            cases h_rest with
            | inl h_prom2 =>
              have h_pres := promotionMoves_preserves_isCapture _ _ h_prom2
              rw [h_pres]
              rfl
            | inr h_empty => simp at h_empty
          · split at h_rest
            · simp only [List.mem_cons] at h_rest
              cases h_rest with
              | inl heq => subst heq; rfl
              | inr h_empty => simp at h_empty
            · simp at h_rest
    · split at h_mem
      · -- En passant on first offset
        simp only [List.mem_cons] at h_mem
        cases h_mem with
        | inl heq => subst heq; rfl
        | inr h_rest =>
          -- Check second offset in rest
          split at h_rest
          · simp at h_rest
          · next target2 =>
            split at h_rest
            · simp only [List.mem_append] at h_rest
              cases h_rest with
              | inl h_prom2 =>
                have h_pres := promotionMoves_preserves_isCapture _ _ h_prom2
                rw [h_pres]
                rfl
              | inr h_empty => simp at h_empty
            · split at h_rest
              · simp only [List.mem_cons] at h_rest
                cases h_rest with
                | inl heq => subst heq; rfl
                | inr h_empty => simp at h_empty
              · simp at h_rest
      · -- Neither enemy nor en passant, check second offset
        split at h_mem
        · simp at h_mem
        · next target2 =>
          split at h_mem
          · simp only [List.mem_append] at h_mem
            cases h_mem with
            | inl h_prom =>
              have h_pres := promotionMoves_preserves_isCapture _ _ h_prom
              rw [h_pres]
              rfl
            | inr h_rest => simp at h_rest
          · split at h_mem
            · simp only [List.mem_cons] at h_mem
              cases h_mem with
              | inl heq => subst heq; rfl
              | inr h_rest => simp at h_rest
            · simp at h_mem

end Chess.Rules
