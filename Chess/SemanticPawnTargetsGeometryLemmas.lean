import Init.Omega
import Chess.Spec
import Chess.ParsingProofs
import Chess.SemanticSlidingGeometryLemmas
import Chess.SemanticPawnLemmas

namespace Chess
namespace Rules

open Movement

theorem squaresBetween_pawn_oneStep
    (c : Color) (src tgt : Square)
    (hSq :
      Movement.squareFromInts src.fileInt (src.rankInt + Movement.pawnDirection c) = some tgt) :
    Movement.squaresBetween src tgt = [] := by
  have hFile :
      tgt.fileInt = src.fileInt :=
    Movement.squareFromInts_fileInt src.fileInt (src.rankInt + Movement.pawnDirection c) tgt hSq
  have hRank :
      tgt.rankInt = src.rankInt + Movement.pawnDirection c :=
    Movement.squareFromInts_rankInt src.fileInt (src.rankInt + Movement.pawnDirection c) tgt hSq
  have hRook : Movement.isRookMove src tgt := by
    apply isRookMove_of_file_eq (src := src) (tgt := tgt) hFile
    intro hEq
    have hDirNe : Movement.pawnDirection c ≠ 0 := pawnDirection_ne_zero c
    have : src.rankInt + Movement.pawnDirection c = src.rankInt := by
      -- `hEq : tgt.rankInt = src.rankInt` and `hRank : tgt.rankInt = src.rankInt + dir`.
      have : src.rankInt = src.rankInt + Movement.pawnDirection c := by
        simpa [hRank] using hEq.symm
      simpa using this.symm
    have : Movement.pawnDirection c = 0 := by
      have : src.rankInt + Movement.pawnDirection c = src.rankInt + 0 := by simpa using this
      exact Int.add_left_cancel this
    exact hDirNe this
  have hNotDiag : ¬ Movement.isDiagonal src tgt := by
    intro hDiag
    have hfd : Movement.fileDiff src tgt = 0 := by
      unfold Movement.fileDiff
      simp [hFile]
    have hrd : Movement.rankDiff src tgt = -Movement.pawnDirection c := by
      unfold Movement.rankDiff
      simp [hRank]
      omega
    have hAbs0 : Movement.absInt (Movement.fileDiff src tgt) = 0 := by
      simp [hfd, Movement.absInt]
    have hAbs1 : Movement.absInt (Movement.rankDiff src tgt) = 1 := by
      cases c <;> simp [hrd, Movement.pawnDirection, Movement.absInt]
    have : (0 : Int) = 1 := by
      simpa [hAbs0, hAbs1] using hDiag.2
    have hNe : (0 : Int) ≠ 1 := by decide
    exact (hNe this).elim
  unfold Movement.squaresBetween
  simp [hNotDiag, hRook]
  have hfd : Movement.fileDiff src tgt = 0 := by
    unfold Movement.fileDiff
    simp [hFile]
  have hrd : Movement.rankDiff src tgt = -Movement.pawnDirection c := by
    unfold Movement.rankDiff
    simp [hRank]
    omega
  -- Reduce the rook steps count to `1`.
  cases c <;>
    simp [hfd, hrd, Movement.pawnDirection]

theorem squaresBetween_pawn_twoStep
    (c : Color) (src tgt mid : Square)
    (hTgt :
      Movement.squareFromInts src.fileInt (src.rankInt + 2 * Movement.pawnDirection c) = some tgt)
    (hMid :
      Movement.squareFromInts src.fileInt (src.rankInt + Movement.pawnDirection c) = some mid) :
    Movement.squaresBetween src tgt = [mid] := by
  have hTgtFile :
      tgt.fileInt = src.fileInt :=
    Movement.squareFromInts_fileInt src.fileInt (src.rankInt + 2 * Movement.pawnDirection c) tgt hTgt
  have hTgtRank :
      tgt.rankInt = src.rankInt + 2 * Movement.pawnDirection c :=
    Movement.squareFromInts_rankInt src.fileInt (src.rankInt + 2 * Movement.pawnDirection c) tgt hTgt
  have hMidFile :
      mid.fileInt = src.fileInt :=
    Movement.squareFromInts_fileInt src.fileInt (src.rankInt + Movement.pawnDirection c) mid hMid
  have hMidRank :
      mid.rankInt = src.rankInt + Movement.pawnDirection c :=
    Movement.squareFromInts_rankInt src.fileInt (src.rankInt + Movement.pawnDirection c) mid hMid
  have hRook : Movement.isRookMove src tgt := by
    apply isRookMove_of_file_eq (src := src) (tgt := tgt) hTgtFile
    intro hEq
    have hDirNe : Movement.pawnDirection c ≠ 0 := pawnDirection_ne_zero c
    have : src.rankInt + 2 * Movement.pawnDirection c = src.rankInt := by
      have : src.rankInt = src.rankInt + 2 * Movement.pawnDirection c := by
        simpa [hTgtRank] using hEq.symm
      simpa using this.symm
    have : 2 * Movement.pawnDirection c = 0 := by
      have : src.rankInt + 2 * Movement.pawnDirection c = src.rankInt + 0 := by simpa using this
      exact Int.add_left_cancel this
    have : Movement.pawnDirection c = 0 := by
      omega
    exact hDirNe this
  have hNotDiag : ¬ Movement.isDiagonal src tgt := by
    intro hDiag
    have hfd : Movement.fileDiff src tgt = 0 := by
      unfold Movement.fileDiff
      simp [hTgtFile]
    have hrd : Movement.rankDiff src tgt = -2 * Movement.pawnDirection c := by
      unfold Movement.rankDiff
      simp [hTgtRank]
      omega
    have hAbs0 : Movement.absInt (Movement.fileDiff src tgt) = 0 := by
      simp [hfd, Movement.absInt]
    have hAbs2 : Movement.absInt (Movement.rankDiff src tgt) = 2 := by
      cases c <;> simp [hrd, Movement.pawnDirection, Movement.absInt]
    have : (0 : Int) = 2 := by
      simpa [hAbs0, hAbs2] using hDiag.2
    have hNe : (0 : Int) ≠ 2 := by decide
    exact (hNe this).elim
  unfold Movement.squaresBetween
  simp [hNotDiag, hRook]
  have hfd : Movement.fileDiff src tgt = 0 := by
    unfold Movement.fileDiff
    simp [hTgtFile]
  have hrd : Movement.rankDiff src tgt = -2 * Movement.pawnDirection c := by
    unfold Movement.rankDiff
    simp [hTgtRank]
    omega
  cases c with
  | White =>
      have hMid' : Movement.squareFromInts src.fileInt (src.rankInt + 1) = some mid := by
        simpa [Movement.pawnDirection] using hMid
      simp [hfd, hrd, Movement.pawnDirection, Movement.signInt, List.filterMap, hMid']
  | Black =>
      have hMid' : Movement.squareFromInts src.fileInt (src.rankInt + (-1)) = some mid := by
        simpa [Movement.pawnDirection] using hMid
      simp [hfd, hrd, Movement.pawnDirection, Movement.signInt, List.filterMap, hMid']

theorem pawn_capture_semantics_of_mem_pieceTargets
    (gs : GameState) (src : Square) (p : Piece) (m : Move)
    (hPawn : p.pieceType = PieceType.Pawn)
    (hTargets : m ∈ pieceTargets gs src p)
    (hCap : m.isCapture = true) :
    Movement.isPawnCapture p.color src m.toSq ∧
      ((m.isEnPassant = true ∧
          gs.enPassantTarget = some m.toSq ∧
          Rules.isEmpty gs.board m.toSq = true ∧
          Rules.enPassantFromHistory gs m.toSq = true) ∨
        (m.isEnPassant = false ∧ Rules.isEnemyNonKingAt gs.board p.color m.toSq = true)) := by
  let board := gs.board
  let color := p.color
  let dir := Movement.pawnDirection color
  let oneStep := Movement.squareFromInts src.fileInt (src.rankInt + dir)
  let twoStep := Movement.squareFromInts src.fileInt (src.rankInt + 2 * dir)
  let forwardMoves : List Move :=
    match oneStep with
    | some target =>
        if Rules.isEmpty board target then
          let base : List Move := [{ piece := p, fromSq := src, toSq := target }]
          let doubleStep : List Move :=
            if src.rankNat = Rules.pawnStartRank color then
              match twoStep with
              | some target2 =>
                  if Rules.isEmpty board target2 then
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
  let stepFn : Int → List Move → List Move :=
    fun df acc =>
      match Movement.squareFromInts (src.fileInt + df) (src.rankInt + dir) with
      | some target =>
          if Rules.isEnemyNonKingAt board color target then
            Rules.promotionMoves { piece := p, fromSq := src, toSq := target, isCapture := true } ++ acc
          else if gs.enPassantTarget = some target ∧ Rules.isEmpty board target ∧ Rules.enPassantFromHistory gs target = true then
            { piece := p, fromSq := src, toSq := target, isCapture := true, isEnPassant := true } :: acc
          else
            acc
      | none => acc
  let captureMoves : List Move := ([-1, 1] : List Int).foldr stepFn []
  have hMem' :
      m ∈ forwardMoves.foldr (fun mv acc => Rules.promotionMoves mv ++ acc) [] ++ captureMoves := by
    simpa [Rules.pieceTargets, hPawn, board, color, dir, oneStep, twoStep, forwardMoves, stepFn, captureMoves] using
      hTargets
  have hForwardNoCap :
      m ∈ forwardMoves.foldr (fun mv acc => Rules.promotionMoves mv ++ acc) [] → False := by
    intro hForward
    rcases (Chess.Parsing.List.mem_foldr_append_iff (f := Rules.promotionMoves) (b := m) forwardMoves).1 hForward with
      ⟨base, hBaseMem, hInProm⟩
    have hBaseCap : base.isCapture = false := by
      -- Forward bases are constructed without `isCapture := true`.
      dsimp [forwardMoves] at hBaseMem
      cases hOne : oneStep with
      | none =>
          cases (show False by simpa [hOne] using hBaseMem)
      | some target =>
          cases hEmpty : Rules.isEmpty board target with
          | false =>
              cases (show False by simpa [hOne, hEmpty] using hBaseMem)
          | true =>
              have hMem'' :
                  base ∈ [{ piece := p, fromSq := src, toSq := target }] ++
                    (if src.rankNat = Rules.pawnStartRank color then
                        match twoStep with
                        | some target2 =>
                            if Rules.isEmpty board target2 then
                              [{ piece := p, fromSq := src, toSq := target2 }]
                            else
                              []
                        | none => []
                      else
                        []) := by
                simpa [hOne, hEmpty] using hBaseMem
              cases List.mem_append.1 hMem'' with
              | inl hIn =>
                  have hEq : base = { piece := p, fromSq := src, toSq := target } := by
                    simpa using hIn
                  simp [hEq]
              | inr hIn =>
                  by_cases hStart : src.rankNat = Rules.pawnStartRank color
                  · cases hTwo : twoStep with
                    | none =>
                        cases (show False by simpa [hStart, hTwo] using hIn)
                    | some target2 =>
                        cases hEmpty2 : Rules.isEmpty board target2 with
                        | false =>
                            cases (show False by simpa [hStart, hTwo, hEmpty2] using hIn)
                        | true =>
                            have hEq : base = { piece := p, fromSq := src, toSq := target2 } := by
                              simpa [hStart, hTwo, hEmpty2] using hIn
                            simp [hEq]
                  · cases (show False by simpa [hStart] using hIn)
    have hCapEq : m.isCapture = base.isCapture := Chess.Parsing.promotionMoves_mem_isCapture_eq m base hInProm
    have : m.isCapture = false := by simp [hCapEq, hBaseCap]
    cases (show False by simpa [hCap] using this)
  have hCapMem : m ∈ captureMoves := by
    cases List.mem_append.1 hMem' with
    | inl hForward => exact (hForwardNoCap hForward).elim
    | inr hCapture => exact hCapture
  -- Unroll `captureMoves` as `stepFn (-1) (stepFn 1 [])`.
  have hCapMem' : m ∈ stepFn (-1) (stepFn 1 []) := by
    simpa [captureMoves, List.foldr] using hCapMem
  -- Analyze `df = -1` branch first.
  dsimp [stepFn] at hCapMem'
  cases hSqNeg : Movement.squareFromInts (src.fileInt + (-1)) (src.rankInt + dir) with
  | none =>
      -- Must have come from the accumulator `stepFn 1 []`.
      have hAcc :
          m ∈
            match Movement.squareFromInts (src.fileInt + 1) (src.rankInt + dir) with
            | some target =>
                if Rules.isEnemyNonKingAt board color target = true then
                  Rules.promotionMoves { piece := p, fromSq := src, toSq := target, isCapture := true }
                else if gs.enPassantTarget = some target ∧ Rules.isEmpty board target ∧ Rules.enPassantFromHistory gs target = true then
                  [{ piece := p, fromSq := src, toSq := target, isCapture := true, isEnPassant := true }]
                else []
            | none => [] := by
        simpa [hSqNeg, stepFn] using hCapMem'
      -- Analyze `df = 1` branch.
      cases hSqPos : Movement.squareFromInts (src.fileInt + 1) (src.rankInt + dir) with
      | none =>
          cases (show False by simpa [hSqPos] using hAcc)
      | some target =>
          cases hEnemy : Rules.isEnemyNonKingAt board color target with
          | true =>
              have hIn :
                  m ∈ Rules.promotionMoves { piece := p, fromSq := src, toSq := target, isCapture := true } := by
                simpa [hSqPos, hEnemy] using hAcc
              have hTo : m.toSq = target := Chess.Parsing.promotionMoves_mem_toSq_eq m _ hIn
              have hSq :
                  Movement.squareFromInts (src.fileInt + 1) (src.rankInt + dir) = some m.toSq := by
                simpa [hTo] using hSqPos
              have hPC :
                  Movement.isPawnCapture color src m.toSq :=
                isPawnCapture_of_step color src m.toSq 1 (Or.inr rfl) hSq
              refine ⟨hPC, ?_⟩
              right
              refine ⟨?_, ?_⟩
              · -- Enemy captures are never en passant.
                have hPres := promotionMoves_mem_preserves_squares m
                  { piece := p, fromSq := src, toSq := target, isCapture := true } hIn
                simpa [hPres.2.2.2.2] using rfl
              · simp [board, color, hTo, hEnemy]
          | false =>
              by_cases hEP : gs.enPassantTarget = some target ∧ Rules.isEmpty board target ∧ Rules.enPassantFromHistory gs target = true
              · have hEqOr : m = { piece := p, fromSq := src, toSq := target, isCapture := true, isEnPassant := true } := by
                  simpa [hSqPos, hEnemy, hEP] using hAcc
                subst hEqOr
                have hSq :
                    Movement.squareFromInts (src.fileInt + 1) (src.rankInt + dir) = some target := hSqPos
                have hPC :
                    Movement.isPawnCapture color src target :=
                  isPawnCapture_of_step color src target 1 (Or.inr rfl) hSq
                refine ⟨hPC, ?_⟩
                left
                refine ⟨rfl, hEP.1, hEP.2.1, hEP.2.2⟩
              ·
                cases (show False by
                  -- `stepFn` returns the accumulator when neither branch applies.
                  simpa [hSqPos, hEnemy, hEP] using hAcc)
  | some target =>
      cases hEnemy : Rules.isEnemyNonKingAt board color target with
      | true =>
          have hSplit :
              m ∈ Rules.promotionMoves { piece := p, fromSq := src, toSq := target, isCapture := true } ∨
                m ∈
                  match Movement.squareFromInts (src.fileInt + 1) (src.rankInt + dir) with
                  | some target =>
                      if Rules.isEnemyNonKingAt board color target = true then
                        Rules.promotionMoves
                            { piece := p, fromSq := src, toSq := target, isCapture := true }
                      else if gs.enPassantTarget = some target ∧ Rules.isEmpty board target ∧ Rules.enPassantFromHistory gs target = true then
                        [{ piece := p, fromSq := src, toSq := target, isCapture := true, isEnPassant := true }]
                      else []
                  | none => [] := by
            simpa [hSqNeg, hEnemy, List.mem_append, stepFn] using hCapMem'
          cases hSplit with
          | inl hIn =>
              have hTo : m.toSq = target := Chess.Parsing.promotionMoves_mem_toSq_eq m _ hIn
              have hSq :
                  Movement.squareFromInts (src.fileInt + (-1)) (src.rankInt + dir) = some m.toSq := by
                simpa [hTo] using hSqNeg
              have hPC :
                  Movement.isPawnCapture color src m.toSq :=
                isPawnCapture_of_step color src m.toSq (-1) (Or.inl rfl) hSq
              refine ⟨hPC, ?_⟩
              right
              refine ⟨?_, ?_⟩
              ·
                have hPres := promotionMoves_mem_preserves_squares m
                  { piece := p, fromSq := src, toSq := target, isCapture := true } hIn
                simpa [hPres.2.2.2.2] using rfl
              · simp [board, color, hTo, hEnemy]
          | inr hAcc =>
              -- Fall back to the `df = 1` case.
              cases hSqPos : Movement.squareFromInts (src.fileInt + 1) (src.rankInt + dir) with
              | none =>
                  cases (show False by simpa [hSqPos] using hAcc)
              | some targetPos =>
                  cases hEnemyPos : Rules.isEnemyNonKingAt board color targetPos with
                  | true =>
                      have hIn :
                          m ∈ Rules.promotionMoves { piece := p, fromSq := src, toSq := targetPos, isCapture := true } := by
                        simpa [hSqPos, hEnemyPos] using hAcc
                      have hTo : m.toSq = targetPos := Chess.Parsing.promotionMoves_mem_toSq_eq m _ hIn
                      have hSq :
                          Movement.squareFromInts (src.fileInt + 1) (src.rankInt + dir) = some m.toSq := by
                        simpa [hTo] using hSqPos
                      have hPC :
                          Movement.isPawnCapture color src m.toSq :=
                        isPawnCapture_of_step color src m.toSq 1 (Or.inr rfl) hSq
                      refine ⟨hPC, ?_⟩
                      right
                      refine ⟨?_, ?_⟩
                      ·
                        have hPres := promotionMoves_mem_preserves_squares m
                          { piece := p, fromSq := src, toSq := targetPos, isCapture := true } hIn
                        simpa [hPres.2.2.2.2] using rfl
                      · simp [board, color, hTo, hEnemyPos]
                  | false =>
                      by_cases hEP : gs.enPassantTarget = some targetPos ∧ Rules.isEmpty board targetPos ∧ Rules.enPassantFromHistory gs targetPos = true
                      · have hEqOr :
                            m = { piece := p
                                  fromSq := src
                                  toSq := targetPos
                                  isCapture := true
                                  isEnPassant := true } := by
                          simpa [hSqPos, hEnemyPos, hEP] using hAcc
                        subst hEqOr
                        have hPC :
                            Movement.isPawnCapture color src targetPos :=
                          isPawnCapture_of_step color src targetPos 1 (Or.inr rfl) hSqPos
                        refine ⟨hPC, ?_⟩
                        left
                        refine ⟨rfl, hEP.1, hEP.2.1, hEP.2.2⟩
                      ·
                        cases (show False by
                          simpa [hSqPos, hEnemyPos, hEP] using hAcc)
      | false =>
          by_cases hEP : gs.enPassantTarget = some target ∧ Rules.isEmpty board target ∧ Rules.enPassantFromHistory gs target = true
          · have hEqOr :
                m =
                    { piece := p
                      fromSq := src
                      toSq := target
                      isCapture := true
                      isEnPassant := true } ∨
                  m ∈
                    match Movement.squareFromInts (src.fileInt + 1) (src.rankInt + dir) with
                    | some targetPos =>
                        if Rules.isEnemyNonKingAt board color targetPos = true then
                          Rules.promotionMoves
                              { piece := p, fromSq := src, toSq := targetPos, isCapture := true }
                        else if gs.enPassantTarget = some targetPos ∧ Rules.isEmpty board targetPos ∧ Rules.enPassantFromHistory gs targetPos = true then
                          [{ piece := p
                             fromSq := src
                             toSq := targetPos
                             isCapture := true
                             isEnPassant := true }]
                        else []
                    | none => [] := by
              simpa [hSqNeg, hEnemy, hEP, List.mem_cons, stepFn] using hCapMem'
            cases hEqOr with
            | inl hEq =>
                subst hEq
                have hPC :
                    Movement.isPawnCapture color src target :=
                  isPawnCapture_of_step color src target (-1) (Or.inl rfl) hSqNeg
                refine ⟨hPC, ?_⟩
                left
                refine ⟨rfl, hEP.1, hEP.2.1, hEP.2.2⟩
            | inr hAcc =>
                -- Delegate to the `df = 1` analysis.
                cases hSqPos : Movement.squareFromInts (src.fileInt + 1) (src.rankInt + dir) with
                | none =>
                    cases (show False by simpa [hSqPos] using hAcc)
                | some targetPos =>
                    cases hEnemyPos : Rules.isEnemyNonKingAt board color targetPos with
                    | true =>
                        have hIn :
                            m ∈ Rules.promotionMoves { piece := p, fromSq := src, toSq := targetPos, isCapture := true } := by
                          simpa [hSqPos, hEnemyPos] using hAcc
                        have hTo : m.toSq = targetPos := Chess.Parsing.promotionMoves_mem_toSq_eq m _ hIn
                        have hSq :
                            Movement.squareFromInts (src.fileInt + 1) (src.rankInt + dir) = some m.toSq := by
                          simpa [hTo] using hSqPos
                        have hPC :
                            Movement.isPawnCapture color src m.toSq :=
                          isPawnCapture_of_step color src m.toSq 1 (Or.inr rfl) hSq
                        refine ⟨hPC, ?_⟩
                        right
                        refine ⟨?_, ?_⟩
                        ·
                          have hPres := promotionMoves_mem_preserves_squares m
                            { piece := p, fromSq := src, toSq := targetPos, isCapture := true } hIn
                          simpa [hPres.2.2.2.2] using rfl
                        · simp [board, color, hTo, hEnemyPos]
                    | false =>
                        by_cases hEP' : gs.enPassantTarget = some targetPos ∧ Rules.isEmpty board targetPos ∧ Rules.enPassantFromHistory gs targetPos = true
                        · have hEqOr' :
                              m = { piece := p
                                    fromSq := src
                                    toSq := targetPos
                                    isCapture := true
                                    isEnPassant := true } := by
                            simpa [hSqPos, hEnemyPos, hEP'] using hAcc
                          subst hEqOr'
                          have hPC :
                              Movement.isPawnCapture color src targetPos :=
                            isPawnCapture_of_step color src targetPos 1 (Or.inr rfl) hSqPos
                          refine ⟨hPC, ?_⟩
                          left
                          exact ⟨rfl, hEP'.1, hEP'.2.1, hEP'.2.2⟩
                        ·
                          cases (show False by
                            simpa [hSqPos, hEnemyPos, hEP'] using hAcc)
          ·
            have hAcc :
                m ∈
                  match Movement.squareFromInts (src.fileInt + 1) (src.rankInt + dir) with
                  | some target =>
                      if Rules.isEnemyNonKingAt board color target = true then
                        Rules.promotionMoves { piece := p, fromSq := src, toSq := target, isCapture := true }
                      else if gs.enPassantTarget = some target ∧ Rules.isEmpty board target ∧ Rules.enPassantFromHistory gs target = true then
                        [{ piece := p
                           fromSq := src
                           toSq := target
                           isCapture := true
                           isEnPassant := true }]
                      else []
                  | none => [] := by
              simpa [hSqNeg, hEnemy, hEP, stepFn] using hCapMem'
            -- Delegate to the `df = 1` analysis (same as earlier).
            cases hSqPos : Movement.squareFromInts (src.fileInt + 1) (src.rankInt + dir) with
            | none =>
                cases (show False by simpa [hSqPos] using hAcc)
            | some targetPos =>
                cases hEnemyPos : Rules.isEnemyNonKingAt board color targetPos with
                | true =>
                    have hIn :
                        m ∈ Rules.promotionMoves { piece := p, fromSq := src, toSq := targetPos, isCapture := true } := by
                      simpa [hSqPos, hEnemyPos] using hAcc
                    have hTo : m.toSq = targetPos := Chess.Parsing.promotionMoves_mem_toSq_eq m _ hIn
                    have hSq :
                        Movement.squareFromInts (src.fileInt + 1) (src.rankInt + dir) = some m.toSq := by
                      simpa [hTo] using hSqPos
                    have hPC :
                        Movement.isPawnCapture color src m.toSq :=
                      isPawnCapture_of_step color src m.toSq 1 (Or.inr rfl) hSq
                    refine ⟨hPC, ?_⟩
                    right
                    refine ⟨?_, ?_⟩
                    ·
                      have hPres := promotionMoves_mem_preserves_squares m
                        { piece := p, fromSq := src, toSq := targetPos, isCapture := true } hIn
                      simpa [hPres.2.2.2.2] using rfl
                    · simp [board, color, hTo, hEnemyPos]
                | false =>
                    by_cases hEP' : gs.enPassantTarget = some targetPos ∧ Rules.isEmpty board targetPos ∧ Rules.enPassantFromHistory gs targetPos = true
                    · have hEqOr :
                          m = { piece := p
                                fromSq := src
                                toSq := targetPos
                                isCapture := true
                                isEnPassant := true } := by
                        simpa [hSqPos, hEnemyPos, hEP'] using hAcc
                      subst hEqOr
                      have hPC :
                          Movement.isPawnCapture color src targetPos :=
                        isPawnCapture_of_step color src targetPos 1 (Or.inr rfl) hSqPos
                      refine ⟨hPC, ?_⟩
                      left
                      exact ⟨rfl, hEP'.1, hEP'.2.1, hEP'.2.2⟩
                    ·
                      cases (show False by
                        simpa [hSqPos, hEnemyPos, hEP'] using hAcc)

theorem pawn_quiet_semantics_of_mem_pieceTargets
    (gs : GameState) (src : Square) (p : Piece) (m : Move)
    (hPawn : p.pieceType = PieceType.Pawn)
    (hTargets : m ∈ pieceTargets gs src p)
    (hCap : m.isCapture = false) :
    Movement.isPawnAdvance p.color src m.toSq ∧
      Rules.pathClear gs.board src m.toSq = true ∧
        (Movement.rankDiff src m.toSq = -2 * Movement.pawnDirection p.color →
          src.rankNat = pawnStartRank p.color) := by
  let board := gs.board
  let color := p.color
  let dir := Movement.pawnDirection color
  let oneStep := Movement.squareFromInts src.fileInt (src.rankInt + dir)
  let twoStep := Movement.squareFromInts src.fileInt (src.rankInt + 2 * dir)
  let forwardMoves : List Move :=
    match oneStep with
    | some target =>
        if Rules.isEmpty board target then
          let base : List Move := [{ piece := p, fromSq := src, toSq := target }]
          let doubleStep : List Move :=
            if src.rankNat = Rules.pawnStartRank color then
              match twoStep with
              | some target2 =>
                  if Rules.isEmpty board target2 then
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
  let stepFn : Int → List Move → List Move :=
    fun df acc =>
      match Movement.squareFromInts (src.fileInt + df) (src.rankInt + dir) with
      | some target =>
          if Rules.isEnemyNonKingAt board color target then
            Rules.promotionMoves { piece := p, fromSq := src, toSq := target, isCapture := true } ++ acc
          else if gs.enPassantTarget = some target ∧ Rules.isEmpty board target ∧ Rules.enPassantFromHistory gs target = true then
            { piece := p, fromSq := src, toSq := target, isCapture := true, isEnPassant := true } :: acc
          else
            acc
      | none => acc
  let captureMoves : List Move := ([-1, 1] : List Int).foldr stepFn []
  have hMem' :
      m ∈ forwardMoves.foldr (fun mv acc => Rules.promotionMoves mv ++ acc) [] ++ captureMoves := by
    simpa [Rules.pieceTargets, hPawn, board, color, dir, oneStep, twoStep, forwardMoves, stepFn, captureMoves] using
      hTargets
  have hCaptureAllCap :
      m ∈ captureMoves → False := by
    intro hIn
    -- Show every capture-move has `isCapture = true`.
    let acc1 : List Move := stepFn 1 []
    have hAcc1 : m ∈ acc1 → m.isCapture = true := by
      intro hMemAcc1
      dsimp [acc1, stepFn] at hMemAcc1
      cases hSq1 : Movement.squareFromInts (src.fileInt + 1) (src.rankInt + dir) with
      | none =>
          cases (show False by simpa [hSq1] using hMemAcc1)
      | some target =>
          cases hEnemy1 : Rules.isEnemyNonKingAt board color target with
          | true =>
              have hInProm :
                  m ∈ Rules.promotionMoves { piece := p, fromSq := src, toSq := target, isCapture := true } := by
                simpa [hSq1, hEnemy1] using hMemAcc1
              have hEq := Chess.Parsing.promotionMoves_mem_isCapture_eq m _ hInProm
              simp [hEq]
          | false =>
              by_cases hEP1 : gs.enPassantTarget = some target ∧ Rules.isEmpty board target ∧ Rules.enPassantFromHistory gs target = true
              · have hEq :
                    m = { piece := p, fromSq := src, toSq := target, isCapture := true, isEnPassant := true } := by
                  simpa [hSq1, hEnemy1, hEP1] using hMemAcc1
                subst hEq
                simp
              · cases (show False by simpa [hSq1, hEnemy1, hEP1] using hMemAcc1)
    have hCapAll : m ∈ stepFn (-1) acc1 → m.isCapture = true := by
      intro hMemCap
      dsimp [stepFn] at hMemCap
      cases hSqN : Movement.squareFromInts (src.fileInt + (-1)) (src.rankInt + dir) with
      | none =>
          have hInAcc : m ∈ acc1 := by simpa [hSqN] using hMemCap
          exact hAcc1 hInAcc
      | some target =>
          cases hEnemyN : Rules.isEnemyNonKingAt board color target with
          | true =>
              have hSplit :
                  m ∈ Rules.promotionMoves { piece := p, fromSq := src, toSq := target, isCapture := true } ∨
                    m ∈ acc1 := by
                simpa [hSqN, hEnemyN, List.mem_append] using hMemCap
              cases hSplit with
              | inl hInProm =>
                  have hEq := Chess.Parsing.promotionMoves_mem_isCapture_eq m _ hInProm
                  simp [hEq]
              | inr hInAcc =>
                  exact hAcc1 hInAcc
          | false =>
              by_cases hEPN : gs.enPassantTarget = some target ∧ Rules.isEmpty board target ∧ Rules.enPassantFromHistory gs target = true
              · have hEqOr :
                    m = { piece := p, fromSq := src, toSq := target, isCapture := true, isEnPassant := true } ∨
                      m ∈ acc1 := by
                  simpa [hSqN, hEnemyN, hEPN, List.mem_cons] using hMemCap
                cases hEqOr with
                | inl hEq =>
                    subst hEq
                    simp
                | inr hInAcc =>
                    exact hAcc1 hInAcc
              ·
                have hInAcc : m ∈ acc1 := by
                  simpa [hSqN, hEnemyN, hEPN] using hMemCap
                exact hAcc1 hInAcc
    have hInUnrolled : m ∈ stepFn (-1) (stepFn 1 []) := by
      simpa [captureMoves, List.foldr] using hIn
    have : m.isCapture = true := by
      simpa [acc1] using hCapAll hInUnrolled
    cases (show False by simpa [hCap] using this)
  have hForwardMem : m ∈ forwardMoves.foldr (fun mv acc => Rules.promotionMoves mv ++ acc) [] := by
    cases List.mem_append.1 hMem' with
    | inl hForward => exact hForward
    | inr hCapture => exact (hCaptureAllCap hCapture).elim
  rcases (Chess.Parsing.List.mem_foldr_append_iff (f := Rules.promotionMoves) (b := m) forwardMoves).1 hForwardMem with
    ⟨base, hBaseMem, hInProm⟩
  have hToEq : m.toSq = base.toSq := Chess.Parsing.promotionMoves_mem_toSq_eq m base hInProm
  -- Identify whether `base` is the one-step or two-step forward move.
  dsimp [forwardMoves] at hBaseMem
  cases hOne : oneStep with
  | none =>
      cases (show False by simpa [hOne] using hBaseMem)
  | some target =>
      cases hEmpty : Rules.isEmpty board target with
      | false =>
          cases (show False by simpa [hOne, hEmpty] using hBaseMem)
      | true =>
          have hMem'' :
              base ∈ [{ piece := p, fromSq := src, toSq := target }] ++
                (if src.rankNat = Rules.pawnStartRank color then
                    match twoStep with
                    | some target2 =>
                        if Rules.isEmpty board target2 then
                          [{ piece := p, fromSq := src, toSq := target2 }]
                        else
                          []
                    | none => []
                  else
                    []) := by
            simpa [hOne, hEmpty] using hBaseMem
          cases List.mem_append.1 hMem'' with
          | inl hIn =>
              have hEq : base = { piece := p, fromSq := src, toSq := target } := by
                simpa using hIn
              subst hEq
              have hSq :
                  Movement.squareFromInts src.fileInt (src.rankInt + dir) = some m.toSq := by
                simpa [hToEq] using hOne
              have hAdv : Movement.isPawnAdvance color src m.toSq :=
                isPawnAdvance_of_oneStep color src m.toSq hSq
              have hPC : Rules.pathClear gs.board src m.toSq = true := by
                unfold Rules.pathClear
                simp [squaresBetween_pawn_oneStep color src m.toSq hSq]
              refine ⟨hAdv, hPC, ?_⟩
              intro hDouble
              -- One-step advances cannot satisfy the double-step rankDiff predicate.
              have hrd : Movement.rankDiff src m.toSq = -Movement.pawnDirection color := by
                have hRank :
                    m.toSq.rankInt = src.rankInt + Movement.pawnDirection color :=
                  Movement.squareFromInts_rankInt src.fileInt (src.rankInt + Movement.pawnDirection color) m.toSq hSq
                unfold Movement.rankDiff
                simp [hRank]
                omega
              have : (-Movement.pawnDirection color : Int) = -2 * Movement.pawnDirection color := by
                simpa [hrd] using hDouble
              have hDirNe : Movement.pawnDirection color ≠ 0 := pawnDirection_ne_zero color
              have : Movement.pawnDirection color = 0 := by
                omega
              exact (hDirNe this).elim
          | inr hIn =>
              by_cases hStart : src.rankNat = Rules.pawnStartRank color
              · cases hTwo : twoStep with
                | none =>
                    cases (show False by simpa [hStart, hTwo] using hIn)
                | some target2 =>
                    cases hEmpty2 : Rules.isEmpty board target2 with
                    | false =>
                        cases (show False by simpa [hStart, hTwo, hEmpty2] using hIn)
                    | true =>
                        have hEq : base = { piece := p, fromSq := src, toSq := target2 } := by
                          simpa [hStart, hTwo, hEmpty2] using hIn
                        subst hEq
                        have hSq :
                            Movement.squareFromInts src.fileInt (src.rankInt + 2 * dir) = some m.toSq := by
                          simpa [hToEq] using hTwo
                        have hAdv : Movement.isPawnAdvance color src m.toSq :=
                          isPawnAdvance_of_twoStep color src m.toSq hSq
                        have hPC : Rules.pathClear gs.board src m.toSq = true := by
                          -- The intermediate square is exactly `target` from `oneStep`.
                          have hBetween : Movement.squaresBetween src m.toSq = [target] := by
                            have hTgt : Movement.squareFromInts src.fileInt (src.rankInt + 2 * dir) = some m.toSq := hSq
                            have hMid : Movement.squareFromInts src.fileInt (src.rankInt + dir) = some target := hOne
                            simpa using squaresBetween_pawn_twoStep color src m.toSq target hTgt hMid
                          unfold Rules.pathClear
                          have hEmptyMid : gs.board target = none := by
                            -- `isEmpty = true` unfolds to the board equality.
                            simpa [Rules.isEmpty] using hEmpty
                          simp [hBetween, hEmptyMid]
                        refine ⟨hAdv, hPC, ?_⟩
                        intro _hDouble
                        exact hStart
              · cases (show False by simpa [hStart] using hIn)

theorem respectsGeometry_of_pieceTargets_pawn
    (gs : GameState) (src : Square) (p : Piece) (m : Move)
    (hPawn : p.pieceType = PieceType.Pawn) :
    m ∈ pieceTargets gs src p →
    respectsGeometry gs m := by
  intro hMem
  have hPieceFrom : m.piece = p ∧ m.fromSq = src :=
    Chess.Parsing.mem_pawn_pieceTargets_piece_fromSq gs src p m hPawn hMem
  have hPt : m.piece.pieceType = PieceType.Pawn := by
    simp [hPieceFrom.1, hPawn]
  -- Split on capture flag.
  by_cases hCap : m.isCapture = true
  · have hInfo := pawn_capture_semantics_of_mem_pieceTargets gs src p m hPawn hMem hCap
    have hCapGeom :
        Movement.isPawnCapture m.piece.color m.fromSq m.toSq := by
      simpa [hPieceFrom.1, hPieceFrom.2] using hInfo.1
    unfold respectsGeometry
    simp [hPt, hCap]
    cases hEP : m.isEnPassant with
    | false =>
        -- Enemy capture branch.
        refine ⟨hCapGeom, ?_⟩
        cases hInfo.2 with
        | inl hBad =>
            have : False := by simpa [hEP] using hBad.1
            exact this.elim
        | inr hEnemy =>
            have hEnemyAt : isEnemyAt gs.board m.piece.color m.toSq = true :=
              isEnemyAt_of_isEnemyNonKingAt_true gs.board m.piece.color m.toSq (by
                simpa [hPieceFrom.1] using hEnemy.2)
            simpa [hPieceFrom.1, hPieceFrom.2, hEP] using hEnemyAt
      | true =>
          refine ⟨hCapGeom, ?_⟩
          cases hInfo.2 with
          | inl hEPInfo =>
              exact hEPInfo.2
          | inr hBad =>
              have : False := by simpa [hEP] using hBad.1
              exact this.elim
  · have hInfo := pawn_quiet_semantics_of_mem_pieceTargets gs src p m hPawn hMem (by
        cases hCap0 : m.isCapture with
        | false => simpa using hCap0
        | true => cases (show False by simpa [hCap] using hCap0))
    have hAdv :
        Movement.isPawnAdvance m.piece.color m.fromSq m.toSq := by
      simpa [hPieceFrom.1, hPieceFrom.2] using hInfo.1
    have hPC :
        Rules.pathClear gs.board m.fromSq m.toSq = true := by
      simpa [hPieceFrom.2] using hInfo.2.1
    have hStart :
        (Movement.rankDiff m.fromSq m.toSq = -2 * Movement.pawnDirection m.piece.color →
          m.fromSq.rankNat = pawnStartRank m.piece.color) := by
      simpa [hPieceFrom.1, hPieceFrom.2] using hInfo.2.2
    unfold respectsGeometry
    simp [hPt, hCap]
    exact ⟨hAdv, hPC, hStart⟩

end Rules
end Chess
