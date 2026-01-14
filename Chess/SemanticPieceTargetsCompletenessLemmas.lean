import Init.Omega
import Chess.ParsingProofs
import Chess.SemanticPromotionSoundnessLemmas
import Chess.SlidingTargetsCompletenessHelpers
import Chess.SlidingTargetsDeltaLemmas
import Chess.Spec

namespace Chess
namespace Rules

private theorem move_eq_record_of_fields (m : Move) (cap : Bool) :
    m.isCapture = cap →
    m.promotion = none →
    m.isCastle = false →
    m.castleRookFrom = none →
    m.castleRookTo = none →
    m.isEnPassant = false →
    ({ piece := m.piece, fromSq := m.fromSq, toSq := m.toSq, isCapture := cap } : Move) = m := by
  intro hCap hPromo hCastle hRF hRT hEP
  cases m with
  | mk piece fromSq toSq isCapture promotion isCastle castleRookFrom castleRookTo isEnPassant =>
      cases cap <;> simp at hCap hPromo hCastle hRF hRT hEP
      · simp [hCap, hPromo, hCastle, hRF, hRT, hEP]
      · simp [hCap, hPromo, hCastle, hRF, hRT, hEP]

private theorem promotion_eq_none_of_not_pawn (gs : GameState) (m : Move) :
    fideLegalSemantic gs m →
    m.piece.pieceType ≠ PieceType.Pawn →
    m.promotion = none := by
  intro hSem hNotPawn
  rcases hSem with
    ⟨_hTurn, _hFrom, _hGeom, _hDest, _hCapSpec, _hNotCheck, _hPromoFwd, hPromoBack, _hCastleClause,
      _hEPFlag, _hCastleFlag, _hRookFields⟩
  cases hProm : m.promotion with
  | none => rfl
  | some pt =>
      have : m.promotion.isSome := by
        simp [hProm]
      have hPawn : m.piece.pieceType = PieceType.Pawn := (hPromoBack this).1
      cases hNotPawn hPawn

private theorem isEnPassant_eq_false_of_not_pawn (gs : GameState) (m : Move) :
    fideLegalSemantic gs m →
    m.piece.pieceType ≠ PieceType.Pawn →
    m.isEnPassant = false := by
  intro hSem hNotPawn
  rcases hSem with
    ⟨_hTurn, _hFrom, _hGeom, _hDest, _hCapSpec, _hNotCheck, _hPromoFwd, _hPromoBack, _hCastleClause,
      hEPFlag, _hCastleFlag, _hRookFields⟩
  cases hEP : m.isEnPassant with
  | false => rfl
  | true =>
      have : m.isEnPassant := by simp [hEP]
      have hPawn : m.piece.pieceType = PieceType.Pawn := hEPFlag this
      cases hNotPawn hPawn

private theorem isCastle_eq_false_of_not_king (gs : GameState) (m : Move) :
    fideLegalSemantic gs m →
    m.piece.pieceType ≠ PieceType.King →
    m.isCastle = false := by
  intro hSem hNotKing
  rcases hSem with
    ⟨_hTurn, _hFrom, _hGeom, _hDest, _hCapSpec, _hNotCheck, _hPromoFwd, _hPromoBack, _hCastleClause,
      _hEPFlag, hCastleFlag, _hRookFields⟩
  cases hC : m.isCastle with
  | false => rfl
  | true =>
      have : m.isCastle := by simp [hC]
      have hKing : m.piece.pieceType = PieceType.King := hCastleFlag this
      cases hNotKing hKing

private theorem capture_eq_of_target_empty (gs : GameState) (m : Move) :
    fideLegalSemantic gs m →
    m.isEnPassant = false →
    gs.board m.toSq = none →
    m.isCapture = false := by
  intro hSem hEP hEmpty
  rcases hSem with
    ⟨_hTurn, _hFrom, _hGeom, _hDest, hCapSpec, _hNotCheck, _hPromoFwd, _hPromoBack, _hCastleClause,
      _hEPFlag, _hCastleFlag, _hRookFields⟩
  have hNoEnemy : ¬(∃ p, gs.board m.toSq = some p ∧ p.color ≠ m.piece.color) := by
    intro hEx
    rcases hEx with ⟨p, hAt, _hNe⟩
    simpa [hEmpty] using hAt
  have hRhsFalse : ¬((∃ p, gs.board m.toSq = some p ∧ p.color ≠ m.piece.color) ∨ m.isEnPassant) := by
    intro hRhs
    rcases hRhs with hEx | hEP'
    · exact hNoEnemy hEx
    · cases (show False by simpa [hEP] using hEP')
  -- If `m.isCapture = true`, the RHS must hold by the iff.
  cases hCap : m.isCapture with
  | false => rfl
  | true =>
      have : False := hRhsFalse (hCapSpec.1 (by simp [hCap]))
      cases this

private theorem capture_eq_true_of_target_enemy (gs : GameState) (m : Move) (p : Piece) :
    fideLegalSemantic gs m →
    gs.board m.toSq = some p →
    destinationFriendlyFreeProp gs m →
    m.isEnPassant = false →
    m.isCapture = true := by
  intro hSem hAt hDest hEP
  rcases hSem with
    ⟨_hTurn, _hFrom, _hGeom, _hDest2, hCapSpec, _hNotCheck, _hPromoFwd, _hPromoBack, _hCastleClause,
      _hEPFlag, _hCastleFlag, _hRookFields⟩
  have hEnemy : p.color ≠ m.piece.color := by
    unfold destinationFriendlyFreeProp destinationFriendlyFree at hDest
    have hBoth : p.color ≠ m.piece.color ∧ p.pieceType ≠ PieceType.King := by
      have : decide (p.color ≠ m.piece.color ∧ p.pieceType ≠ PieceType.King) = true := by
        simpa [hAt] using hDest
      simpa [decide_eq_true_eq] using this
    exact hBoth.1
  have hRhs : (∃ q, gs.board m.toSq = some q ∧ q.color ≠ m.piece.color) ∨ m.isEnPassant := by
    left
    exact ⟨p, hAt, hEnemy⟩
  have : m.isCapture = true := hCapSpec.2 hRhs
  simpa using this

theorem fideLegalSemantic_implies_mem_pieceTargets_knight (gs : GameState) (m : Move) :
    fideLegalSemantic gs m →
    m.piece.pieceType = PieceType.Knight →
    m ∈ pieceTargets gs m.fromSq m.piece := by
  intro hSem hKnight
  have hSem0 := hSem
  rcases hSem with
    ⟨_hTurn, _hFrom, hGeom, hDest, _hCapSpec, _hNotCheck, _hPromoFwd, _hPromoBack, _hCastleClause,
      _hEPFlag, _hCastleFlag, hRookFields⟩
  have hNotPawn : m.piece.pieceType ≠ PieceType.Pawn := by
    intro hPawn
    simpa [hPawn] using hKnight
  have hNotKing : m.piece.pieceType ≠ PieceType.King := by
    intro hKing
    simpa [hKing] using hKnight
  have hEP : m.isEnPassant = false := isEnPassant_eq_false_of_not_pawn gs m hSem0 hNotPawn
  have hCastle : m.isCastle = false := isCastle_eq_false_of_not_king gs m hSem0 hNotKing
  have hPromo : m.promotion = none := promotion_eq_none_of_not_pawn gs m hSem0 hNotPawn
  have hRookNone : m.castleRookFrom = none ∧ m.castleRookTo = none := by
    have : ¬m.isCastle := by simp [hCastle]
    exact hRookFields this

  have hMove : Movement.isKnightMove m.fromSq m.toSq := by
    -- `respectsGeometry` for knights is exactly `isKnightMove`.
    simpa [respectsGeometry, hKnight] using hGeom

  -- Unfold the knight branch and provide the witness square.
  unfold pieceTargets
  -- `simp` exposes the underlying `filterMap` membership as an explicit witness goal.
  simp [hKnight]
  refine ⟨m.toSq, ?_, ?_, ?_⟩
  · exact (Movement.mem_knightTargets_iff m.fromSq m.toSq).2 hMove
  ·
    have hFree : destinationFriendlyFree gs { piece := m.piece, fromSq := m.fromSq, toSq := m.toSq } = true := by
      simpa [destinationFriendlyFreeProp] using hDest
    simpa using hFree
  ·
    cases hAt : gs.board.get m.toSq with
    | none =>
        have hAt' : gs.board m.toSq = none := by simpa using hAt
        have hCap : m.isCapture = false :=
          capture_eq_of_target_empty gs m hSem0 hEP hAt'
        have hEqMove :
            ({ piece := m.piece, fromSq := m.fromSq, toSq := m.toSq, isCapture := false } : Move) = m :=
          move_eq_record_of_fields m false hCap hPromo hCastle hRookNone.1 hRookNone.2 hEP
        simpa [hAt] using congrArg some hEqMove
    | some p =>
        have hAt' : gs.board m.toSq = some p := by simpa using hAt
        have hCap : m.isCapture = true :=
          capture_eq_true_of_target_enemy gs m p hSem0 hAt' hDest hEP
        have hEqMove :
            ({ piece := m.piece, fromSq := m.fromSq, toSq := m.toSq, isCapture := true } : Move) = m :=
          move_eq_record_of_fields m true hCap hPromo hCastle hRookNone.1 hRookNone.2 hEP
        simpa [hAt] using congrArg some hEqMove

theorem fideLegalSemantic_implies_mem_pieceTargets_king_not_castle (gs : GameState) (m : Move) :
    fideLegalSemantic gs m →
    m.piece.pieceType = PieceType.King →
    m.isCastle = false →
    m ∈ pieceTargets gs m.fromSq m.piece := by
  intro hSem hKing hNotCastle
  have hSem0 := hSem
  rcases hSem with
    ⟨_hTurn, _hFrom, hGeom, hDest, _hCapSpec, _hNotCheck, _hPromoFwd, _hPromoBack, _hCastleClause,
      _hEPFlag, _hCastleFlag, hRookFields⟩
  have hNotPawn : m.piece.pieceType ≠ PieceType.Pawn := by
    intro hPawn
    simpa [hPawn] using hKing
  have hEP : m.isEnPassant = false := isEnPassant_eq_false_of_not_pawn gs m hSem0 hNotPawn
  have hPromo : m.promotion = none := promotion_eq_none_of_not_pawn gs m hSem0 hNotPawn
  have hRookNone : m.castleRookFrom = none ∧ m.castleRookTo = none := by
    have : ¬m.isCastle := by simp [hNotCastle]
    exact hRookFields this

  have hMove : Movement.isKingStep m.fromSq m.toSq := by
    -- `respectsGeometry` for non-castle kings is `isKingStep`.
    simpa [respectsGeometry, hKing, hNotCastle] using hGeom

  unfold pieceTargets
  -- Reduce to the `standard` part (left disjunct), since `m.isCastle = false`.
  simp [hKing]
  left
  refine ⟨m.toSq, ?_, ?_, ?_⟩
  · exact (Movement.mem_kingTargets_iff m.fromSq m.toSq).2 hMove
  ·
    have hFree : destinationFriendlyFree gs { piece := m.piece, fromSq := m.fromSq, toSq := m.toSq } = true := by
      simpa [destinationFriendlyFreeProp] using hDest
    simpa using hFree
  ·
    cases hAt : gs.board.get m.toSq with
    | none =>
        have hAt' : gs.board m.toSq = none := by simpa using hAt
        have hCap : m.isCapture = false :=
          capture_eq_of_target_empty gs m hSem0 hEP hAt'
        have hEqMove :
            ({ piece := m.piece, fromSq := m.fromSq, toSq := m.toSq, isCapture := false } : Move) = m :=
          move_eq_record_of_fields m false hCap hPromo hNotCastle hRookNone.1 hRookNone.2 hEP
        simpa [hAt] using congrArg some hEqMove
    | some p =>
        have hAt' : gs.board m.toSq = some p := by simpa using hAt
        have hCap : m.isCapture = true :=
          capture_eq_true_of_target_enemy gs m p hSem0 hAt' hDest hEP
        have hEqMove :
            ({ piece := m.piece, fromSq := m.fromSq, toSq := m.toSq, isCapture := true } : Move) = m :=
          move_eq_record_of_fields m true hCap hPromo hNotCastle hRookNone.1 hRookNone.2 hEP
        simpa [hAt] using congrArg some hEqMove

theorem fideLegalSemantic_implies_mem_pieceTargets_rook (gs : GameState) (m : Move) :
    fideLegalSemantic gs m →
    m.piece.pieceType = PieceType.Rook →
    m ∈ pieceTargets gs m.fromSq m.piece := by
  intro hSem hRook
  have hSem0 := hSem
  rcases hSem with
    ⟨_hTurn, _hFrom, hGeom, hDest, _hCapSpec, _hNotCheck, _hPromoFwd, _hPromoBack, _hCastleClause,
      _hEPFlag, _hCastleFlag, hRookFields⟩
  have hNotPawn : m.piece.pieceType ≠ PieceType.Pawn := by
    intro hPawn
    simpa [hPawn] using hRook
  have hNotKing : m.piece.pieceType ≠ PieceType.King := by
    intro hKing
    simpa [hKing] using hRook
  have hEP : m.isEnPassant = false := isEnPassant_eq_false_of_not_pawn gs m hSem0 hNotPawn
  have hCastle : m.isCastle = false := isCastle_eq_false_of_not_king gs m hSem0 hNotKing
  have hPromo : m.promotion = none := promotion_eq_none_of_not_pawn gs m hSem0 hNotPawn
  have hRookNone : m.castleRookFrom = none ∧ m.castleRookTo = none := by
    have : ¬m.isCastle := by simp [hCastle]
    exact hRookFields this

  have hGeom' : Movement.isRookMove m.fromSq m.toSq ∧ Rules.pathClear gs.board m.fromSq m.toSq := by
    simpa [respectsGeometry, hRook] using hGeom
  have hMove : Movement.isRookMove m.fromSq m.toSq := hGeom'.1
  have hPathClear : Rules.pathClear gs.board m.fromSq m.toSq = true := by simpa using hGeom'.2
  have hBetweenEmpty :
      ∀ sq, sq ∈ Movement.squaresBetween m.fromSq m.toSq → gs.board sq = none := by
    exact (Rules.pathClear_eq_true_iff gs.board m.fromSq m.toSq).1 hPathClear

  let k : Nat := Movement.rookOffset m.fromSq m.toSq
  have hkLe7 : k ≤ 7 := by
    simpa [k] using (Chess.Movement.rookOffset_le_7 m.fromSq m.toSq hMove)
  have hkPos : 0 < k := by
    -- One of the diffs is non-zero for a rook move.
    cases hMove.2 with
    | inl h =>
        have hrdNe : Movement.rankDiff m.fromSq m.toSq ≠ 0 := h.2
        have : 0 < (Movement.rankDiff m.fromSq m.toSq).natAbs := (Int.natAbs_pos).2 hrdNe
        simpa [k, Movement.rookOffset, h.1] using this
    | inr h =>
        have hfdNe : Movement.fileDiff m.fromSq m.toSq ≠ 0 := h.2
        have : 0 < (Movement.fileDiff m.fromSq m.toSq).natAbs := (Int.natAbs_pos).2 hfdNe
        simpa [k, Movement.rookOffset, h.1] using this

  let df : Int := (Movement.rookDelta m.fromSq m.toSq).1
  let dr : Int := (Movement.rookDelta m.fromSq m.toSq).2
  have hDeltaMem :
      Movement.rookDelta m.fromSq m.toSq ∈ [(1, 0), (-1, 0), (0, 1), (0, -1)] :=
    Chess.Movement.rookDelta_mem_rookDeltas m.fromSq m.toSq hMove

  have hEmptyIntermediate :
      ∀ t, 1 ≤ t → t < k →
        ∀ sq,
          Movement.squareFromInts (m.fromSq.fileInt + df * (t : Int))
              (m.fromSq.rankInt + dr * (t : Int)) =
            some sq →
          Rules.isEmpty gs.board sq = true := by
    intro t ht1 htLt sq hSq
    -- Use existence and “between-squares” membership to conclude emptiness from `pathClear`.
    have hSq' :
        Movement.squareFromInts (m.fromSq.fileInt + (Movement.rookDelta m.fromSq m.toSq).1 * (t : Int))
            (m.fromSq.rankInt + (Movement.rookDelta m.fromSq m.toSq).2 * (t : Int)) =
          some sq := by
      simpa [df, dr] using hSq
    have hMemBetween :
        sq ∈ Movement.squaresBetween m.fromSq m.toSq :=
      Chess.Movement.rook_step_square_mem_squaresBetween m.fromSq m.toSq hMove t ht1 (by simpa [k] using htLt) sq hSq'
    have hEmpty : gs.board sq = none := hBetweenEmpty sq hMemBetween
    simpa [Rules.isEmpty] using hEmpty

  -- Helper: if a move is present at the “target step”, it remains present at the initial `walk` step `7`
  -- provided the intermediate squares are empty.
  have walk_mem_to_step7 (mv : Move)
      (hBase : ∀ acc,
        mv ∈ Rules.slidingTargets.walk m.fromSq m.piece gs.board m.piece.color 7 df dr (7 - k).succ acc) :
      ∀ acc, mv ∈ Rules.slidingTargets.walk m.fromSq m.piece gs.board m.piece.color 7 df dr 7 acc := by
    intro acc
    let sTarget : Nat := 7 - k
    let stepTarget : Nat := sTarget.succ
    have hsTargetLe6 : sTarget ≤ 6 := by
      have hk1 : 1 ≤ k := Nat.succ_le_of_lt hkPos
      have : 7 - k ≤ 7 - 1 := Nat.sub_le_sub_left hk1 7
      simpa [sTarget] using this
    have hStepTargetLe7 : stepTarget ≤ 7 := by
      simpa [stepTarget] using (Nat.succ_le_succ hsTargetLe6)
    have hOff : 7 - sTarget = k := by
      simpa [sTarget] using (Nat.sub_sub_self hkLe7)
    -- Lift along `d = 0..(7 - stepTarget)` using the recursion equation for the empty-square branch.
    let dFinal : Nat := 7 - stepTarget
    have hLift :
        ∀ d, d ≤ dFinal →
          ∀ acc,
            mv ∈
              Rules.slidingTargets.walk m.fromSq m.piece gs.board m.piece.color 7 df dr (stepTarget + d) acc := by
      intro d hd
      induction d with
      | zero =>
          intro acc
          simpa [stepTarget, sTarget] using hBase acc
      | succ d ih =>
          intro acc
          have hd' : d ≤ dFinal := Nat.le_trans (Nat.le_of_lt (Nat.lt_succ_self d)) hd
          let pred : Nat := stepTarget + d
          -- Show the square at offset `t = 7 - pred` exists and is empty.
          have hPredLe6 : pred ≤ 6 := by
            have hStepLe7 : stepTarget + d.succ ≤ 7 := by
              have h1 : stepTarget + d.succ ≤ stepTarget + (7 - stepTarget) := Nat.add_le_add_left hd stepTarget
              simpa [Nat.add_sub_of_le hStepTargetLe7] using h1
            have : pred + 1 ≤ 7 := by
              simpa [pred, Nat.succ_eq_add_one, Nat.add_assoc] using hStepLe7
            omega
          let t : Nat := 7 - pred
          have ht1 : 1 ≤ t := by
            have hPredLt7 : pred < 7 := Nat.lt_succ_of_le hPredLe6
            have htPos : 0 < 7 - pred := Nat.sub_pos_of_lt hPredLt7
            simpa [t] using (Nat.succ_le_of_lt htPos)
          have htLt : t < k := by
            have hsTargetLt7 : sTarget < 7 := by
              have : 7 - k < 7 := Nat.sub_lt (by decide : 0 < 7) hkPos
              simpa [sTarget] using this
            have hsTargetLtPred : sTarget < pred := by
              have hsTargetLtStep : sTarget < stepTarget := by
                simpa [stepTarget] using (Nat.lt_succ_self sTarget)
              have hStepLePred : stepTarget ≤ pred := Nat.le_add_right stepTarget d
              exact Nat.lt_of_lt_of_le hsTargetLtStep hStepLePred
            have : 7 - pred < 7 - sTarget := Nat.sub_lt_sub_left hsTargetLt7 hsTargetLtPred
            simpa [t, hOff] using this
          have htLe : t ≤ k := Nat.le_of_lt htLt
          rcases Chess.Movement.squareFromInts_rookDelta_step_some m.fromSq m.toSq hMove t (by
              simpa [k] using htLe) with ⟨sq, hSq⟩
          have hSqW :
              Movement.squareFromInts (m.fromSq.fileInt + df * (t : Int))
                  (m.fromSq.rankInt + dr * (t : Int)) =
                some sq := by
            simpa [df, dr] using hSq
          have hEmptySq : Rules.isEmpty gs.board sq = true := by
            exact hEmptyIntermediate t ht1 (by simpa [k] using htLt) sq (by simpa using hSqW)
          -- Use IH at the recursive call `pred`.
          have hRec :
              mv ∈ Rules.slidingTargets.walk m.fromSq m.piece gs.board m.piece.color 7 df dr pred
                ({ piece := m.piece, fromSq := m.fromSq, toSq := sq } :: acc) :=
            ih hd' ({ piece := m.piece, fromSq := m.fromSq, toSq := sq } :: acc)
          have hStep : stepTarget + d.succ = Nat.succ pred := by
            simp [pred, stepTarget, Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          -- Unfold one `walk` layer at `step = pred.succ` and reduce to the recursive membership.
          have hSqWalk :
              Movement.squareFromInts (m.fromSq.fileInt + df * (↑(7 - pred) : Int))
                  (m.fromSq.rankInt + dr * (↑(7 - pred) : Int)) =
                some sq := by
            simpa [t] using hSqW
          rw [hStep]
          -- Unfold one `walk` layer and select the empty-square branch.
          simp [Rules.slidingTargets.walk]
          rw [hSqWalk]
          simp [hEmptySq]
          exact hRec
    have hEq : stepTarget + dFinal = 7 := Nat.add_sub_of_le hStepTargetLe7
    have hMem : mv ∈ Rules.slidingTargets.walk m.fromSq m.piece gs.board m.piece.color 7 df dr (stepTarget + dFinal) acc :=
      hLift dFinal (Nat.le_refl _) acc
    simpa [hEq, dFinal] using hMem

  -- Reduce to the rook branch of `pieceTargets`.
  unfold pieceTargets
  simp [hRook]
  -- Analyze the destination occupancy to choose the concrete move record.
  cases hAt : gs.board.get m.toSq with
  | none =>
      have hAt' : gs.board m.toSq = none := by simpa using hAt
      have hCap : m.isCapture = false := capture_eq_of_target_empty gs m hSem0 hEP hAt'
      have hEqMove :
          ({ piece := m.piece, fromSq := m.fromSq, toSq := m.toSq, isCapture := false } : Move) = m :=
        move_eq_record_of_fields m false hCap hPromo hCastle hRookNone.1 hRookNone.2 hEP
      have hEmptyTgt : Rules.isEmpty gs.board m.toSq = true := by simpa [Rules.isEmpty] using hAt'
      -- Show the move is in the correct rook ray, then in `slidingTargets`.
      let mv : Move := { piece := m.piece, fromSq := m.fromSq, toSq := m.toSq }
      have hMvDef : mv.piece = m.piece ∧ mv.fromSq = m.fromSq ∧ mv.toSq = m.toSq := by
        simp [mv]
      have hMvWalk :
          ∀ acc, mv ∈ Rules.slidingTargets.walk m.fromSq m.piece gs.board m.piece.color 7 df dr 7 acc := by
        let sTarget : Nat := 7 - k
        have hSqAtTarget :
            Movement.squareFromInts (m.fromSq.fileInt + df * Int.ofNat (7 - sTarget))
                (m.fromSq.rankInt + dr * Int.ofNat (7 - sTarget)) =
              some m.toSq := by
          have hTgt := Movement.squareFromInts_rookDelta_rookOffset m.fromSq m.toSq hMove
          simpa [sTarget, k, df, dr, Nat.sub_sub_self hkLe7] using hTgt
        have hBase :
            ∀ acc,
              mv ∈ Rules.slidingTargets.walk m.fromSq m.piece gs.board m.piece.color 7 df dr (Nat.succ sTarget) acc := by
          intro acc
          exact
            Rules.slidingTargets_walk_mem_of_empty_square m.fromSq m.piece gs.board m.piece.color 7 df dr sTarget acc
              m.toSq hSqAtTarget hEmptyTgt
        exact walk_mem_to_step7 mv (by simpa [sTarget] using hBase)
      -- Fold over deltas; pick the correct one using `rookDelta_mem_rookDeltas`.
      have hMemSliding :
          mv ∈ Rules.slidingTargets gs m.fromSq m.piece [(1, 0), (-1, 0), (0, 1), (0, -1)] := by
        unfold Rules.slidingTargets
        -- Induct over the delta list to expose the matching ray.
        have :
            ∀ (deltas : List (Int × Int)),
              Movement.rookDelta m.fromSq m.toSq ∈ deltas →
                mv ∈
                  List.foldr
                    (fun d acc =>
                      let (df0, dr0) := d
                      Rules.slidingTargets.walk m.fromSq m.piece gs.board m.piece.color 7 df0 dr0 7 acc)
                    [] deltas := by
          intro deltas hIn
          induction deltas with
          | nil =>
              cases (show False by simpa using hIn)
          | cons d rest ih =>
              have hSplit :
                  Movement.rookDelta m.fromSq m.toSq = d ∨ Movement.rookDelta m.fromSq m.toSq ∈ rest := by
                simpa [List.mem_cons] using hIn
              cases hSplit with
              | inl hEq =>
                  -- This head delta is the rook delta; show membership in its `walk`.
                  cases d with
                  | mk df0 dr0 =>
                      have hdf : df0 = df := by
                        simpa [df] using (congrArg Prod.fst hEq).symm
                      have hdr : dr0 = dr := by
                        simpa [dr] using (congrArg Prod.snd hEq).symm
                      -- `acc` is the fold of the rest.
                      let acc :=
                        rest.foldr
                          (fun d acc =>
                            let (df1, dr1) := d
                            Rules.slidingTargets.walk m.fromSq m.piece gs.board m.piece.color 7 df1 dr1 7 acc)
                          []
                      have hWalk :
                          mv ∈ Rules.slidingTargets.walk m.fromSq m.piece gs.board m.piece.color 7 df0 dr0 7 acc := by
                        simpa [hdf, hdr, acc] using hMvWalk acc
                      simpa [List.foldr, acc] using hWalk
              | inr hInRest =>
                  -- `mv ∈ acc` by IH, then by accumulator monotonicity it remains in the head `walk`.
                  cases d with
                  | mk df0 dr0 =>
                      let acc :=
                        rest.foldr
                          (fun d acc =>
                            let (df1, dr1) := d
                            Rules.slidingTargets.walk m.fromSq m.piece gs.board m.piece.color 7 df1 dr1 7 acc)
                          []
                      have hAcc : mv ∈ acc := by
                        simpa [acc] using ih hInRest
                      have hHead :
                          mv ∈ Rules.slidingTargets.walk m.fromSq m.piece gs.board m.piece.color 7 df0 dr0 7 acc :=
                        slidingTargets_walk_acc_subset m.fromSq m.piece gs.board m.piece.color 7 df0 dr0 7 acc
                          (m := mv) hAcc
                      simpa [List.foldr, acc] using hHead
        -- Apply the general fold lemma to the fixed rook delta list.
        simpa using this [(1, 0), (-1, 0), (0, 1), (0, -1)] hDeltaMem

      simpa [hEqMove, mv] using hMemSliding
  | some p =>
      have hAt' : gs.board m.toSq = some p := by simpa using hAt
      have hCap : m.isCapture = true :=
        capture_eq_true_of_target_enemy gs m p hSem0 hAt' hDest hEP
      have hEqMove :
          ({ piece := m.piece, fromSq := m.fromSq, toSq := m.toSq, isCapture := true } : Move) = m :=
        move_eq_record_of_fields m true hCap hPromo hCastle hRookNone.1 hRookNone.2 hEP
      -- `destinationFriendlyFree` implies the piece at the target is an enemy non-king.
      have hEnemyTgt : Rules.isEnemyNonKingAt gs.board m.piece.color m.toSq = true := by
        unfold destinationFriendlyFreeProp destinationFriendlyFree at hDest
        have hBoth : p.color ≠ m.piece.color ∧ p.pieceType ≠ PieceType.King := by
          have : decide (p.color ≠ m.piece.color ∧ p.pieceType ≠ PieceType.King) = true := by
            simpa [hAt'] using hDest
          simpa [decide_eq_true_eq] using this
        simp [Rules.isEnemyNonKingAt, hAt', hBoth.1, hBoth.2]
      let mv : Move := { piece := m.piece, fromSq := m.fromSq, toSq := m.toSq, isCapture := true }
      have hMvDef : mv.piece = m.piece ∧ mv.fromSq = m.fromSq ∧ mv.toSq = m.toSq := by
        simp [mv]
      have hMvWalk :
          ∀ acc, mv ∈ Rules.slidingTargets.walk m.fromSq m.piece gs.board m.piece.color 7 df dr 7 acc := by
        let sTarget : Nat := 7 - k
        have hSqAtTarget :
            Movement.squareFromInts (m.fromSq.fileInt + df * Int.ofNat (7 - sTarget))
                (m.fromSq.rankInt + dr * Int.ofNat (7 - sTarget)) =
              some m.toSq := by
          have hTgt := Movement.squareFromInts_rookDelta_rookOffset m.fromSq m.toSq hMove
          simpa [sTarget, k, df, dr, Nat.sub_sub_self hkLe7] using hTgt
        have hEmptyFalse : Rules.isEmpty gs.board m.toSq = false := by
          simp [Rules.isEmpty, hAt']
        have hBase :
            ∀ acc,
              mv ∈ Rules.slidingTargets.walk m.fromSq m.piece gs.board m.piece.color 7 df dr (Nat.succ sTarget) acc := by
          intro acc
          exact
            Rules.slidingTargets_walk_mem_of_enemy_square m.fromSq m.piece gs.board m.piece.color 7 df dr sTarget acc
              m.toSq hSqAtTarget hEmptyFalse hEnemyTgt
        exact walk_mem_to_step7 mv (by simpa [sTarget] using hBase)
      have hMemSliding :
          mv ∈ Rules.slidingTargets gs m.fromSq m.piece [(1, 0), (-1, 0), (0, 1), (0, -1)] := by
        unfold Rules.slidingTargets
        have :
            ∀ (deltas : List (Int × Int)),
              Movement.rookDelta m.fromSq m.toSq ∈ deltas →
                mv ∈
                  List.foldr
                    (fun d acc =>
                      let (df0, dr0) := d
                      Rules.slidingTargets.walk m.fromSq m.piece gs.board m.piece.color 7 df0 dr0 7 acc)
                    [] deltas := by
          intro deltas hIn
          induction deltas with
          | nil =>
              cases (show False by simpa using hIn)
          | cons d rest ih =>
              have hSplit :
                  Movement.rookDelta m.fromSq m.toSq = d ∨ Movement.rookDelta m.fromSq m.toSq ∈ rest := by
                simpa [List.mem_cons] using hIn
              cases hSplit with
              | inl hEq =>
                  cases d with
                  | mk df0 dr0 =>
                      have hdf : df0 = df := by
                        simpa [df] using (congrArg Prod.fst hEq).symm
                      have hdr : dr0 = dr := by
                        simpa [dr] using (congrArg Prod.snd hEq).symm
                      let acc :=
                        rest.foldr
                          (fun d acc =>
                            let (df1, dr1) := d
                            Rules.slidingTargets.walk m.fromSq m.piece gs.board m.piece.color 7 df1 dr1 7 acc)
                          []
                      have hWalk :
                          mv ∈ Rules.slidingTargets.walk m.fromSq m.piece gs.board m.piece.color 7 df0 dr0 7 acc := by
                        simpa [hdf, hdr, acc] using hMvWalk acc
                      simpa [List.foldr, acc] using hWalk
              | inr hInRest =>
                  cases d with
                  | mk df0 dr0 =>
                      let acc :=
                        rest.foldr
                          (fun d acc =>
                            let (df1, dr1) := d
                            Rules.slidingTargets.walk m.fromSq m.piece gs.board m.piece.color 7 df1 dr1 7 acc)
                          []
                      have hAcc : mv ∈ acc := by
                        simpa [acc] using ih hInRest
                      have hHead :
                          mv ∈ Rules.slidingTargets.walk m.fromSq m.piece gs.board m.piece.color 7 df0 dr0 7 acc :=
                        slidingTargets_walk_acc_subset m.fromSq m.piece gs.board m.piece.color 7 df0 dr0 7 acc
                          (m := mv) hAcc
                      simpa [List.foldr, acc] using hHead
        simpa using this [(1, 0), (-1, 0), (0, 1), (0, -1)] hDeltaMem
      simpa [hEqMove, mv] using hMemSliding

theorem fideLegalSemantic_implies_mem_pieceTargets_bishop (gs : GameState) (m : Move) :
    fideLegalSemantic gs m →
    m.piece.pieceType = PieceType.Bishop →
    m ∈ pieceTargets gs m.fromSq m.piece := by
  intro hSem hBishop
  have hSem0 := hSem
  rcases hSem with
    ⟨_hTurn, _hFrom, hGeom, hDest, _hCapSpec, _hNotCheck, _hPromoFwd, _hPromoBack, _hCastleClause,
      _hEPFlag, _hCastleFlag, hRookFields⟩
  have hNotPawn : m.piece.pieceType ≠ PieceType.Pawn := by
    intro hPawn
    simpa [hPawn] using hBishop
  have hNotKing : m.piece.pieceType ≠ PieceType.King := by
    intro hKing
    simpa [hKing] using hBishop
  have hEP : m.isEnPassant = false := isEnPassant_eq_false_of_not_pawn gs m hSem0 hNotPawn
  have hCastle : m.isCastle = false := isCastle_eq_false_of_not_king gs m hSem0 hNotKing
  have hPromo : m.promotion = none := promotion_eq_none_of_not_pawn gs m hSem0 hNotPawn
  have hRookNone : m.castleRookFrom = none ∧ m.castleRookTo = none := by
    have : ¬m.isCastle := by simp [hCastle]
    exact hRookFields this

  have hGeom' : Movement.isDiagonal m.fromSq m.toSq ∧ Rules.pathClear gs.board m.fromSq m.toSq := by
    simpa [respectsGeometry, hBishop] using hGeom
  have hMove : Movement.isDiagonal m.fromSq m.toSq := hGeom'.1
  have hPathClear : Rules.pathClear gs.board m.fromSq m.toSq = true := by simpa using hGeom'.2
  have hBetweenEmpty :
      ∀ sq, sq ∈ Movement.squaresBetween m.fromSq m.toSq → gs.board sq = none := by
    exact (Rules.pathClear_eq_true_iff gs.board m.fromSq m.toSq).1 hPathClear

  let k : Nat := Movement.bishopOffset m.fromSq m.toSq
  have hkLe7 : k ≤ 7 := by
    simpa [k, Movement.bishopOffset] using (Chess.Movement.fileDiff_natAbs_le_7 m.fromSq m.toSq)
  have hkPos : 0 < k := by
    have hFdNe : Movement.fileDiff m.fromSq m.toSq ≠ 0 := by
      intro hFd0
      have hAbs0 : Movement.absInt (Movement.rankDiff m.fromSq m.toSq) = 0 := by
        simpa [hFd0, Movement.absInt] using (Eq.symm hMove.2)
      have hRd0 : Movement.rankDiff m.fromSq m.toSq = 0 := by
        by_cases hNonneg : 0 ≤ Movement.rankDiff m.fromSq m.toSq
        · simpa [Movement.absInt, hNonneg] using hAbs0
        ·
          have : -Movement.rankDiff m.fromSq m.toSq = 0 := by
            simpa [Movement.absInt, hNonneg] using hAbs0
          omega
      have hFileEq : m.toSq.fileInt = m.fromSq.fileInt := by
        unfold Movement.fileDiff at hFd0
        omega
      have hRankEq : m.toSq.rankInt = m.fromSq.rankInt := by
        unfold Movement.rankDiff at hRd0
        omega
      have hEq : m.fromSq = m.toSq := by
        have hFileNatEq : m.toSq.fileNat = m.fromSq.fileNat := by
          have : Int.ofNat m.toSq.fileNat = Int.ofNat m.fromSq.fileNat := by
            simpa [Square.fileInt] using hFileEq
          exact Int.ofNat.inj this
        have hRankNatEq : m.toSq.rankNat = m.fromSq.rankNat := by
          have : Int.ofNat m.toSq.rankNat = Int.ofNat m.fromSq.rankNat := by
            simpa [Square.rankInt] using hRankEq
          exact Int.ofNat.inj this
        cases hFromSq : m.fromSq with
        | mk srcFile srcRank =>
            cases hToSq : m.toSq with
            | mk tgtFile tgtRank =>
                have hFileVal : tgtFile.val = srcFile.val := by
                  have : File.toNat tgtFile = File.toNat srcFile := by
                    simpa [Square.fileNat, hFromSq, hToSq] using hFileNatEq
                  simpa [File.toNat] using this
                have hRankVal : tgtRank.val = srcRank.val := by
                  have : Rank.toNat tgtRank = Rank.toNat srcRank := by
                    simpa [Square.rankNat, hFromSq, hToSq] using hRankNatEq
                  simpa [Rank.toNat] using this
                have hFile : srcFile = tgtFile := Fin.ext (by simpa using hFileVal.symm)
                have hRank : srcRank = tgtRank := Fin.ext (by simpa using hRankVal.symm)
                have hSqEq :
                    ({ file := srcFile, rank := srcRank } : Square) =
                      { file := tgtFile, rank := tgtRank } := by
                  cases hFile
                  cases hRank
                  rfl
                exact hSqEq
      exact hMove.1 hEq
    have : 0 < (Movement.fileDiff m.fromSq m.toSq).natAbs := (Int.natAbs_pos).2 hFdNe
    simpa [k, Movement.bishopOffset] using this

  let df : Int := (Movement.bishopDelta m.fromSq m.toSq).1
  let dr : Int := (Movement.bishopDelta m.fromSq m.toSq).2
  have hDeltaMem :
      Movement.bishopDelta m.fromSq m.toSq ∈ [(1, 1), (-1, -1), (1, -1), (-1, 1)] :=
    Chess.Movement.bishopDelta_mem_bishopDeltas m.fromSq m.toSq hMove

  have hEmptyIntermediate :
      ∀ t, 1 ≤ t → t < k →
        ∀ sq,
          Movement.squareFromInts (m.fromSq.fileInt + df * (t : Int))
              (m.fromSq.rankInt + dr * (t : Int)) =
            some sq →
          Rules.isEmpty gs.board sq = true := by
    intro t ht1 htLt sq hSq
    have hSq' :
        Movement.squareFromInts
            (m.fromSq.fileInt + (Movement.bishopDelta m.fromSq m.toSq).1 * (t : Int))
            (m.fromSq.rankInt + (Movement.bishopDelta m.fromSq m.toSq).2 * (t : Int)) =
          some sq := by
      simpa [df, dr] using hSq
    have hMemBetween :
        sq ∈ Movement.squaresBetween m.fromSq m.toSq :=
      Chess.Movement.bishop_step_square_mem_squaresBetween m.fromSq m.toSq hMove t ht1 (by simpa [k] using htLt) sq hSq'
    have hEmpty : gs.board sq = none := hBetweenEmpty sq hMemBetween
    simpa [Rules.isEmpty] using hEmpty

  have walk_mem_to_step7 (mv : Move)
      (hBase : ∀ acc,
        mv ∈ Rules.slidingTargets.walk m.fromSq m.piece gs.board m.piece.color 7 df dr (7 - k).succ acc) :
      ∀ acc, mv ∈ Rules.slidingTargets.walk m.fromSq m.piece gs.board m.piece.color 7 df dr 7 acc := by
    intro acc
    let sTarget : Nat := 7 - k
    let stepTarget : Nat := sTarget.succ
    have hsTargetLe6 : sTarget ≤ 6 := by
      have hk1 : 1 ≤ k := Nat.succ_le_of_lt hkPos
      have : 7 - k ≤ 7 - 1 := Nat.sub_le_sub_left hk1 7
      simpa [sTarget] using this
    have hStepTargetLe7 : stepTarget ≤ 7 := by
      simpa [stepTarget] using (Nat.succ_le_succ hsTargetLe6)
    have hOff : 7 - sTarget = k := by
      simpa [sTarget] using (Nat.sub_sub_self hkLe7)
    let dFinal : Nat := 7 - stepTarget
    have hLift :
        ∀ d, d ≤ dFinal →
          ∀ acc,
            mv ∈
              Rules.slidingTargets.walk m.fromSq m.piece gs.board m.piece.color 7 df dr (stepTarget + d) acc := by
      intro d hd
      induction d with
      | zero =>
          intro acc
          simpa [stepTarget, sTarget] using hBase acc
      | succ d ih =>
          intro acc
          have hd' : d ≤ dFinal := Nat.le_trans (Nat.le_of_lt (Nat.lt_succ_self d)) hd
          let pred : Nat := stepTarget + d
          have hPredLe6 : pred ≤ 6 := by
            have hStepLe7 : stepTarget + d.succ ≤ 7 := by
              have h1 : stepTarget + d.succ ≤ stepTarget + (7 - stepTarget) := Nat.add_le_add_left hd stepTarget
              simpa [Nat.add_sub_of_le hStepTargetLe7] using h1
            have : pred + 1 ≤ 7 := by
              simpa [pred, Nat.succ_eq_add_one, Nat.add_assoc] using hStepLe7
            omega
          let t : Nat := 7 - pred
          have ht1 : 1 ≤ t := by
            have hPredLt7 : pred < 7 := Nat.lt_succ_of_le hPredLe6
            have htPos : 0 < 7 - pred := Nat.sub_pos_of_lt hPredLt7
            simpa [t] using (Nat.succ_le_of_lt htPos)
          have htLt : t < k := by
            have hsTargetLt7 : sTarget < 7 := by
              have : 7 - k < 7 := Nat.sub_lt (by decide : 0 < 7) hkPos
              simpa [sTarget] using this
            have hsTargetLtPred : sTarget < pred := by
              have hsTargetLtStep : sTarget < stepTarget := by
                simpa [stepTarget] using (Nat.lt_succ_self sTarget)
              have hStepLePred : stepTarget ≤ pred := Nat.le_add_right stepTarget d
              exact Nat.lt_of_lt_of_le hsTargetLtStep hStepLePred
            have : 7 - pred < 7 - sTarget := Nat.sub_lt_sub_left hsTargetLt7 hsTargetLtPred
            simpa [t, hOff] using this
          have htLe : t ≤ k := Nat.le_of_lt htLt
          rcases Chess.Movement.squareFromInts_bishopDelta_step_some m.fromSq m.toSq hMove t (by
              simpa [k] using htLe) with ⟨sq, hSq⟩
          have hSqW :
              Movement.squareFromInts (m.fromSq.fileInt + df * (t : Int))
                  (m.fromSq.rankInt + dr * (t : Int)) =
                some sq := by
            simpa [df, dr] using hSq
          have hEmptySq : Rules.isEmpty gs.board sq = true := by
            exact hEmptyIntermediate t ht1 (by simpa [k] using htLt) sq (by simpa using hSqW)
          have hRec :
              mv ∈ Rules.slidingTargets.walk m.fromSq m.piece gs.board m.piece.color 7 df dr pred
                ({ piece := m.piece, fromSq := m.fromSq, toSq := sq } :: acc) :=
            ih hd' ({ piece := m.piece, fromSq := m.fromSq, toSq := sq } :: acc)
          have hStep : stepTarget + d.succ = Nat.succ pred := by
            simp [pred, stepTarget, Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          have hSqWalk :
              Movement.squareFromInts (m.fromSq.fileInt + df * (↑(7 - pred) : Int))
                  (m.fromSq.rankInt + dr * (↑(7 - pred) : Int)) =
                some sq := by
            simpa [t] using hSqW
          rw [hStep]
          simp [Rules.slidingTargets.walk]
          rw [hSqWalk]
          simp [hEmptySq]
          exact hRec
    have hEq : stepTarget + dFinal = 7 := Nat.add_sub_of_le hStepTargetLe7
    have hMem : mv ∈ Rules.slidingTargets.walk m.fromSq m.piece gs.board m.piece.color 7 df dr (stepTarget + dFinal) acc :=
      hLift dFinal (Nat.le_refl _) acc
    simpa [hEq, dFinal] using hMem

  unfold pieceTargets
  simp [hBishop]
  cases hAt : gs.board.get m.toSq with
  | none =>
      have hAt' : gs.board m.toSq = none := by simpa using hAt
      have hCap : m.isCapture = false := capture_eq_of_target_empty gs m hSem0 hEP hAt'
      have hEqMove :
          ({ piece := m.piece, fromSq := m.fromSq, toSq := m.toSq, isCapture := false } : Move) = m :=
        move_eq_record_of_fields m false hCap hPromo hCastle hRookNone.1 hRookNone.2 hEP
      have hEmptyTgt : Rules.isEmpty gs.board m.toSq = true := by simpa [Rules.isEmpty] using hAt'
      let mv : Move := { piece := m.piece, fromSq := m.fromSq, toSq := m.toSq }
      have hMvWalk :
          ∀ acc, mv ∈ Rules.slidingTargets.walk m.fromSq m.piece gs.board m.piece.color 7 df dr 7 acc := by
        let sTarget : Nat := 7 - k
        have hSqAtTarget :
            Movement.squareFromInts (m.fromSq.fileInt + df * Int.ofNat (7 - sTarget))
                (m.fromSq.rankInt + dr * Int.ofNat (7 - sTarget)) =
              some m.toSq := by
          have hTgt := Movement.squareFromInts_bishopDelta_bishopOffset m.fromSq m.toSq hMove
          simpa [sTarget, k, df, dr, Nat.sub_sub_self hkLe7] using hTgt
        have hBase :
            ∀ acc,
              mv ∈ Rules.slidingTargets.walk m.fromSq m.piece gs.board m.piece.color 7 df dr (Nat.succ sTarget) acc := by
          intro acc
          exact
            Rules.slidingTargets_walk_mem_of_empty_square m.fromSq m.piece gs.board m.piece.color 7 df dr sTarget acc
              m.toSq hSqAtTarget hEmptyTgt
        exact walk_mem_to_step7 mv (by simpa [sTarget] using hBase)
      have hMemSliding :
          mv ∈ Rules.slidingTargets gs m.fromSq m.piece [(1, 1), (-1, -1), (1, -1), (-1, 1)] := by
        unfold Rules.slidingTargets
        have :
            ∀ (deltas : List (Int × Int)),
              Movement.bishopDelta m.fromSq m.toSq ∈ deltas →
                mv ∈
                  List.foldr
                    (fun d acc =>
                      let (df0, dr0) := d
                      Rules.slidingTargets.walk m.fromSq m.piece gs.board m.piece.color 7 df0 dr0 7 acc)
                    [] deltas := by
          intro deltas hIn
          induction deltas with
          | nil =>
              cases (show False by simpa using hIn)
          | cons d rest ih =>
              have hSplit :
                  Movement.bishopDelta m.fromSq m.toSq = d ∨ Movement.bishopDelta m.fromSq m.toSq ∈ rest := by
                simpa [List.mem_cons] using hIn
              cases hSplit with
              | inl hEq =>
                  cases d with
                  | mk df0 dr0 =>
                      have hdf : df0 = df := by
                        simpa [df] using (congrArg Prod.fst hEq).symm
                      have hdr : dr0 = dr := by
                        simpa [dr] using (congrArg Prod.snd hEq).symm
                      let acc :=
                        rest.foldr
                          (fun d acc =>
                            let (df1, dr1) := d
                            Rules.slidingTargets.walk m.fromSq m.piece gs.board m.piece.color 7 df1 dr1 7 acc)
                          []
                      have hWalk :
                          mv ∈ Rules.slidingTargets.walk m.fromSq m.piece gs.board m.piece.color 7 df0 dr0 7 acc := by
                        simpa [hdf, hdr, acc] using hMvWalk acc
                      simpa [List.foldr, acc] using hWalk
              | inr hInRest =>
                  cases d with
                  | mk df0 dr0 =>
                      let acc :=
                        rest.foldr
                          (fun d acc =>
                            let (df1, dr1) := d
                            Rules.slidingTargets.walk m.fromSq m.piece gs.board m.piece.color 7 df1 dr1 7 acc)
                          []
                      have hAcc : mv ∈ acc := by
                        simpa [acc] using ih hInRest
                      have hHead :
                          mv ∈ Rules.slidingTargets.walk m.fromSq m.piece gs.board m.piece.color 7 df0 dr0 7 acc :=
                        slidingTargets_walk_acc_subset m.fromSq m.piece gs.board m.piece.color 7 df0 dr0 7 acc
                          (m := mv) hAcc
                      simpa [List.foldr, acc] using hHead
        simpa using this [(1, 1), (-1, -1), (1, -1), (-1, 1)] hDeltaMem
      simpa [hEqMove, mv] using hMemSliding
  | some p =>
      have hAt' : gs.board m.toSq = some p := by simpa using hAt
      have hCap : m.isCapture = true :=
        capture_eq_true_of_target_enemy gs m p hSem0 hAt' hDest hEP
      have hEqMove :
          ({ piece := m.piece, fromSq := m.fromSq, toSq := m.toSq, isCapture := true } : Move) = m :=
        move_eq_record_of_fields m true hCap hPromo hCastle hRookNone.1 hRookNone.2 hEP
      have hEnemyTgt : Rules.isEnemyNonKingAt gs.board m.piece.color m.toSq = true := by
        unfold destinationFriendlyFreeProp destinationFriendlyFree at hDest
        have hBoth : p.color ≠ m.piece.color ∧ p.pieceType ≠ PieceType.King := by
          have : decide (p.color ≠ m.piece.color ∧ p.pieceType ≠ PieceType.King) = true := by
            simpa [hAt'] using hDest
          simpa [decide_eq_true_eq] using this
        simp [Rules.isEnemyNonKingAt, hAt', hBoth.1, hBoth.2]
      let mv : Move := { piece := m.piece, fromSq := m.fromSq, toSq := m.toSq, isCapture := true }
      have hMvWalk :
          ∀ acc, mv ∈ Rules.slidingTargets.walk m.fromSq m.piece gs.board m.piece.color 7 df dr 7 acc := by
        let sTarget : Nat := 7 - k
        have hSqAtTarget :
            Movement.squareFromInts (m.fromSq.fileInt + df * Int.ofNat (7 - sTarget))
                (m.fromSq.rankInt + dr * Int.ofNat (7 - sTarget)) =
              some m.toSq := by
          have hTgt := Movement.squareFromInts_bishopDelta_bishopOffset m.fromSq m.toSq hMove
          simpa [sTarget, k, df, dr, Nat.sub_sub_self hkLe7] using hTgt
        have hEmptyFalse : Rules.isEmpty gs.board m.toSq = false := by
          simp [Rules.isEmpty, hAt']
        have hBase :
            ∀ acc,
              mv ∈ Rules.slidingTargets.walk m.fromSq m.piece gs.board m.piece.color 7 df dr (Nat.succ sTarget) acc := by
          intro acc
          exact
            Rules.slidingTargets_walk_mem_of_enemy_square m.fromSq m.piece gs.board m.piece.color 7 df dr sTarget acc
              m.toSq hSqAtTarget hEmptyFalse hEnemyTgt
        exact walk_mem_to_step7 mv (by simpa [sTarget] using hBase)
      have hMemSliding :
          mv ∈ Rules.slidingTargets gs m.fromSq m.piece [(1, 1), (-1, -1), (1, -1), (-1, 1)] := by
        unfold Rules.slidingTargets
        have :
            ∀ (deltas : List (Int × Int)),
              Movement.bishopDelta m.fromSq m.toSq ∈ deltas →
                mv ∈
                  List.foldr
                    (fun d acc =>
                      let (df0, dr0) := d
                      Rules.slidingTargets.walk m.fromSq m.piece gs.board m.piece.color 7 df0 dr0 7 acc)
                    [] deltas := by
          intro deltas hIn
          induction deltas with
          | nil =>
              cases (show False by simpa using hIn)
          | cons d rest ih =>
              have hSplit :
                  Movement.bishopDelta m.fromSq m.toSq = d ∨ Movement.bishopDelta m.fromSq m.toSq ∈ rest := by
                simpa [List.mem_cons] using hIn
              cases hSplit with
              | inl hEq =>
                  cases d with
                  | mk df0 dr0 =>
                      have hdf : df0 = df := by
                        simpa [df] using (congrArg Prod.fst hEq).symm
                      have hdr : dr0 = dr := by
                        simpa [dr] using (congrArg Prod.snd hEq).symm
                      let acc :=
                        rest.foldr
                          (fun d acc =>
                            let (df1, dr1) := d
                            Rules.slidingTargets.walk m.fromSq m.piece gs.board m.piece.color 7 df1 dr1 7 acc)
                          []
                      have hWalk :
                          mv ∈ Rules.slidingTargets.walk m.fromSq m.piece gs.board m.piece.color 7 df0 dr0 7 acc := by
                        simpa [hdf, hdr, acc] using hMvWalk acc
                      simpa [List.foldr, acc] using hWalk
              | inr hInRest =>
                  cases d with
                  | mk df0 dr0 =>
                      let acc :=
                        rest.foldr
                          (fun d acc =>
                            let (df1, dr1) := d
                            Rules.slidingTargets.walk m.fromSq m.piece gs.board m.piece.color 7 df1 dr1 7 acc)
                          []
                      have hAcc : mv ∈ acc := by
                        simpa [acc] using ih hInRest
                      have hHead :
                          mv ∈ Rules.slidingTargets.walk m.fromSq m.piece gs.board m.piece.color 7 df0 dr0 7 acc :=
                        slidingTargets_walk_acc_subset m.fromSq m.piece gs.board m.piece.color 7 df0 dr0 7 acc
                          (m := mv) hAcc
                      simpa [List.foldr, acc] using hHead
        simpa using this [(1, 1), (-1, -1), (1, -1), (-1, 1)] hDeltaMem
      simpa [hEqMove, mv] using hMemSliding

theorem fideLegalSemantic_implies_mem_pieceTargets_queen (gs : GameState) (m : Move) :
    fideLegalSemantic gs m →
    m.piece.pieceType = PieceType.Queen →
    m ∈ pieceTargets gs m.fromSq m.piece := by
  intro hSem hQueen
  have hSem0 := hSem
  rcases hSem with
    ⟨_hTurn, _hFrom, hGeom, hDest, _hCapSpec, _hNotCheck, _hPromoFwd, _hPromoBack, _hCastleClause,
      _hEPFlag, _hCastleFlag, hRookFields⟩
  have hNotPawn : m.piece.pieceType ≠ PieceType.Pawn := by
    intro hPawn
    simpa [hPawn] using hQueen
  have hNotKing : m.piece.pieceType ≠ PieceType.King := by
    intro hKing
    simpa [hKing] using hQueen
  have hEP : m.isEnPassant = false := isEnPassant_eq_false_of_not_pawn gs m hSem0 hNotPawn
  have hCastle : m.isCastle = false := isCastle_eq_false_of_not_king gs m hSem0 hNotKing
  have hPromo : m.promotion = none := promotion_eq_none_of_not_pawn gs m hSem0 hNotPawn
  have hRookNone : m.castleRookFrom = none ∧ m.castleRookTo = none := by
    have : ¬m.isCastle := by simp [hCastle]
    exact hRookFields this

  have hGeom' : Movement.isQueenMove m.fromSq m.toSq ∧ Rules.pathClear gs.board m.fromSq m.toSq := by
    simpa [respectsGeometry, hQueen] using hGeom
  have hPathClear : Rules.pathClear gs.board m.fromSq m.toSq = true := by simpa using hGeom'.2
  have hBetweenEmpty :
      ∀ sq, sq ∈ Movement.squaresBetween m.fromSq m.toSq → gs.board sq = none := by
    exact (Rules.pathClear_eq_true_iff gs.board m.fromSq m.toSq).1 hPathClear

  let rookDeltas : List (Int × Int) := [(1, 0), (-1, 0), (0, 1), (0, -1)]
  let bishopDeltas : List (Int × Int) := [(1, 1), (-1, -1), (1, -1), (-1, 1)]
  let queenDeltas : List (Int × Int) := rookDeltas ++ bishopDeltas

  -- Reduce to the queen branch of `pieceTargets`.
  unfold pieceTargets
  simp [hQueen, rookDeltas, bishopDeltas, queenDeltas]

  -- Split queen geometry into rook-like vs diagonal.
  cases hGeom'.1 with
  | inl hRookMove =>
      -- Rook-like queen move.
      have hMove : Movement.isRookMove m.fromSq m.toSq := hRookMove

      let k : Nat := Movement.rookOffset m.fromSq m.toSq
      have hkLe7 : k ≤ 7 := by
        simpa [k] using (Chess.Movement.rookOffset_le_7 m.fromSq m.toSq hMove)
      have hkPos : 0 < k := by
        cases hMove.2 with
        | inl h =>
            have hrdNe : Movement.rankDiff m.fromSq m.toSq ≠ 0 := h.2
            have : 0 < (Movement.rankDiff m.fromSq m.toSq).natAbs := (Int.natAbs_pos).2 hrdNe
            simpa [k, Movement.rookOffset, h.1] using this
        | inr h =>
            have hfdNe : Movement.fileDiff m.fromSq m.toSq ≠ 0 := h.2
            have : 0 < (Movement.fileDiff m.fromSq m.toSq).natAbs := (Int.natAbs_pos).2 hfdNe
            simpa [k, Movement.rookOffset, h.1] using this

      let df : Int := (Movement.rookDelta m.fromSq m.toSq).1
      let dr : Int := (Movement.rookDelta m.fromSq m.toSq).2
      have hDeltaMemRook : Movement.rookDelta m.fromSq m.toSq ∈ rookDeltas :=
        Chess.Movement.rookDelta_mem_rookDeltas m.fromSq m.toSq hMove
      have hDeltaMemQ : Movement.rookDelta m.fromSq m.toSq ∈ queenDeltas := by
        -- `queenDeltas = rookDeltas ++ bishopDeltas`.
        have : Movement.rookDelta m.fromSq m.toSq ∈ rookDeltas := hDeltaMemRook
        exact List.mem_append_left bishopDeltas this

      have hEmptyIntermediate :
          ∀ t, 1 ≤ t → t < k →
            ∀ sq,
              Movement.squareFromInts (m.fromSq.fileInt + df * (t : Int))
                  (m.fromSq.rankInt + dr * (t : Int)) =
                some sq →
              Rules.isEmpty gs.board sq = true := by
        intro t ht1 htLt sq hSq
        have hSq' :
            Movement.squareFromInts (m.fromSq.fileInt + (Movement.rookDelta m.fromSq m.toSq).1 * (t : Int))
                (m.fromSq.rankInt + (Movement.rookDelta m.fromSq m.toSq).2 * (t : Int)) =
              some sq := by
          simpa [df, dr] using hSq
        have hMemBetween :
            sq ∈ Movement.squaresBetween m.fromSq m.toSq :=
          Chess.Movement.rook_step_square_mem_squaresBetween m.fromSq m.toSq hMove t ht1 (by simpa [k] using htLt) sq hSq'
        have hEmpty : gs.board sq = none := hBetweenEmpty sq hMemBetween
        simpa [Rules.isEmpty] using hEmpty

      have walk_mem_to_step7 (mv : Move)
          (hBase : ∀ acc,
            mv ∈ Rules.slidingTargets.walk m.fromSq m.piece gs.board m.piece.color 7 df dr (7 - k).succ acc) :
          ∀ acc, mv ∈ Rules.slidingTargets.walk m.fromSq m.piece gs.board m.piece.color 7 df dr 7 acc := by
        intro acc
        let sTarget : Nat := 7 - k
        let stepTarget : Nat := sTarget.succ
        have hsTargetLe6 : sTarget ≤ 6 := by
          have hk1 : 1 ≤ k := Nat.succ_le_of_lt hkPos
          have : 7 - k ≤ 7 - 1 := Nat.sub_le_sub_left hk1 7
          simpa [sTarget] using this
        have hStepTargetLe7 : stepTarget ≤ 7 := by
          simpa [stepTarget] using (Nat.succ_le_succ hsTargetLe6)
        have hOff : 7 - sTarget = k := by
          simpa [sTarget] using (Nat.sub_sub_self hkLe7)
        let dFinal : Nat := 7 - stepTarget
        have hLift :
            ∀ d, d ≤ dFinal →
              ∀ acc,
                mv ∈
                  Rules.slidingTargets.walk m.fromSq m.piece gs.board m.piece.color 7 df dr (stepTarget + d) acc := by
          intro d hd
          induction d with
          | zero =>
              intro acc
              simpa [stepTarget, sTarget] using hBase acc
          | succ d ih =>
              intro acc
              have hd' : d ≤ dFinal := Nat.le_trans (Nat.le_of_lt (Nat.lt_succ_self d)) hd
              let pred : Nat := stepTarget + d
              have hPredLe6 : pred ≤ 6 := by
                have hStepLe7 : stepTarget + d.succ ≤ 7 := by
                  have h1 : stepTarget + d.succ ≤ stepTarget + (7 - stepTarget) := Nat.add_le_add_left hd stepTarget
                  simpa [Nat.add_sub_of_le hStepTargetLe7] using h1
                have : pred + 1 ≤ 7 := by
                  simpa [pred, Nat.succ_eq_add_one, Nat.add_assoc] using hStepLe7
                omega
              let t : Nat := 7 - pred
              have ht1 : 1 ≤ t := by
                have hPredLt7 : pred < 7 := Nat.lt_succ_of_le hPredLe6
                have htPos : 0 < 7 - pred := Nat.sub_pos_of_lt hPredLt7
                simpa [t] using (Nat.succ_le_of_lt htPos)
              have htLt : t < k := by
                have hsTargetLt7 : sTarget < 7 := by
                  have : 7 - k < 7 := Nat.sub_lt (by decide : 0 < 7) hkPos
                  simpa [sTarget] using this
                have hsTargetLtPred : sTarget < pred := by
                  have hsTargetLtStep : sTarget < stepTarget := by
                    simpa [stepTarget] using (Nat.lt_succ_self sTarget)
                  have hStepLePred : stepTarget ≤ pred := Nat.le_add_right stepTarget d
                  exact Nat.lt_of_lt_of_le hsTargetLtStep hStepLePred
                have : 7 - pred < 7 - sTarget := Nat.sub_lt_sub_left hsTargetLt7 hsTargetLtPred
                simpa [t, hOff] using this
              have htLe : t ≤ k := Nat.le_of_lt htLt
              rcases Chess.Movement.squareFromInts_rookDelta_step_some m.fromSq m.toSq hMove t (by
                  simpa [k] using htLe) with ⟨sq, hSq⟩
              have hSqW :
                  Movement.squareFromInts (m.fromSq.fileInt + df * (t : Int))
                      (m.fromSq.rankInt + dr * (t : Int)) =
                    some sq := by
                simpa [df, dr] using hSq
              have hEmptySq : Rules.isEmpty gs.board sq = true := by
                exact hEmptyIntermediate t ht1 (by simpa [k] using htLt) sq (by simpa using hSqW)
              have hRec :
                  mv ∈ Rules.slidingTargets.walk m.fromSq m.piece gs.board m.piece.color 7 df dr pred
                    ({ piece := m.piece, fromSq := m.fromSq, toSq := sq } :: acc) :=
                ih hd' ({ piece := m.piece, fromSq := m.fromSq, toSq := sq } :: acc)
              have hStep : stepTarget + d.succ = Nat.succ pred := by
                simp [pred, stepTarget, Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
              have hSqWalk :
                  Movement.squareFromInts (m.fromSq.fileInt + df * (↑(7 - pred) : Int))
                      (m.fromSq.rankInt + dr * (↑(7 - pred) : Int)) =
                    some sq := by
                simpa [t] using hSqW
              rw [hStep]
              simp [Rules.slidingTargets.walk]
              rw [hSqWalk]
              simp [hEmptySq]
              exact hRec
        have hEq : stepTarget + dFinal = 7 := Nat.add_sub_of_le hStepTargetLe7
        have hMem : mv ∈ Rules.slidingTargets.walk m.fromSq m.piece gs.board m.piece.color 7 df dr (stepTarget + dFinal) acc :=
          hLift dFinal (Nat.le_refl _) acc
        simpa [hEq, dFinal] using hMem

      -- Analyze destination occupancy to choose the concrete move record.
      cases hAt : gs.board.get m.toSq with
      | none =>
          have hAt' : gs.board m.toSq = none := by simpa using hAt
          have hCap : m.isCapture = false := capture_eq_of_target_empty gs m hSem0 hEP hAt'
          have hEqMove :
              ({ piece := m.piece, fromSq := m.fromSq, toSq := m.toSq, isCapture := false } : Move) = m :=
            move_eq_record_of_fields m false hCap hPromo hCastle hRookNone.1 hRookNone.2 hEP
          have hEmptyTgt : Rules.isEmpty gs.board m.toSq = true := by simpa [Rules.isEmpty] using hAt'
          let mv : Move := { piece := m.piece, fromSq := m.fromSq, toSq := m.toSq }
          have hMvWalk :
              ∀ acc, mv ∈ Rules.slidingTargets.walk m.fromSq m.piece gs.board m.piece.color 7 df dr 7 acc := by
            let sTarget : Nat := 7 - k
            have hSqAtTarget :
                Movement.squareFromInts (m.fromSq.fileInt + df * Int.ofNat (7 - sTarget))
                    (m.fromSq.rankInt + dr * Int.ofNat (7 - sTarget)) =
                  some m.toSq := by
              have hTgt := Movement.squareFromInts_rookDelta_rookOffset m.fromSq m.toSq hMove
              simpa [sTarget, k, df, dr, Nat.sub_sub_self hkLe7] using hTgt
            have hBase :
                ∀ acc,
                  mv ∈ Rules.slidingTargets.walk m.fromSq m.piece gs.board m.piece.color 7 df dr (Nat.succ sTarget) acc := by
              intro acc
              exact
                Rules.slidingTargets_walk_mem_of_empty_square m.fromSq m.piece gs.board m.piece.color 7 df dr sTarget acc
                  m.toSq hSqAtTarget hEmptyTgt
            exact walk_mem_to_step7 mv (by simpa [sTarget] using hBase)
          have hMemSliding :
              mv ∈ Rules.slidingTargets gs m.fromSq m.piece queenDeltas := by
            unfold Rules.slidingTargets
            have :
                ∀ (deltas : List (Int × Int)),
                  Movement.rookDelta m.fromSq m.toSq ∈ deltas →
                    mv ∈
                      List.foldr
                        (fun d acc =>
                          let (df0, dr0) := d
                          Rules.slidingTargets.walk m.fromSq m.piece gs.board m.piece.color 7 df0 dr0 7 acc)
                        [] deltas := by
              intro deltas hIn
              induction deltas with
              | nil =>
                  cases (show False by simpa using hIn)
              | cons d rest ih =>
                  have hSplit :
                      Movement.rookDelta m.fromSq m.toSq = d ∨ Movement.rookDelta m.fromSq m.toSq ∈ rest := by
                    simpa [List.mem_cons] using hIn
                  cases hSplit with
                  | inl hEq =>
                      cases d with
                      | mk df0 dr0 =>
                          have hdf : df0 = df := by
                            simpa [df] using (congrArg Prod.fst hEq).symm
                          have hdr : dr0 = dr := by
                            simpa [dr] using (congrArg Prod.snd hEq).symm
                          let acc :=
                            rest.foldr
                              (fun d acc =>
                                let (df1, dr1) := d
                                Rules.slidingTargets.walk m.fromSq m.piece gs.board m.piece.color 7 df1 dr1 7 acc)
                              []
                          have hWalk :
                              mv ∈ Rules.slidingTargets.walk m.fromSq m.piece gs.board m.piece.color 7 df0 dr0 7 acc := by
                            simpa [hdf, hdr, acc] using hMvWalk acc
                          simpa [List.foldr, acc] using hWalk
                  | inr hInRest =>
                      cases d with
                      | mk df0 dr0 =>
                          let acc :=
                            rest.foldr
                              (fun d acc =>
                                let (df1, dr1) := d
                                Rules.slidingTargets.walk m.fromSq m.piece gs.board m.piece.color 7 df1 dr1 7 acc)
                              []
                          have hAcc : mv ∈ acc := by
                            simpa [acc] using ih hInRest
                          have hHead :
                              mv ∈ Rules.slidingTargets.walk m.fromSq m.piece gs.board m.piece.color 7 df0 dr0 7 acc :=
                            slidingTargets_walk_acc_subset m.fromSq m.piece gs.board m.piece.color 7 df0 dr0 7 acc
                              (m := mv) hAcc
                          simpa [List.foldr, acc] using hHead
            simpa [queenDeltas] using this queenDeltas hDeltaMemQ
          simpa [hEqMove, mv] using hMemSliding
      | some p =>
          have hAt' : gs.board m.toSq = some p := by simpa using hAt
          have hCap : m.isCapture = true :=
            capture_eq_true_of_target_enemy gs m p hSem0 hAt' hDest hEP
          have hEqMove :
              ({ piece := m.piece, fromSq := m.fromSq, toSq := m.toSq, isCapture := true } : Move) = m :=
            move_eq_record_of_fields m true hCap hPromo hCastle hRookNone.1 hRookNone.2 hEP
          have hEnemyTgt : Rules.isEnemyNonKingAt gs.board m.piece.color m.toSq = true := by
            unfold destinationFriendlyFreeProp destinationFriendlyFree at hDest
            have hBoth : p.color ≠ m.piece.color ∧ p.pieceType ≠ PieceType.King := by
              have : decide (p.color ≠ m.piece.color ∧ p.pieceType ≠ PieceType.King) = true := by
                simpa [hAt'] using hDest
              simpa [decide_eq_true_eq] using this
            simp [Rules.isEnemyNonKingAt, hAt', hBoth.1, hBoth.2]
          let mv : Move := { piece := m.piece, fromSq := m.fromSq, toSq := m.toSq, isCapture := true }
          have hMvWalk :
              ∀ acc, mv ∈ Rules.slidingTargets.walk m.fromSq m.piece gs.board m.piece.color 7 df dr 7 acc := by
            let sTarget : Nat := 7 - k
            have hSqAtTarget :
                Movement.squareFromInts (m.fromSq.fileInt + df * Int.ofNat (7 - sTarget))
                    (m.fromSq.rankInt + dr * Int.ofNat (7 - sTarget)) =
                  some m.toSq := by
              have hTgt := Movement.squareFromInts_rookDelta_rookOffset m.fromSq m.toSq hMove
              simpa [sTarget, k, df, dr, Nat.sub_sub_self hkLe7] using hTgt
            have hEmptyFalse : Rules.isEmpty gs.board m.toSq = false := by
              simp [Rules.isEmpty, hAt']
            have hBase :
                ∀ acc,
                  mv ∈ Rules.slidingTargets.walk m.fromSq m.piece gs.board m.piece.color 7 df dr (Nat.succ sTarget) acc := by
              intro acc
              exact
                Rules.slidingTargets_walk_mem_of_enemy_square m.fromSq m.piece gs.board m.piece.color 7 df dr sTarget acc
                  m.toSq hSqAtTarget hEmptyFalse hEnemyTgt
            exact walk_mem_to_step7 mv (by simpa [sTarget] using hBase)
          have hMemSliding :
              mv ∈ Rules.slidingTargets gs m.fromSq m.piece queenDeltas := by
            unfold Rules.slidingTargets
            have :
                ∀ (deltas : List (Int × Int)),
                  Movement.rookDelta m.fromSq m.toSq ∈ deltas →
                    mv ∈
                      List.foldr
                        (fun d acc =>
                          let (df0, dr0) := d
                          Rules.slidingTargets.walk m.fromSq m.piece gs.board m.piece.color 7 df0 dr0 7 acc)
                        [] deltas := by
              intro deltas hIn
              induction deltas with
              | nil =>
                  cases (show False by simpa using hIn)
              | cons d rest ih =>
                  have hSplit :
                      Movement.rookDelta m.fromSq m.toSq = d ∨ Movement.rookDelta m.fromSq m.toSq ∈ rest := by
                    simpa [List.mem_cons] using hIn
                  cases hSplit with
                  | inl hEq =>
                      cases d with
                      | mk df0 dr0 =>
                          have hdf : df0 = df := by
                            simpa [df] using (congrArg Prod.fst hEq).symm
                          have hdr : dr0 = dr := by
                            simpa [dr] using (congrArg Prod.snd hEq).symm
                          let acc :=
                            rest.foldr
                              (fun d acc =>
                                let (df1, dr1) := d
                                Rules.slidingTargets.walk m.fromSq m.piece gs.board m.piece.color 7 df1 dr1 7 acc)
                              []
                          have hWalk :
                              mv ∈ Rules.slidingTargets.walk m.fromSq m.piece gs.board m.piece.color 7 df0 dr0 7 acc := by
                            simpa [hdf, hdr, acc] using hMvWalk acc
                          simpa [List.foldr, acc] using hWalk
                  | inr hInRest =>
                      cases d with
                      | mk df0 dr0 =>
                          let acc :=
                            rest.foldr
                              (fun d acc =>
                                let (df1, dr1) := d
                                Rules.slidingTargets.walk m.fromSq m.piece gs.board m.piece.color 7 df1 dr1 7 acc)
                              []
                          have hAcc : mv ∈ acc := by
                            simpa [acc] using ih hInRest
                          have hHead :
                              mv ∈ Rules.slidingTargets.walk m.fromSq m.piece gs.board m.piece.color 7 df0 dr0 7 acc :=
                            slidingTargets_walk_acc_subset m.fromSq m.piece gs.board m.piece.color 7 df0 dr0 7 acc
                              (m := mv) hAcc
                          simpa [List.foldr, acc] using hHead
            simpa [queenDeltas] using this queenDeltas hDeltaMemQ
          simpa [hEqMove, mv] using hMemSliding
  | inr hDiagMove =>
      -- Diagonal queen move: reuse bishop-style argument but fold into `queenDeltas` (right side of append).
      have hMove : Movement.isDiagonal m.fromSq m.toSq := hDiagMove

      let k : Nat := Movement.bishopOffset m.fromSq m.toSq
      have hkLe7 : k ≤ 7 := by
        simpa [k, Movement.bishopOffset] using (Chess.Movement.fileDiff_natAbs_le_7 m.fromSq m.toSq)
      have hkPos : 0 < k := by
        have hFdNe : Movement.fileDiff m.fromSq m.toSq ≠ 0 := by
          intro hFd0
          have hAbs0 : Movement.absInt (Movement.rankDiff m.fromSq m.toSq) = 0 := by
            simpa [hFd0, Movement.absInt] using (Eq.symm hMove.2)
          have hRd0 : Movement.rankDiff m.fromSq m.toSq = 0 := by
            by_cases hNonneg : 0 ≤ Movement.rankDiff m.fromSq m.toSq
            · simpa [Movement.absInt, hNonneg] using hAbs0
            ·
              have : -Movement.rankDiff m.fromSq m.toSq = 0 := by
                simpa [Movement.absInt, hNonneg] using hAbs0
              omega
          have hFileEq : m.toSq.fileInt = m.fromSq.fileInt := by
            unfold Movement.fileDiff at hFd0
            omega
          have hRankEq : m.toSq.rankInt = m.fromSq.rankInt := by
            unfold Movement.rankDiff at hRd0
            omega
          have hEq : m.fromSq = m.toSq := by
            have hFileNatEq : m.toSq.fileNat = m.fromSq.fileNat := by
              have : Int.ofNat m.toSq.fileNat = Int.ofNat m.fromSq.fileNat := by
                simpa [Square.fileInt] using hFileEq
              exact Int.ofNat.inj this
            have hRankNatEq : m.toSq.rankNat = m.fromSq.rankNat := by
              have : Int.ofNat m.toSq.rankNat = Int.ofNat m.fromSq.rankNat := by
                simpa [Square.rankInt] using hRankEq
              exact Int.ofNat.inj this
            cases hFromSq : m.fromSq with
            | mk srcFile srcRank =>
                cases hToSq : m.toSq with
                | mk tgtFile tgtRank =>
                    have hFileVal : tgtFile.val = srcFile.val := by
                      have : File.toNat tgtFile = File.toNat srcFile := by
                        simpa [Square.fileNat, hFromSq, hToSq] using hFileNatEq
                      simpa [File.toNat] using this
                    have hRankVal : tgtRank.val = srcRank.val := by
                      have : Rank.toNat tgtRank = Rank.toNat srcRank := by
                        simpa [Square.rankNat, hFromSq, hToSq] using hRankNatEq
                      simpa [Rank.toNat] using this
                    have hFile : srcFile = tgtFile := Fin.ext (by simpa using hFileVal.symm)
                    have hRank : srcRank = tgtRank := Fin.ext (by simpa using hRankVal.symm)
                    have hSqEq :
                        ({ file := srcFile, rank := srcRank } : Square) =
                          { file := tgtFile, rank := tgtRank } := by
                      cases hFile
                      cases hRank
                      rfl
                    exact hSqEq
          exact hMove.1 hEq
        have : 0 < (Movement.fileDiff m.fromSq m.toSq).natAbs := (Int.natAbs_pos).2 hFdNe
        simpa [k, Movement.bishopOffset] using this

      let df : Int := (Movement.bishopDelta m.fromSq m.toSq).1
      let dr : Int := (Movement.bishopDelta m.fromSq m.toSq).2
      have hDeltaMemB : Movement.bishopDelta m.fromSq m.toSq ∈ bishopDeltas :=
        Chess.Movement.bishopDelta_mem_bishopDeltas m.fromSq m.toSq hMove
      have hDeltaMemQ : Movement.bishopDelta m.fromSq m.toSq ∈ queenDeltas := by
        have : Movement.bishopDelta m.fromSq m.toSq ∈ bishopDeltas := hDeltaMemB
        exact List.mem_append_right rookDeltas this

      have hEmptyIntermediate :
          ∀ t, 1 ≤ t → t < k →
            ∀ sq,
              Movement.squareFromInts (m.fromSq.fileInt + df * (t : Int))
                  (m.fromSq.rankInt + dr * (t : Int)) =
                some sq →
              Rules.isEmpty gs.board sq = true := by
        intro t ht1 htLt sq hSq
        have hSq' :
            Movement.squareFromInts
                (m.fromSq.fileInt + (Movement.bishopDelta m.fromSq m.toSq).1 * (t : Int))
                (m.fromSq.rankInt + (Movement.bishopDelta m.fromSq m.toSq).2 * (t : Int)) =
              some sq := by
          simpa [df, dr] using hSq
        have hMemBetween :
            sq ∈ Movement.squaresBetween m.fromSq m.toSq :=
          Chess.Movement.bishop_step_square_mem_squaresBetween m.fromSq m.toSq hMove t ht1 (by simpa [k] using htLt) sq hSq'
        have hEmpty : gs.board sq = none := hBetweenEmpty sq hMemBetween
        simpa [Rules.isEmpty] using hEmpty

      have walk_mem_to_step7 (mv : Move)
          (hBase : ∀ acc,
            mv ∈ Rules.slidingTargets.walk m.fromSq m.piece gs.board m.piece.color 7 df dr (7 - k).succ acc) :
          ∀ acc, mv ∈ Rules.slidingTargets.walk m.fromSq m.piece gs.board m.piece.color 7 df dr 7 acc := by
        intro acc
        let sTarget : Nat := 7 - k
        let stepTarget : Nat := sTarget.succ
        have hsTargetLe6 : sTarget ≤ 6 := by
          have hk1 : 1 ≤ k := Nat.succ_le_of_lt hkPos
          have : 7 - k ≤ 7 - 1 := Nat.sub_le_sub_left hk1 7
          simpa [sTarget] using this
        have hStepTargetLe7 : stepTarget ≤ 7 := by
          simpa [stepTarget] using (Nat.succ_le_succ hsTargetLe6)
        have hOff : 7 - sTarget = k := by
          simpa [sTarget] using (Nat.sub_sub_self hkLe7)
        let dFinal : Nat := 7 - stepTarget
        have hLift :
            ∀ d, d ≤ dFinal →
              ∀ acc,
                mv ∈
                  Rules.slidingTargets.walk m.fromSq m.piece gs.board m.piece.color 7 df dr (stepTarget + d) acc := by
          intro d hd
          induction d with
          | zero =>
              intro acc
              simpa [stepTarget, sTarget] using hBase acc
          | succ d ih =>
              intro acc
              have hd' : d ≤ dFinal := Nat.le_trans (Nat.le_of_lt (Nat.lt_succ_self d)) hd
              let pred : Nat := stepTarget + d
              have hPredLe6 : pred ≤ 6 := by
                have hStepLe7 : stepTarget + d.succ ≤ 7 := by
                  have h1 : stepTarget + d.succ ≤ stepTarget + (7 - stepTarget) := Nat.add_le_add_left hd stepTarget
                  simpa [Nat.add_sub_of_le hStepTargetLe7] using h1
                have : pred + 1 ≤ 7 := by
                  simpa [pred, Nat.succ_eq_add_one, Nat.add_assoc] using hStepLe7
                omega
              let t : Nat := 7 - pred
              have ht1 : 1 ≤ t := by
                have hPredLt7 : pred < 7 := Nat.lt_succ_of_le hPredLe6
                have htPos : 0 < 7 - pred := Nat.sub_pos_of_lt hPredLt7
                simpa [t] using (Nat.succ_le_of_lt htPos)
              have htLt : t < k := by
                have hsTargetLt7 : sTarget < 7 := by
                  have : 7 - k < 7 := Nat.sub_lt (by decide : 0 < 7) hkPos
                  simpa [sTarget] using this
                have hsTargetLtPred : sTarget < pred := by
                  have hsTargetLtStep : sTarget < stepTarget := by
                    simpa [stepTarget] using (Nat.lt_succ_self sTarget)
                  have hStepLePred : stepTarget ≤ pred := Nat.le_add_right stepTarget d
                  exact Nat.lt_of_lt_of_le hsTargetLtStep hStepLePred
                have : 7 - pred < 7 - sTarget := Nat.sub_lt_sub_left hsTargetLt7 hsTargetLtPred
                simpa [t, hOff] using this
              have htLe : t ≤ k := Nat.le_of_lt htLt
              rcases Chess.Movement.squareFromInts_bishopDelta_step_some m.fromSq m.toSq hMove t (by
                  simpa [k] using htLe) with ⟨sq, hSq⟩
              have hSqW :
                  Movement.squareFromInts (m.fromSq.fileInt + df * (t : Int))
                      (m.fromSq.rankInt + dr * (t : Int)) =
                    some sq := by
                simpa [df, dr] using hSq
              have hEmptySq : Rules.isEmpty gs.board sq = true := by
                exact hEmptyIntermediate t ht1 (by simpa [k] using htLt) sq (by simpa using hSqW)
              have hRec :
                  mv ∈ Rules.slidingTargets.walk m.fromSq m.piece gs.board m.piece.color 7 df dr pred
                    ({ piece := m.piece, fromSq := m.fromSq, toSq := sq } :: acc) :=
                ih hd' ({ piece := m.piece, fromSq := m.fromSq, toSq := sq } :: acc)
              have hStep : stepTarget + d.succ = Nat.succ pred := by
                simp [pred, stepTarget, Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
              have hSqWalk :
                  Movement.squareFromInts (m.fromSq.fileInt + df * (↑(7 - pred) : Int))
                      (m.fromSq.rankInt + dr * (↑(7 - pred) : Int)) =
                    some sq := by
                simpa [t] using hSqW
              rw [hStep]
              simp [Rules.slidingTargets.walk]
              rw [hSqWalk]
              simp [hEmptySq]
              exact hRec
        have hEq : stepTarget + dFinal = 7 := Nat.add_sub_of_le hStepTargetLe7
        have hMem : mv ∈ Rules.slidingTargets.walk m.fromSq m.piece gs.board m.piece.color 7 df dr (stepTarget + dFinal) acc :=
          hLift dFinal (Nat.le_refl _) acc
        simpa [hEq, dFinal] using hMem

      cases hAt : gs.board.get m.toSq with
      | none =>
          have hAt' : gs.board m.toSq = none := by simpa using hAt
          have hCap : m.isCapture = false := capture_eq_of_target_empty gs m hSem0 hEP hAt'
          have hEqMove :
              ({ piece := m.piece, fromSq := m.fromSq, toSq := m.toSq, isCapture := false } : Move) = m :=
            move_eq_record_of_fields m false hCap hPromo hCastle hRookNone.1 hRookNone.2 hEP
          have hEmptyTgt : Rules.isEmpty gs.board m.toSq = true := by simpa [Rules.isEmpty] using hAt'
          let mv : Move := { piece := m.piece, fromSq := m.fromSq, toSq := m.toSq }
          have hMvWalk :
              ∀ acc, mv ∈ Rules.slidingTargets.walk m.fromSq m.piece gs.board m.piece.color 7 df dr 7 acc := by
            let sTarget : Nat := 7 - k
            have hSqAtTarget :
                Movement.squareFromInts (m.fromSq.fileInt + df * Int.ofNat (7 - sTarget))
                    (m.fromSq.rankInt + dr * Int.ofNat (7 - sTarget)) =
                  some m.toSq := by
              have hTgt := Movement.squareFromInts_bishopDelta_bishopOffset m.fromSq m.toSq hMove
              simpa [sTarget, k, df, dr, Nat.sub_sub_self hkLe7] using hTgt
            have hBase :
                ∀ acc,
                  mv ∈ Rules.slidingTargets.walk m.fromSq m.piece gs.board m.piece.color 7 df dr (Nat.succ sTarget) acc := by
              intro acc
              exact
                Rules.slidingTargets_walk_mem_of_empty_square m.fromSq m.piece gs.board m.piece.color 7 df dr sTarget acc
                  m.toSq hSqAtTarget hEmptyTgt
            exact walk_mem_to_step7 mv (by simpa [sTarget] using hBase)
          have hMemSliding :
              mv ∈ Rules.slidingTargets gs m.fromSq m.piece queenDeltas := by
            unfold Rules.slidingTargets
            have :
                ∀ (deltas : List (Int × Int)),
                  Movement.bishopDelta m.fromSq m.toSq ∈ deltas →
                    mv ∈
                      List.foldr
                        (fun d acc =>
                          let (df0, dr0) := d
                          Rules.slidingTargets.walk m.fromSq m.piece gs.board m.piece.color 7 df0 dr0 7 acc)
                        [] deltas := by
              intro deltas hIn
              induction deltas with
              | nil =>
                  cases (show False by simpa using hIn)
              | cons d rest ih =>
                  have hSplit :
                      Movement.bishopDelta m.fromSq m.toSq = d ∨ Movement.bishopDelta m.fromSq m.toSq ∈ rest := by
                    simpa [List.mem_cons] using hIn
                  cases hSplit with
                  | inl hEq =>
                      cases d with
                      | mk df0 dr0 =>
                          have hdf : df0 = df := by
                            simpa [df] using (congrArg Prod.fst hEq).symm
                          have hdr : dr0 = dr := by
                            simpa [dr] using (congrArg Prod.snd hEq).symm
                          let acc :=
                            rest.foldr
                              (fun d acc =>
                                let (df1, dr1) := d
                                Rules.slidingTargets.walk m.fromSq m.piece gs.board m.piece.color 7 df1 dr1 7 acc)
                              []
                          have hWalk :
                              mv ∈ Rules.slidingTargets.walk m.fromSq m.piece gs.board m.piece.color 7 df0 dr0 7 acc := by
                            simpa [hdf, hdr, acc] using hMvWalk acc
                          simpa [List.foldr, acc] using hWalk
                  | inr hInRest =>
                      cases d with
                      | mk df0 dr0 =>
                          let acc :=
                            rest.foldr
                              (fun d acc =>
                                let (df1, dr1) := d
                                Rules.slidingTargets.walk m.fromSq m.piece gs.board m.piece.color 7 df1 dr1 7 acc)
                              []
                          have hAcc : mv ∈ acc := by
                            simpa [acc] using ih hInRest
                          have hHead :
                              mv ∈ Rules.slidingTargets.walk m.fromSq m.piece gs.board m.piece.color 7 df0 dr0 7 acc :=
                            slidingTargets_walk_acc_subset m.fromSq m.piece gs.board m.piece.color 7 df0 dr0 7 acc
                              (m := mv) hAcc
                          simpa [List.foldr, acc] using hHead
            simpa [queenDeltas] using this queenDeltas hDeltaMemQ
          simpa [hEqMove, mv] using hMemSliding
      | some p =>
          have hAt' : gs.board m.toSq = some p := by simpa using hAt
          have hCap : m.isCapture = true :=
            capture_eq_true_of_target_enemy gs m p hSem0 hAt' hDest hEP
          have hEqMove :
              ({ piece := m.piece, fromSq := m.fromSq, toSq := m.toSq, isCapture := true } : Move) = m :=
            move_eq_record_of_fields m true hCap hPromo hCastle hRookNone.1 hRookNone.2 hEP
          have hEnemyTgt : Rules.isEnemyNonKingAt gs.board m.piece.color m.toSq = true := by
            unfold destinationFriendlyFreeProp destinationFriendlyFree at hDest
            have hBoth : p.color ≠ m.piece.color ∧ p.pieceType ≠ PieceType.King := by
              have : decide (p.color ≠ m.piece.color ∧ p.pieceType ≠ PieceType.King) = true := by
                simpa [hAt'] using hDest
              simpa [decide_eq_true_eq] using this
            simp [Rules.isEnemyNonKingAt, hAt', hBoth.1, hBoth.2]
          let mv : Move := { piece := m.piece, fromSq := m.fromSq, toSq := m.toSq, isCapture := true }
          have hMvWalk :
              ∀ acc, mv ∈ Rules.slidingTargets.walk m.fromSq m.piece gs.board m.piece.color 7 df dr 7 acc := by
            let sTarget : Nat := 7 - k
            have hSqAtTarget :
                Movement.squareFromInts (m.fromSq.fileInt + df * Int.ofNat (7 - sTarget))
                    (m.fromSq.rankInt + dr * Int.ofNat (7 - sTarget)) =
                  some m.toSq := by
              have hTgt := Movement.squareFromInts_bishopDelta_bishopOffset m.fromSq m.toSq hMove
              simpa [sTarget, k, df, dr, Nat.sub_sub_self hkLe7] using hTgt
            have hEmptyFalse : Rules.isEmpty gs.board m.toSq = false := by
              simp [Rules.isEmpty, hAt']
            have hBase :
                ∀ acc,
                  mv ∈ Rules.slidingTargets.walk m.fromSq m.piece gs.board m.piece.color 7 df dr (Nat.succ sTarget) acc := by
              intro acc
              exact
                Rules.slidingTargets_walk_mem_of_enemy_square m.fromSq m.piece gs.board m.piece.color 7 df dr sTarget acc
                  m.toSq hSqAtTarget hEmptyFalse hEnemyTgt
            exact walk_mem_to_step7 mv (by simpa [sTarget] using hBase)
          have hMemSliding :
              mv ∈ Rules.slidingTargets gs m.fromSq m.piece queenDeltas := by
            unfold Rules.slidingTargets
            have :
                ∀ (deltas : List (Int × Int)),
                  Movement.bishopDelta m.fromSq m.toSq ∈ deltas →
                    mv ∈
                      List.foldr
                        (fun d acc =>
                          let (df0, dr0) := d
                          Rules.slidingTargets.walk m.fromSq m.piece gs.board m.piece.color 7 df0 dr0 7 acc)
                        [] deltas := by
              intro deltas hIn
              induction deltas with
              | nil =>
                  cases (show False by simpa using hIn)
              | cons d rest ih =>
                  have hSplit :
                      Movement.bishopDelta m.fromSq m.toSq = d ∨ Movement.bishopDelta m.fromSq m.toSq ∈ rest := by
                    simpa [List.mem_cons] using hIn
                  cases hSplit with
                  | inl hEq =>
                      cases d with
                      | mk df0 dr0 =>
                          have hdf : df0 = df := by
                            simpa [df] using (congrArg Prod.fst hEq).symm
                          have hdr : dr0 = dr := by
                            simpa [dr] using (congrArg Prod.snd hEq).symm
                          let acc :=
                            rest.foldr
                              (fun d acc =>
                                let (df1, dr1) := d
                                Rules.slidingTargets.walk m.fromSq m.piece gs.board m.piece.color 7 df1 dr1 7 acc)
                              []
                          have hWalk :
                              mv ∈ Rules.slidingTargets.walk m.fromSq m.piece gs.board m.piece.color 7 df0 dr0 7 acc := by
                            simpa [hdf, hdr, acc] using hMvWalk acc
                          simpa [List.foldr, acc] using hWalk
                  | inr hInRest =>
                      cases d with
                      | mk df0 dr0 =>
                          let acc :=
                            rest.foldr
                              (fun d acc =>
                                let (df1, dr1) := d
                                Rules.slidingTargets.walk m.fromSq m.piece gs.board m.piece.color 7 df1 dr1 7 acc)
                              []
                          have hAcc : mv ∈ acc := by
                            simpa [acc] using ih hInRest
                          have hHead :
                              mv ∈ Rules.slidingTargets.walk m.fromSq m.piece gs.board m.piece.color 7 df0 dr0 7 acc :=
                            slidingTargets_walk_acc_subset m.fromSq m.piece gs.board m.piece.color 7 df0 dr0 7 acc
                              (m := mv) hAcc
                          simpa [List.foldr, acc] using hHead
            simpa [queenDeltas] using this queenDeltas hDeltaMemQ
          simpa [hEqMove, mv] using hMemSliding

end Rules
end Chess
