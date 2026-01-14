import Init.Omega
import Chess.Rules
import Chess.Spec
import Chess.ParsingProofs
import Chess.SemanticPromotionLemmas
import Chess.SemanticMoveFlagLemmas

namespace Chess
namespace Rules

open Movement

theorem mem_standardFilterMap_promotion_none (gs : GameState) (src : Square) (p : Piece)
    (targets : List Square) (m : Move) :
    m ∈ targets.filterMap (fun target =>
      if destinationFriendlyFree gs { piece := p, fromSq := src, toSq := target } then
        match gs.board target with
        | some _ => some { piece := p, fromSq := src, toSq := target, isCapture := true }
        | none => some { piece := p, fromSq := src, toSq := target }
      else
        none) →
    m.promotion = none := by
  intro hMem
  rcases (List.mem_filterMap.1 hMem) with ⟨target, _hTargetMem, hSome⟩
  cases hFree : destinationFriendlyFree gs { piece := p, fromSq := src, toSq := target } with
  | false =>
      have : False := by
        simpa [hFree] using hSome
      cases this
  | true =>
      cases hBoard : gs.board target <;> simp [hFree, hBoard] at hSome
      ·
        have : m = { piece := p, fromSq := src, toSq := target } := by
          simpa using hSome.symm
        simp [this]
      ·
        have : m = { piece := p, fromSq := src, toSq := target, isCapture := true } := by
          simpa using hSome.symm
        simp [this]

theorem slidingTargets_walk_mem_promotion_none
    (src : Square) (p : Piece) (board : Board) (color : Color) (maxStep : Nat)
    (df dr : Int) :
    ∀ (step : Nat) (acc : List Move) (m : Move),
      (∀ x ∈ acc, x.promotion = none) →
      m ∈ Rules.slidingTargets.walk src p board color maxStep df dr step acc →
      m.promotion = none := by
  intro step
  induction step with
  | zero =>
      intro acc m hAcc hMem
      simp [Rules.slidingTargets.walk] at hMem
      exact hAcc m hMem
  | succ s ih =>
      intro acc m hAcc hMem
      have hMem' :
          m ∈
            match Movement.squareFromInts (src.fileInt + df * Int.ofNat (maxStep - s))
                  (src.rankInt + dr * Int.ofNat (maxStep - s)) with
            | none => acc
            | some target =>
                if Rules.isEmpty board target = true then
                  Rules.slidingTargets.walk src p board color maxStep df dr s
                    ({ piece := p, fromSq := src, toSq := target } :: acc)
                else if Rules.isEnemyNonKingAt board color target = true then
                  { piece := p, fromSq := src, toSq := target, isCapture := true } :: acc
                else acc := by
        simpa [Rules.slidingTargets.walk] using hMem
      revert hMem'
      cases hSq :
          Movement.squareFromInts (src.fileInt + df * Int.ofNat (maxStep - s))
              (src.rankInt + dr * Int.ofNat (maxStep - s)) with
      | none =>
          intro hMem'
          exact hAcc m hMem'
      | some target =>
          intro hMem'
          by_cases hEmpty : Rules.isEmpty board target = true
          ·
            have hRec :
                m ∈ Rules.slidingTargets.walk src p board color maxStep df dr s
                      ({ piece := p, fromSq := src, toSq := target } :: acc) := by
              simpa [hEmpty] using hMem'
            have hAcc' :
                ∀ x ∈ ({ piece := p, fromSq := src, toSq := target } :: acc), x.promotion = none := by
              intro x hx
              have hx' : x = { piece := p, fromSq := src, toSq := target } ∨ x ∈ acc := by
                simpa [List.mem_cons] using hx
              cases hx' with
              | inl hEq => simp [hEq]
              | inr hIn => exact hAcc x hIn
            exact ih ({ piece := p, fromSq := src, toSq := target } :: acc) m hAcc' hRec
          ·
            by_cases hEnemy : Rules.isEnemyNonKingAt board color target = true
            ·
              have hMemCons :
                  m ∈ { piece := p, fromSq := src, toSq := target, isCapture := true } :: acc := by
                simpa [hEmpty, hEnemy] using hMem'
              have hSplit :
                  m = { piece := p, fromSq := src, toSq := target, isCapture := true } ∨ m ∈ acc := by
                simpa [List.mem_cons] using hMemCons
              cases hSplit with
              | inl hEq => simp [hEq]
              | inr hIn => exact hAcc m hIn
            ·
              have hIn : m ∈ acc := by
                simpa [hEmpty, hEnemy] using hMem'
              exact hAcc m hIn

theorem mem_slidingTargets_promotion_none (gs : GameState) (src : Square) (p : Piece)
    (deltas : List (Int × Int)) (m : Move) :
    m ∈ Rules.slidingTargets gs src p deltas →
    m.promotion = none := by
  revert m
  induction deltas with
  | nil =>
      intro m hMem
      cases (show False by simpa [Rules.slidingTargets] using hMem)
  | cons d rest ih =>
      intro m hMem
      cases d with
      | mk df dr =>
          let acc :=
            List.foldr
              (fun d acc =>
                match d with
                | (df, dr) =>
                    Rules.slidingTargets.walk src p gs.board p.color 7 df dr 7 acc)
              [] rest
          have hAccAll : ∀ x ∈ acc, x.promotion = none := by
            intro x hx
            have hx' : x ∈ Rules.slidingTargets gs src p rest := by
              simpa [Rules.slidingTargets, acc] using hx
            exact ih x hx'
          have hMem' : m ∈ Rules.slidingTargets.walk src p gs.board p.color 7 df dr 7 acc := by
            simpa [Rules.slidingTargets, List.foldr, acc] using hMem
          have hProm :=
            slidingTargets_walk_mem_promotion_none src p gs.board p.color 7 df dr 7 acc m hAccAll hMem'
          exact hProm

theorem castleMoveIfLegal_promotion_none (gs : GameState) (kingSide : Bool) (m : Move) :
    castleMoveIfLegal gs kingSide = some m →
    m.promotion = none := by
  intro hCM
  -- `castleMoveIfLegal` only ever constructs a move with default `promotion := none`.
  -- We follow the successful branch to recover the constructed record.
  let c := gs.toMove
  let cfg := castleConfig c kingSide
  have h0 :
      (if castleRight gs.castlingRights c kingSide then
          match gs.board cfg.kingFrom, gs.board cfg.rookFrom with
          | some k, some r =>
              if k.pieceType = PieceType.King ∧ k.color = c ∧
                  r.pieceType = PieceType.Rook ∧ r.color = c then
                let pathEmpty := cfg.emptySquares.all (isEmpty gs.board)
                let safe := cfg.checkSquares.all (fun sq =>
                  !(inCheck (gs.board.update cfg.kingFrom none |>.update sq (some k)) c))
                if pathEmpty && safe then
                  some
                    { piece := k
                      fromSq := cfg.kingFrom
                      toSq := cfg.kingTo
                      isCastle := true
                      castleRookFrom := some cfg.rookFrom
                      castleRookTo := some cfg.rookTo }
                else none
              else none
          | _, _ => none
        else none) = some m := by
    simpa [castleMoveIfLegal, c, cfg] using hCM
  cases hRight : castleRight gs.castlingRights c kingSide with
  | false =>
      cases (show False by simpa [hRight] using h0)
  | true =>
      have h1 :
          (match gs.board cfg.kingFrom, gs.board cfg.rookFrom with
          | some k, some r =>
              if k.pieceType = PieceType.King ∧ k.color = c ∧
                  r.pieceType = PieceType.Rook ∧ r.color = c then
                let pathEmpty := cfg.emptySquares.all (isEmpty gs.board)
                let safe := cfg.checkSquares.all (fun sq =>
                  !(inCheck (gs.board.update cfg.kingFrom none |>.update sq (some k)) c))
                if pathEmpty && safe then
                  some
                    { piece := k
                      fromSq := cfg.kingFrom
                      toSq := cfg.kingTo
                      isCastle := true
                      castleRookFrom := some cfg.rookFrom
                      castleRookTo := some cfg.rookTo }
                else none
              else none
          | _, _ => none) = some m := by
        simpa [hRight] using h0
      revert h1
      cases hK : gs.board cfg.kingFrom with
      | none =>
          intro h1
          cases (show False by simpa [hK] using h1)
      | some k =>
          cases hR : gs.board cfg.rookFrom with
          | none =>
              intro h1
              cases (show False by simpa [hK, hR] using h1)
          | some r =>
              intro h1
              by_cases hPieces :
                  k.pieceType = PieceType.King ∧ k.color = c ∧
                    r.pieceType = PieceType.Rook ∧ r.color = c
              ·
                have h2 :
                    (let pathEmpty := cfg.emptySquares.all (isEmpty gs.board)
                    let safe := cfg.checkSquares.all (fun sq =>
                      !(inCheck (gs.board.update cfg.kingFrom none |>.update sq (some k)) c))
                    if pathEmpty && safe then
                      some
                        { piece := k
                          fromSq := cfg.kingFrom
                          toSq := cfg.kingTo
                          isCastle := true
                          castleRookFrom := some cfg.rookFrom
                          castleRookTo := some cfg.rookTo }
                    else none) = some m := by
                  simpa [hK, hR, hPieces] using h1
                let pathEmpty := cfg.emptySquares.all (isEmpty gs.board)
                let safe := cfg.checkSquares.all (fun sq =>
                  !(inCheck (gs.board.update cfg.kingFrom none |>.update sq (some k)) c))
                cases hOk : (pathEmpty && safe) with
                | false =>
                    cases (show False by simpa [pathEmpty, safe, hOk] using h2)
                | true =>
                    have hEq :
                        { piece := k
                          fromSq := cfg.kingFrom
                          toSq := cfg.kingTo
                          isCastle := true
                          castleRookFrom := some cfg.rookFrom
                          castleRookTo := some cfg.rookTo } = m := by
                      simpa [pathEmpty, safe, hOk] using h2
                    -- The constructed literal has default `promotion := none`.
                    have hProm : m.promotion = none := by
                      have := congrArg Move.promotion hEq.symm
                      simpa using this
                    exact hProm
              ·
                cases (show False by simpa [hK, hR, hPieces] using h1)

theorem mem_pawn_pieceTargets_promotion_isSome_implies_toPromotionRank
    (gs : GameState) (src : Square) (p : Piece) (m : Move)
    (hPawn : p.pieceType = PieceType.Pawn)
    (hTargets : m ∈ pieceTargets gs src p)
    (hSome : m.promotion.isSome = true) :
    m.toSq.rankNat = pawnPromotionRank p.color := by
  -- Unfold pawn generator and split on forward vs capture lists, then on whether we are in a
  -- `promotionMoves base` branch.
  let board := gs.board
  let color := p.color
  let dir := Movement.pawnDirection color
  let oneStep := Movement.squareFromInts src.fileInt (src.rankInt + dir)
  let twoStep := Movement.squareFromInts src.fileInt (src.rankInt + 2 * dir)
  let forwardMoves : List Move :=
    match oneStep with
    | some target =>
        if isEmpty board target then
          let base : List Move := [{ piece := p, fromSq := src, toSq := target }]
          let doubleStep : List Move :=
            if src.rankNat = pawnStartRank color then
              match twoStep with
              | some target2 =>
                  if isEmpty board target2 then
                    [{ piece := p, fromSq := src, toSq := target2 }]
                  else []
              | none => []
            else []
          base ++ doubleStep
        else []
    | none => []
  let stepFn : Int → List Move → List Move :=
    fun df acc =>
      match Movement.squareFromInts (src.fileInt + df) (src.rankInt + dir) with
      | some target =>
          if isEnemyNonKingAt board color target then
            promotionMoves { piece := p, fromSq := src, toSq := target, isCapture := true } ++ acc
          else if gs.enPassantTarget = some target ∧ isEmpty board target ∧ enPassantFromHistory gs target = true then
            { piece := p, fromSq := src, toSq := target, isCapture := true, isEnPassant := true } :: acc
          else acc
      | none => acc
  let captureMoves : List Move := ([-1, 1] : List Int).foldr stepFn []
  have hMem' :
      m ∈ forwardMoves.foldr (fun mv acc => promotionMoves mv ++ acc) [] ++ captureMoves := by
    simpa [pieceTargets, hPawn, board, color, dir, oneStep, twoStep, forwardMoves, stepFn, captureMoves] using
      hTargets
  cases List.mem_append.1 hMem' with
  | inl hForward =>
      rcases (Chess.Parsing.List.mem_foldr_append_iff (f := promotionMoves) (b := m) forwardMoves).1 hForward with
        ⟨base, _hBaseMem, hInProm⟩
      -- Forward bases have `promotion = none` by construction.
      have hBaseProm : base.promotion = none := by
        -- `base` is one of the literals `{ piece := p, fromSq := src, toSq := ... }`.
        -- Those literals use the default `promotion := none`.
        -- The proof is by exhausting the forward list shape.
        dsimp [forwardMoves] at _hBaseMem
        cases hOne : oneStep with
        | none =>
            cases (show False by simpa [hOne] using _hBaseMem)
        | some target =>
            cases hEmpty : isEmpty board target with
            | false =>
                cases (show False by simpa [hOne, hEmpty] using _hBaseMem)
            | true =>
                have hMem'' :
                    base ∈ [{ piece := p, fromSq := src, toSq := target }] ++
                      (if src.rankNat = pawnStartRank color then
                          match twoStep with
                          | some target2 =>
                              if isEmpty board target2 then
                                [{ piece := p, fromSq := src, toSq := target2 }]
                              else []
                          | none => []
                        else []) := by
                  simpa [hOne, hEmpty] using _hBaseMem
                cases List.mem_append.1 hMem'' with
                | inl hIn =>
                    have hEq : base = { piece := p, fromSq := src, toSq := target } := by
                      simpa using hIn
                    subst hEq
                    simp
                | inr hIn =>
                    by_cases hStart : src.rankNat = pawnStartRank color
                    · cases hTwo : twoStep with
                      | none =>
                          cases (show False by simpa [hStart, hTwo] using hIn)
                      | some target2 =>
                          cases hEmpty2 : isEmpty board target2 with
                          | false =>
                              cases (show False by simpa [hStart, hTwo, hEmpty2] using hIn)
                          | true =>
                              have hEq : base = { piece := p, fromSq := src, toSq := target2 } := by
                                simpa [hStart, hTwo, hEmpty2] using hIn
                              subst hEq
                              simp
                    · cases (show False by simpa [hStart] using hIn)
      have hBasePromPred :
          base.piece.pieceType = PieceType.Pawn ∧
            base.toSq.rankNat = pawnPromotionRank base.piece.color :=
        promotionMoves_mem_promotion_isSome m base hBaseProm hInProm hSome
      -- `base.piece = p` by construction.
      have hBasePiece : base.piece = p := by
        -- Same case analysis as in `hBaseProm`.
        dsimp [forwardMoves] at _hBaseMem
        cases hOne : oneStep with
        | none =>
            cases (show False by simpa [hOne] using _hBaseMem)
        | some target =>
            cases hEmpty : isEmpty board target with
            | false =>
                cases (show False by simpa [hOne, hEmpty] using _hBaseMem)
            | true =>
                have hMem'' :
                    base ∈ [{ piece := p, fromSq := src, toSq := target }] ++
                      (if src.rankNat = pawnStartRank color then
                          match twoStep with
                          | some target2 =>
                              if isEmpty board target2 then
                                [{ piece := p, fromSq := src, toSq := target2 }]
                              else []
                          | none => []
                        else []) := by
                  simpa [hOne, hEmpty] using _hBaseMem
                cases List.mem_append.1 hMem'' with
                | inl hIn =>
                    have hEq : base = { piece := p, fromSq := src, toSq := target } := by
                      simpa using hIn
                    subst hEq
                    simp
                | inr hIn =>
                    by_cases hStart : src.rankNat = pawnStartRank color
                    · cases hTwo : twoStep with
                      | none =>
                          cases (show False by simpa [hStart, hTwo] using hIn)
                      | some target2 =>
                          cases hEmpty2 : isEmpty board target2 with
                          | false =>
                              cases (show False by simpa [hStart, hTwo, hEmpty2] using hIn)
                          | true =>
                              have hEq : base = { piece := p, fromSq := src, toSq := target2 } := by
                                simpa [hStart, hTwo, hEmpty2] using hIn
                              subst hEq
                              simp
                    · cases (show False by simpa [hStart] using hIn)
      have hToEq : m.toSq = base.toSq := Chess.Parsing.promotionMoves_mem_toSq_eq m base hInProm
      -- Conclude on `m.toSq` using base's promotion rank.
      have : base.toSq.rankNat = pawnPromotionRank p.color := by
        simpa [hBasePiece] using hBasePromPred.2
      simpa [hToEq] using this
  | inr hCapture =>
      -- Unroll capture foldr into the two `df` branches.
      have hCapMem : m ∈ stepFn (-1) (stepFn 1 []) := by
        simpa [captureMoves, List.foldr] using hCapture
      -- Analyze `df = -1` branch.
      dsimp [stepFn] at hCapMem
      cases hSqNeg : Movement.squareFromInts (src.fileInt + (-1)) (src.rankInt + dir) with
      | none =>
          -- Must come from `df = 1` branch.
          have hAcc :
              m ∈
                match Movement.squareFromInts (src.fileInt + 1) (src.rankInt + dir) with
                | some target =>
                    if isEnemyNonKingAt board color target = true then
                      promotionMoves { piece := p, fromSq := src, toSq := target, isCapture := true }
                    else if gs.enPassantTarget = some target ∧ isEmpty board target ∧ enPassantFromHistory gs target = true then
                      [{ piece := p, fromSq := src, toSq := target, isCapture := true, isEnPassant := true }]
                    else []
                | none => [] := by
            simpa [hSqNeg, stepFn] using hCapMem
          cases hSqPos : Movement.squareFromInts (src.fileInt + 1) (src.rankInt + dir) with
          | none =>
              cases (show False by simpa [hSqPos] using hAcc)
          | some target =>
              cases hEnemy : isEnemyNonKingAt board color target with
              | true =>
                  have hIn : m ∈ promotionMoves { piece := p, fromSq := src, toSq := target, isCapture := true } := by
                    simpa [hSqPos, hEnemy] using hAcc
                  have hBaseProm :
                      ({ piece := p, fromSq := src, toSq := target, isCapture := true } : Move).promotion = none := by
                    simp
                  have hBasePromPred :
                      ({ piece := p, fromSq := src, toSq := target, isCapture := true } : Move).piece.pieceType =
                          PieceType.Pawn ∧
                        ({ piece := p, fromSq := src, toSq := target, isCapture := true } : Move).toSq.rankNat =
                          pawnPromotionRank ({ piece := p, fromSq := src, toSq := target, isCapture := true } : Move).piece.color :=
                    promotionMoves_mem_promotion_isSome _ _ hBaseProm hIn hSome
                  have hToEq : m.toSq = target := by
                    simpa using (Chess.Parsing.promotionMoves_mem_toSq_eq m _ hIn)
                  simpa [hToEq] using hBasePromPred.2
              | false =>
                  -- Only EP or empty accumulator remains; EP cannot have promotion.
                  by_cases hEP : gs.enPassantTarget = some target ∧ isEmpty board target ∧ enPassantFromHistory gs target = true
                  · have hEq :
                        m = { piece := p
                              fromSq := src
                              toSq := target
                              isCapture := true
                              isEnPassant := true } := by
                      simpa [hSqPos, hEnemy, hEP] using hAcc
                    subst hEq
                    have : False := by
                      simpa using hSome
                    cases this
                  · cases (show False by simpa [hSqPos, hEnemy, hEP] using hAcc)
      | some target =>
          cases hEnemy : isEnemyNonKingAt board color target with
          | true =>
              have hSplit :
                  m ∈ promotionMoves { piece := p, fromSq := src, toSq := target, isCapture := true } ∨
                    m ∈
                      match Movement.squareFromInts (src.fileInt + 1) (src.rankInt + dir) with
                      | some target2 =>
                          if isEnemyNonKingAt board color target2 = true then
                            promotionMoves { piece := p, fromSq := src, toSq := target2, isCapture := true }
                          else if gs.enPassantTarget = some target2 ∧ isEmpty board target2 ∧ enPassantFromHistory gs target2 = true then
                            [{ piece := p
                               fromSq := src
                               toSq := target2
                               isCapture := true
                               isEnPassant := true }]
                          else []
                      | none => [] := by
                simpa [hSqNeg, hEnemy, List.mem_append, stepFn] using hCapMem
              cases hSplit with
              | inl hIn =>
                  have hBaseProm :
                      ({ piece := p, fromSq := src, toSq := target, isCapture := true } : Move).promotion = none := by
                    simp
                  have hBasePromPred :=
                    promotionMoves_mem_promotion_isSome m
                      ({ piece := p, fromSq := src, toSq := target, isCapture := true } : Move)
                      hBaseProm hIn hSome
                  have hToEq : m.toSq = target := by
                    simpa using (Chess.Parsing.promotionMoves_mem_toSq_eq m _ hIn)
                  simpa [hToEq] using hBasePromPred.2
              | inr hAcc =>
                  -- Delegate to `df = 1` as above: if promotion exists, it must be enemy capture.
                  cases hSqPos : Movement.squareFromInts (src.fileInt + 1) (src.rankInt + dir) with
                  | none =>
                      cases (show False by simpa [hSqPos] using hAcc)
                  | some target2 =>
                      cases hEnemy2 : isEnemyNonKingAt board color target2 with
                      | true =>
                          have hIn : m ∈ promotionMoves { piece := p, fromSq := src, toSq := target2, isCapture := true } := by
                            simpa [hSqPos, hEnemy2] using hAcc
                          have hBaseProm :
                              ({ piece := p, fromSq := src, toSq := target2, isCapture := true } : Move).promotion = none := by
                            simp
                          have hBasePromPred :=
                            promotionMoves_mem_promotion_isSome m
                              ({ piece := p, fromSq := src, toSq := target2, isCapture := true } : Move)
                              hBaseProm hIn hSome
                          have hToEq : m.toSq = target2 := by
                            simpa using (Chess.Parsing.promotionMoves_mem_toSq_eq m _ hIn)
                          simpa [hToEq] using hBasePromPred.2
                      | false =>
                          -- EP or empty; cannot have promotion.
                          by_cases hEP : gs.enPassantTarget = some target2 ∧ isEmpty board target2 ∧ enPassantFromHistory gs target2 = true
                          · have hEq :
                                m =
                                  { piece := p
                                    fromSq := src
                                    toSq := target2
                                    isCapture := true
                                    isEnPassant := true } := by
                              simpa [hSqPos, hEnemy2, hEP] using hAcc
                            subst hEq
                            have : False := by
                              simpa using hSome
                            cases this
                          · cases (show False by simpa [hSqPos, hEnemy2, hEP] using hAcc)
          | false =>
              -- Either EP literal or accumulator; EP cannot have promotion.
              by_cases hEP : gs.enPassantTarget = some target ∧ isEmpty board target ∧ enPassantFromHistory gs target = true
              · have hEqOr :
                    m = { piece := p
                          fromSq := src
                          toSq := target
                          isCapture := true
                          isEnPassant := true } ∨
                      m ∈
                        match Movement.squareFromInts (src.fileInt + 1) (src.rankInt + dir) with
                        | some target2 =>
                            if isEnemyNonKingAt board color target2 = true then
                              promotionMoves { piece := p, fromSq := src, toSq := target2, isCapture := true }
                            else if gs.enPassantTarget = some target2 ∧ isEmpty board target2 ∧ enPassantFromHistory gs target2 = true then
                              [{ piece := p
                                 fromSq := src
                                 toSq := target2
                                 isCapture := true
                                 isEnPassant := true }]
                            else []
                        | none => [] := by
                  simpa [hSqNeg, hEnemy, hEP, List.mem_cons, stepFn] using hCapMem
                cases hEqOr with
                | inl hEq =>
                    subst hEq
                    have : False := by
                      simpa using hSome
                    cases this
                | inr hAcc =>
                    -- Delegate to `df = 1` analysis; but it cannot produce promotion unless enemy.
                    cases hSqPos : Movement.squareFromInts (src.fileInt + 1) (src.rankInt + dir) with
                    | none =>
                        cases (show False by simpa [hSqPos] using hAcc)
                    | some target2 =>
                        cases hEnemy2 : isEnemyNonKingAt board color target2 with
                        | true =>
                            have hIn :
                                m ∈ promotionMoves { piece := p, fromSq := src, toSq := target2, isCapture := true } := by
                              simpa [hSqPos, hEnemy2] using hAcc
                            have hBaseProm :
                                ({ piece := p, fromSq := src, toSq := target2, isCapture := true } : Move).promotion = none := by
                              simp
                            have hBasePromPred :=
                              promotionMoves_mem_promotion_isSome m
                                ({ piece := p, fromSq := src, toSq := target2, isCapture := true } : Move)
                                hBaseProm hIn hSome
                            have hToEq : m.toSq = target2 := by
                              simpa using (Chess.Parsing.promotionMoves_mem_toSq_eq m _ hIn)
                            simpa [hToEq] using hBasePromPred.2
                        | false =>
                            by_cases hEP2 : gs.enPassantTarget = some target2 ∧ isEmpty board target2 ∧ enPassantFromHistory gs target2 = true
                            · have hEq :
                                  m =
                                    { piece := p
                                      fromSq := src
                                      toSq := target2
                                      isCapture := true
                                      isEnPassant := true } := by
                                simpa [hSqPos, hEnemy2, hEP2] using hAcc
                              subst hEq
                              have : False := by
                                simpa using hSome
                              cases this
                            · cases (show False by simpa [hSqPos, hEnemy2, hEP2] using hAcc)
              ·
                -- Not enemy, not EP: must come from accumulator, recurse to df=1 similarly; cannot promote.
                have hAcc :
                    m ∈
                      match Movement.squareFromInts (src.fileInt + 1) (src.rankInt + dir) with
                      | some target2 =>
                          if isEnemyNonKingAt board color target2 = true then
                            promotionMoves { piece := p, fromSq := src, toSq := target2, isCapture := true }
                          else if gs.enPassantTarget = some target2 ∧ isEmpty board target2 ∧ enPassantFromHistory gs target2 = true then
                            [{ piece := p
                               fromSq := src
                               toSq := target2
                               isCapture := true
                               isEnPassant := true }]
                          else []
                      | none => [] := by
                  simpa [hSqNeg, hEnemy, hEP, stepFn] using hCapMem
                cases hSqPos : Movement.squareFromInts (src.fileInt + 1) (src.rankInt + dir) with
                | none =>
                    cases (show False by simpa [hSqPos] using hAcc)
                | some target2 =>
                    cases hEnemy2 : isEnemyNonKingAt board color target2 with
                    | true =>
                        have hIn :
                            m ∈ promotionMoves { piece := p, fromSq := src, toSq := target2, isCapture := true } := by
                          simpa [hSqPos, hEnemy2] using hAcc
                        have hBaseProm :
                            ({ piece := p, fromSq := src, toSq := target2, isCapture := true } : Move).promotion = none := by
                          simp
                        have hBasePromPred :=
                          promotionMoves_mem_promotion_isSome m
                            ({ piece := p, fromSq := src, toSq := target2, isCapture := true } : Move)
                            hBaseProm hIn hSome
                        have hToEq : m.toSq = target2 := by
                          simpa using (Chess.Parsing.promotionMoves_mem_toSq_eq m _ hIn)
                        simpa [hToEq] using hBasePromPred.2
                    | false =>
                        by_cases hEP2 : gs.enPassantTarget = some target2 ∧ isEmpty board target2 ∧ enPassantFromHistory gs target2 = true
                        · have hEq :
                              m =
                                { piece := p
                                  fromSq := src
                                  toSq := target2
                                  isCapture := true
                                  isEnPassant := true } := by
                            simpa [hSqPos, hEnemy2, hEP2] using hAcc
                          subst hEq
                          have : False := by
                            simpa using hSome
                          cases this
                        · cases (show False by simpa [hSqPos, hEnemy2, hEP2] using hAcc)

private theorem promotionMoves_mem_promotion_eq_some_implies_mem_promotionTargets
    (m base : Move) (pt : PieceType) :
    base.promotion = none →
    m ∈ promotionMoves base →
    m.promotion = some pt →
    pt ∈ promotionTargets := by
  intro hBase hMem hEq
  unfold promotionMoves at hMem
  by_cases hProm :
      base.piece.pieceType = PieceType.Pawn ∧
        base.toSq.rankNat = pawnPromotionRank base.piece.color
  ·
    simp [hProm] at hMem
    rcases hMem with ⟨pt0, hpt0, hEqM⟩
    subst hEqM
    have : pt0 = pt := by
      have : (some pt0 : Option PieceType) = some pt := by
        simpa using hEq
      exact Option.some.inj this
    subst this
    simpa using hpt0
  ·
    simp [hProm] at hMem
    subst hMem
    cases (show False by simpa [hBase] using hEq)

theorem mem_pawn_pieceTargets_promotion_eq_some_implies_mem_promotionTargets
    (gs : GameState) (src : Square) (p : Piece) (m : Move) (pt : PieceType)
    (hPawn : p.pieceType = PieceType.Pawn)
    (hTargets : m ∈ pieceTargets gs src p)
    (hEq : m.promotion = some pt) :
    pt ∈ promotionTargets := by
  have hSome : m.promotion.isSome = true := by
    simp [hEq]
  -- Unfold pawn generator and split on forward vs capture lists, then on whether we are in a
  -- `promotionMoves base` branch.
  let board := gs.board
  let color := p.color
  let dir := Movement.pawnDirection color
  let oneStep := Movement.squareFromInts src.fileInt (src.rankInt + dir)
  let twoStep := Movement.squareFromInts src.fileInt (src.rankInt + 2 * dir)
  let forwardMoves : List Move :=
    match oneStep with
    | some target =>
        if isEmpty board target then
          let base : List Move := [{ piece := p, fromSq := src, toSq := target }]
          let doubleStep : List Move :=
            if src.rankNat = pawnStartRank color then
              match twoStep with
              | some target2 =>
                  if isEmpty board target2 then
                    [{ piece := p, fromSq := src, toSq := target2 }]
                  else []
              | none => []
            else []
          base ++ doubleStep
        else []
    | none => []
  let stepFn : Int → List Move → List Move :=
    fun df acc =>
      match Movement.squareFromInts (src.fileInt + df) (src.rankInt + dir) with
      | some target =>
          if isEnemyNonKingAt board color target then
            promotionMoves { piece := p, fromSq := src, toSq := target, isCapture := true } ++ acc
          else if gs.enPassantTarget = some target ∧ isEmpty board target ∧ enPassantFromHistory gs target = true then
            { piece := p, fromSq := src, toSq := target, isCapture := true, isEnPassant := true } :: acc
          else acc
      | none => acc
  let captureMoves : List Move := ([-1, 1] : List Int).foldr stepFn []
  have hMem' :
      m ∈ forwardMoves.foldr (fun mv acc => promotionMoves mv ++ acc) [] ++ captureMoves := by
    simpa [pieceTargets, hPawn, board, color, dir, oneStep, twoStep, forwardMoves, stepFn, captureMoves] using
      hTargets
  cases List.mem_append.1 hMem' with
  | inl hForward =>
      rcases (Chess.Parsing.List.mem_foldr_append_iff (f := promotionMoves) (b := m) forwardMoves).1 hForward with
        ⟨base, hBaseMem, hInProm⟩
      -- Forward bases have `promotion = none` by construction.
      have hBaseProm : base.promotion = none := by
        dsimp [forwardMoves] at hBaseMem
        cases hOne : oneStep with
        | none =>
            cases (show False by simpa [hOne] using hBaseMem)
        | some target =>
            cases hEmpty : isEmpty board target with
            | false =>
                cases (show False by simpa [hOne, hEmpty] using hBaseMem)
            | true =>
                have hMem'' :
                    base ∈ [{ piece := p, fromSq := src, toSq := target }] ++
                      (if src.rankNat = pawnStartRank color then
                          match twoStep with
                          | some target2 =>
                              if isEmpty board target2 then
                                [{ piece := p, fromSq := src, toSq := target2 }]
                              else []
                          | none => []
                        else []) := by
                  simpa [hOne, hEmpty] using hBaseMem
                cases List.mem_append.1 hMem'' with
                | inl hIn =>
                    have hEqBase : base = { piece := p, fromSq := src, toSq := target } := by
                      simpa using hIn
                    subst hEqBase
                    simp
                | inr hIn =>
                    by_cases hStart : src.rankNat = pawnStartRank color
                    · cases hTwo : twoStep with
                      | none =>
                          cases (show False by simpa [hStart, hTwo] using hIn)
                      | some target2 =>
                          cases hEmpty2 : isEmpty board target2 with
                          | false =>
                              cases (show False by simpa [hStart, hTwo, hEmpty2] using hIn)
                          | true =>
                              have hEqBase : base = { piece := p, fromSq := src, toSq := target2 } := by
                                simpa [hStart, hTwo, hEmpty2] using hIn
                              subst hEqBase
                              simp
                    · cases (show False by simpa [hStart] using hIn)
      exact promotionMoves_mem_promotion_eq_some_implies_mem_promotionTargets m base pt hBaseProm hInProm hEq
  | inr hCapture =>
      -- Unroll capture foldr into the two `df` branches.
      have hCapMem : m ∈ stepFn (-1) (stepFn 1 []) := by
        simpa [captureMoves, List.foldr] using hCapture
      -- Analyze `df = -1` branch.
      dsimp [stepFn] at hCapMem
      cases hSqNeg : Movement.squareFromInts (src.fileInt + (-1)) (src.rankInt + dir) with
      | none =>
          -- Must come from `df = 1` branch.
          have hAcc :
              m ∈
                match Movement.squareFromInts (src.fileInt + 1) (src.rankInt + dir) with
                | some target =>
                    if isEnemyNonKingAt board color target = true then
                      promotionMoves { piece := p, fromSq := src, toSq := target, isCapture := true }
                    else if gs.enPassantTarget = some target ∧ isEmpty board target ∧ enPassantFromHistory gs target = true then
                      [{ piece := p, fromSq := src, toSq := target, isCapture := true, isEnPassant := true }]
                    else []
                | none => [] := by
            simpa [hSqNeg] using hCapMem
          cases hSqPos : Movement.squareFromInts (src.fileInt + 1) (src.rankInt + dir) with
          | none =>
              cases (show False by simpa [hSqPos] using hAcc)
          | some target =>
              cases hEnemy : isEnemyNonKingAt board color target with
              | true =>
                  have hIn : m ∈ promotionMoves { piece := p, fromSq := src, toSq := target, isCapture := true } := by
                    simpa [hSqPos, hEnemy] using hAcc
                  have hBaseProm :
                      ({ piece := p, fromSq := src, toSq := target, isCapture := true } : Move).promotion = none := by
                    simp
                  exact
                    promotionMoves_mem_promotion_eq_some_implies_mem_promotionTargets m
                      ({ piece := p, fromSq := src, toSq := target, isCapture := true } : Move)
                      pt hBaseProm hIn hEq
              | false =>
                  by_cases hEP : gs.enPassantTarget = some target ∧ isEmpty board target ∧ enPassantFromHistory gs target = true
                  ·
                    have hEqEP :
                        m =
                          { piece := p
                            fromSq := src
                            toSq := target
                            isCapture := true
                            isEnPassant := true } := by
                      simpa [hSqPos, hEnemy, hEP] using hAcc
                    subst hEqEP
                    cases (show False by simpa using hEq)
                  · cases (show False by simpa [hSqPos, hEnemy, hEP] using hAcc)
      | some target =>
          cases hEnemy : isEnemyNonKingAt board color target with
          | true =>
              have hSplit :
                  m ∈ promotionMoves { piece := p, fromSq := src, toSq := target, isCapture := true } ∨
                    m ∈
                      match Movement.squareFromInts (src.fileInt + 1) (src.rankInt + dir) with
                      | some target2 =>
                          if isEnemyNonKingAt board color target2 = true then
                            promotionMoves { piece := p, fromSq := src, toSq := target2, isCapture := true }
                          else if gs.enPassantTarget = some target2 ∧ isEmpty board target2 ∧ enPassantFromHistory gs target2 = true then
                            [{ piece := p
                               fromSq := src
                               toSq := target2
                               isCapture := true
                               isEnPassant := true }]
                          else []
                      | none => [] := by
                simpa [hSqNeg, hEnemy, List.mem_append, stepFn] using hCapMem
              cases hSplit with
              | inl hIn =>
                  have hBaseProm :
                      ({ piece := p, fromSq := src, toSq := target, isCapture := true } : Move).promotion = none := by
                    simp
                  exact
                    promotionMoves_mem_promotion_eq_some_implies_mem_promotionTargets m
                      ({ piece := p, fromSq := src, toSq := target, isCapture := true } : Move)
                      pt hBaseProm hIn hEq
              | inr hAcc =>
                  -- Delegate to `df = 1` as above: if promotion exists, it must be enemy capture.
                  cases hSqPos : Movement.squareFromInts (src.fileInt + 1) (src.rankInt + dir) with
                  | none =>
                      cases (show False by simpa [hSqPos] using hAcc)
                  | some target2 =>
                      cases hEnemy2 : isEnemyNonKingAt board color target2 with
                      | true =>
                          have hIn : m ∈ promotionMoves { piece := p, fromSq := src, toSq := target2, isCapture := true } := by
                            simpa [hSqPos, hEnemy2] using hAcc
                          have hBaseProm :
                              ({ piece := p, fromSq := src, toSq := target2, isCapture := true } : Move).promotion = none := by
                            simp
                          exact
                            promotionMoves_mem_promotion_eq_some_implies_mem_promotionTargets m
                              ({ piece := p, fromSq := src, toSq := target2, isCapture := true } : Move)
                              pt hBaseProm hIn hEq
                      | false =>
                          by_cases hEP2 : gs.enPassantTarget = some target2 ∧ isEmpty board target2 ∧ enPassantFromHistory gs target2 = true
                          ·
                            have hEqEP :
                                m =
                                  { piece := p
                                    fromSq := src
                                    toSq := target2
                                    isCapture := true
                                    isEnPassant := true } := by
                              simpa [hSqPos, hEnemy2, hEP2] using hAcc
                            subst hEqEP
                            cases (show False by simpa using hEq)
                          · cases (show False by simpa [hSqPos, hEnemy2, hEP2] using hAcc)
          | false =>
              -- Either EP literal or empty accumulator; EP cannot have promotion.
              by_cases hEP : gs.enPassantTarget = some target ∧ isEmpty board target ∧ enPassantFromHistory gs target = true
              ·
                have hSplit :
                    m =
                        { piece := p
                          fromSq := src
                          toSq := target
                          isCapture := true
                          isEnPassant := true } ∨
                      m ∈ stepFn 1 [] := by
                  simpa [hSqNeg, hEnemy, hEP, List.mem_cons, stepFn] using hCapMem
                cases hSplit with
                | inl hEqEP =>
                    subst hEqEP
                    cases (show False by simpa using hEq)
                | inr hInAcc =>
                    -- Fall back to the `+1` side analysis.
                    dsimp [stepFn] at hInAcc
                    cases hSqPos : Movement.squareFromInts (src.fileInt + 1) (src.rankInt + dir) with
                    | none =>
                        cases (show False by simpa [hSqPos] using hInAcc)
                    | some target2 =>
                        cases hEnemy2 : isEnemyNonKingAt board color target2 with
                        | true =>
                            have hIn : m ∈ promotionMoves { piece := p, fromSq := src, toSq := target2, isCapture := true } := by
                              simpa [hSqPos, hEnemy2] using hInAcc
                            have hBaseProm :
                                ({ piece := p, fromSq := src, toSq := target2, isCapture := true } : Move).promotion = none := by
                              simp
                            exact
                              promotionMoves_mem_promotion_eq_some_implies_mem_promotionTargets m
                                ({ piece := p, fromSq := src, toSq := target2, isCapture := true } : Move)
                                pt hBaseProm hIn hEq
                        | false =>
                            by_cases hEP2 : gs.enPassantTarget = some target2 ∧ isEmpty board target2 ∧ enPassantFromHistory gs target2 = true
                            ·
                              have hEqEP :
                                  m =
                                    { piece := p
                                      fromSq := src
                                      toSq := target2
                                      isCapture := true
                                      isEnPassant := true } := by
                                simpa [hSqPos, hEnemy2, hEP2] using hInAcc
                              subst hEqEP
                              cases (show False by simpa using hEq)
                            · cases (show False by simpa [hSqPos, hEnemy2, hEP2] using hInAcc)
              ·
                have hAcc : m ∈ stepFn 1 [] := by
                  simpa [hSqNeg, hEnemy, hEP, stepFn] using hCapMem
                dsimp [stepFn] at hAcc
                cases hSqPos : Movement.squareFromInts (src.fileInt + 1) (src.rankInt + dir) with
                | none =>
                    cases (show False by simpa [hSqPos] using hAcc)
                | some target2 =>
                    cases hEnemy2 : isEnemyNonKingAt board color target2 with
                    | true =>
                        have hIn : m ∈ promotionMoves { piece := p, fromSq := src, toSq := target2, isCapture := true } := by
                          simpa [hSqPos, hEnemy2] using hAcc
                        have hBaseProm :
                            ({ piece := p, fromSq := src, toSq := target2, isCapture := true } : Move).promotion = none := by
                          simp
                        exact
                          promotionMoves_mem_promotion_eq_some_implies_mem_promotionTargets m
                            ({ piece := p, fromSq := src, toSq := target2, isCapture := true } : Move)
                            pt hBaseProm hIn hEq
                    | false =>
                        by_cases hEP2 : gs.enPassantTarget = some target2 ∧ isEmpty board target2 ∧ enPassantFromHistory gs target2 = true
                        ·
                          have hEqEP :
                              m =
                                { piece := p
                                  fromSq := src
                                  toSq := target2
                                  isCapture := true
                                  isEnPassant := true } := by
                            simpa [hSqPos, hEnemy2, hEP2] using hAcc
                          subst hEqEP
                          cases (show False by simpa using hEq)
                        · cases (show False by simpa [hSqPos, hEnemy2, hEP2] using hAcc)

theorem mem_pawn_pieceTargets_toPromotionRank_implies_promotion_isSome
    (gs : GameState) (src : Square) (p : Piece) (m : Move)
    (hValid : hasValidEPRank gs)
    (hPawn : p.pieceType = PieceType.Pawn)
    (hTargets : m ∈ pieceTargets gs src p)
    (hRank : m.toSq.rankNat = pawnPromotionRank p.color) :
    m.promotion.isSome = true := by
  -- Unfold pawn generator and split on forward vs capture lists, then on whether we are in a
  -- `promotionMoves base` branch. En passant targets are ruled out using `hasValidEPRank`.
  let board := gs.board
  let color := p.color
  let dir := Movement.pawnDirection color
  let oneStep := Movement.squareFromInts src.fileInt (src.rankInt + dir)
  let twoStep := Movement.squareFromInts src.fileInt (src.rankInt + 2 * dir)
  let forwardMoves : List Move :=
    match oneStep with
    | some target =>
        if isEmpty board target then
          let base : List Move := [{ piece := p, fromSq := src, toSq := target }]
          let doubleStep : List Move :=
            if src.rankNat = pawnStartRank color then
              match twoStep with
              | some target2 =>
                  if isEmpty board target2 then
                    [{ piece := p, fromSq := src, toSq := target2 }]
                  else []
              | none => []
            else []
          base ++ doubleStep
        else []
    | none => []
  let stepFn : Int → List Move → List Move :=
    fun df acc =>
      match Movement.squareFromInts (src.fileInt + df) (src.rankInt + dir) with
      | some target =>
          if isEnemyNonKingAt board color target then
            promotionMoves { piece := p, fromSq := src, toSq := target, isCapture := true } ++ acc
          else if gs.enPassantTarget = some target ∧ isEmpty board target ∧ enPassantFromHistory gs target = true then
            { piece := p, fromSq := src, toSq := target, isCapture := true, isEnPassant := true } :: acc
          else acc
      | none => acc
  let captureMoves : List Move := ([-1, 1] : List Int).foldr stepFn []
  have hMem' :
      m ∈ forwardMoves.foldr (fun mv acc => promotionMoves mv ++ acc) [] ++ captureMoves := by
    simpa [pieceTargets, hPawn, board, color, dir, oneStep, twoStep, forwardMoves, stepFn, captureMoves] using
      hTargets
  cases List.mem_append.1 hMem' with
  | inl hForward =>
      rcases (Chess.Parsing.List.mem_foldr_append_iff (f := promotionMoves) (b := m) forwardMoves).1 hForward with
        ⟨base, hBaseMem, hInProm⟩
      -- Forward bases have `promotion = none` by construction.
      have hBaseProm : base.promotion = none := by
        dsimp [forwardMoves] at hBaseMem
        cases hOne : oneStep with
        | none =>
            cases (show False by simpa [hOne] using hBaseMem)
        | some target =>
            cases hEmpty : isEmpty board target with
            | false =>
                cases (show False by simpa [hOne, hEmpty] using hBaseMem)
            | true =>
                have hMem'' :
                    base ∈ [{ piece := p, fromSq := src, toSq := target }] ++
                      (if src.rankNat = pawnStartRank color then
                          match twoStep with
                          | some target2 =>
                              if isEmpty board target2 then
                                [{ piece := p, fromSq := src, toSq := target2 }]
                              else []
                          | none => []
                        else []) := by
                  simpa [hOne, hEmpty] using hBaseMem
                cases List.mem_append.1 hMem'' with
                | inl hIn =>
                    have hEq : base = { piece := p, fromSq := src, toSq := target } := by
                      simpa using hIn
                    subst hEq
                    simp
                | inr hIn =>
                    by_cases hStart : src.rankNat = pawnStartRank color
                    · cases hTwo : twoStep with
                      | none =>
                          cases (show False by simpa [hStart, hTwo] using hIn)
                      | some target2 =>
                          cases hEmpty2 : isEmpty board target2 with
                          | false =>
                              cases (show False by simpa [hStart, hTwo, hEmpty2] using hIn)
                          | true =>
                              have hEq : base = { piece := p, fromSq := src, toSq := target2 } := by
                                simpa [hStart, hTwo, hEmpty2] using hIn
                              subst hEq
                              simp
                    · cases (show False by simpa [hStart] using hIn)
      have hBasePiece : base.piece = p := by
        dsimp [forwardMoves] at hBaseMem
        cases hOne : oneStep with
        | none =>
            cases (show False by simpa [hOne] using hBaseMem)
        | some target =>
            cases hEmpty : isEmpty board target with
            | false =>
                cases (show False by simpa [hOne, hEmpty] using hBaseMem)
            | true =>
                have hMem'' :
                    base ∈ [{ piece := p, fromSq := src, toSq := target }] ++
                      (if src.rankNat = pawnStartRank color then
                          match twoStep with
                          | some target2 =>
                              if isEmpty board target2 then
                                [{ piece := p, fromSq := src, toSq := target2 }]
                              else []
                          | none => []
                        else []) := by
                  simpa [hOne, hEmpty] using hBaseMem
                cases List.mem_append.1 hMem'' with
                | inl hIn =>
                    have hEq : base = { piece := p, fromSq := src, toSq := target } := by
                      simpa using hIn
                    subst hEq
                    simp
                | inr hIn =>
                    by_cases hStart : src.rankNat = pawnStartRank color
                    · cases hTwo : twoStep with
                      | none =>
                          cases (show False by simpa [hStart, hTwo] using hIn)
                      | some target2 =>
                          cases hEmpty2 : isEmpty board target2 with
                          | false =>
                              cases (show False by simpa [hStart, hTwo, hEmpty2] using hIn)
                          | true =>
                              have hEq : base = { piece := p, fromSq := src, toSq := target2 } := by
                                simpa [hStart, hTwo, hEmpty2] using hIn
                              subst hEq
                              simp
                    · cases (show False by simpa [hStart] using hIn)
      have hToEq : m.toSq = base.toSq := Chess.Parsing.promotionMoves_mem_toSq_eq m base hInProm
      have hPawnBase : base.piece.pieceType = PieceType.Pawn := by
        simpa [hBasePiece] using hPawn
      have hRankBase : base.toSq.rankNat = pawnPromotionRank base.piece.color := by
        have : base.toSq.rankNat = pawnPromotionRank p.color := by
          simpa [hToEq] using hRank
        simpa [hBasePiece] using this
      exact promotionMoves_mem_promotion_if_at_rank m base hBaseProm hPawnBase hRankBase hInProm
  | inr hCapture =>
      -- Unroll capture foldr into the two `df` branches.
      have hCapMem : m ∈ stepFn (-1) (stepFn 1 []) := by
        simpa [captureMoves, List.foldr] using hCapture
      -- Analyze `df = -1` branch.
      dsimp [stepFn] at hCapMem
      cases hSqNeg : Movement.squareFromInts (src.fileInt + (-1)) (src.rankInt + dir) with
      | none =>
          -- Must come from `df = 1` branch.
          have hAcc :
              m ∈
                match Movement.squareFromInts (src.fileInt + 1) (src.rankInt + dir) with
                | some target =>
                    if isEnemyNonKingAt board color target = true then
                      promotionMoves { piece := p, fromSq := src, toSq := target, isCapture := true }
                    else if gs.enPassantTarget = some target ∧ isEmpty board target ∧ enPassantFromHistory gs target = true then
                      [{ piece := p, fromSq := src, toSq := target, isCapture := true, isEnPassant := true }]
                    else []
                | none => [] := by
            simpa [hSqNeg, stepFn] using hCapMem
          cases hSqPos : Movement.squareFromInts (src.fileInt + 1) (src.rankInt + dir) with
          | none =>
              cases (show False by simpa [hSqPos] using hAcc)
          | some target =>
              cases hEnemy : isEnemyNonKingAt board color target with
              | true =>
                  have hInProm :
                      m ∈ promotionMoves { piece := p, fromSq := src, toSq := target, isCapture := true } := by
                    simpa [hSqPos, hEnemy] using hAcc
                  let base : Move := { piece := p, fromSq := src, toSq := target, isCapture := true }
                  have hBaseProm : base.promotion = none := by rfl
                  have hPawnBase : base.piece.pieceType = PieceType.Pawn := by simpa [base] using hPawn
                  have hToEq : m.toSq = base.toSq := Chess.Parsing.promotionMoves_mem_toSq_eq m base hInProm
                  have hRankBase : base.toSq.rankNat = pawnPromotionRank base.piece.color := by
                    have : base.toSq.rankNat = pawnPromotionRank p.color := by
                      simpa [hToEq] using hRank
                    simpa [base] using this
                  exact promotionMoves_mem_promotion_if_at_rank m base hBaseProm hPawnBase hRankBase hInProm
              | false =>
                  by_cases hEP : gs.enPassantTarget = some target ∧ isEmpty board target ∧ enPassantFromHistory gs target = true
                  · have hEq :
                        m =
                          { piece := p
                            fromSq := src
                            toSq := target
                            isCapture := true
                            isEnPassant := true } := by
                      simpa [hSqPos, hEnemy, hEP] using hAcc
                    subst hEq
                    -- Contradict promotion rank using `hasValidEPRank`.
                    have hValid' : hasValidEPRank gs := hValid
                    have hRankEP : target.rankNat = 2 ∨ target.rankNat = 5 := by
                      simpa [hasValidEPRank, hEP.1] using hValid'
                    have hNotPromo : target.rankNat ≠ pawnPromotionRank p.color :=
                      validEPRank_not_promotion target p.color hRankEP
                    have : False := by
                      exact hNotPromo (by simpa using hRank)
                    cases this
                  · cases (show False by simpa [hSqPos, hEnemy, hEP] using hAcc)
      | some target =>
          cases hEnemy : isEnemyNonKingAt board color target with
          | true =>
              -- Either from this promotion list or from `df = 1`.
              have hSplit :
                  m ∈ promotionMoves { piece := p, fromSq := src, toSq := target, isCapture := true } ∨
                    m ∈
                      match Movement.squareFromInts (src.fileInt + 1) (src.rankInt + dir) with
                      | some target2 =>
                          if isEnemyNonKingAt board color target2 = true then
                            promotionMoves { piece := p, fromSq := src, toSq := target2, isCapture := true }
                          else if gs.enPassantTarget = some target2 ∧ isEmpty board target2 ∧ enPassantFromHistory gs target2 = true then
                            [{ piece := p
                               fromSq := src
                               toSq := target2
                               isCapture := true
                               isEnPassant := true }]
                          else []
                      | none => [] := by
                simpa [hSqNeg, hEnemy, List.mem_append, stepFn] using hCapMem
              cases hSplit with
              | inl hInProm =>
                  let base : Move := { piece := p, fromSq := src, toSq := target, isCapture := true }
                  have hBaseProm : base.promotion = none := by rfl
                  have hPawnBase : base.piece.pieceType = PieceType.Pawn := by simpa [base] using hPawn
                  have hToEq : m.toSq = base.toSq := Chess.Parsing.promotionMoves_mem_toSq_eq m base hInProm
                  have hRankBase : base.toSq.rankNat = pawnPromotionRank base.piece.color := by
                    have : base.toSq.rankNat = pawnPromotionRank p.color := by
                      simpa [hToEq] using hRank
                    simpa [base] using this
                  exact promotionMoves_mem_promotion_if_at_rank m base hBaseProm hPawnBase hRankBase hInProm
              | inr hAcc =>
                  cases hSqPos : Movement.squareFromInts (src.fileInt + 1) (src.rankInt + dir) with
                  | none =>
                      cases (show False by simpa [hSqPos] using hAcc)
                  | some target2 =>
                      cases hEnemy2 : isEnemyNonKingAt board color target2 with
                      | true =>
                          have hInProm :
                              m ∈ promotionMoves { piece := p, fromSq := src, toSq := target2, isCapture := true } := by
                            simpa [hSqPos, hEnemy2] using hAcc
                          let base : Move := { piece := p, fromSq := src, toSq := target2, isCapture := true }
                          have hBaseProm : base.promotion = none := by rfl
                          have hPawnBase : base.piece.pieceType = PieceType.Pawn := by simpa [base] using hPawn
                          have hToEq : m.toSq = base.toSq := Chess.Parsing.promotionMoves_mem_toSq_eq m base hInProm
                          have hRankBase : base.toSq.rankNat = pawnPromotionRank base.piece.color := by
                            have : base.toSq.rankNat = pawnPromotionRank p.color := by
                              simpa [hToEq] using hRank
                            simpa [base] using this
                          exact promotionMoves_mem_promotion_if_at_rank m base hBaseProm hPawnBase hRankBase hInProm
                      | false =>
                          by_cases hEP2 : gs.enPassantTarget = some target2 ∧ isEmpty board target2 ∧ enPassantFromHistory gs target2 = true
                          · have hEq :
                                m =
                                  { piece := p
                                    fromSq := src
                                    toSq := target2
                                    isCapture := true
                                    isEnPassant := true } := by
                              simpa [hSqPos, hEnemy2, hEP2] using hAcc
                            subst hEq
                            have hRankEP : target2.rankNat = 2 ∨ target2.rankNat = 5 := by
                              simpa [hasValidEPRank, hEP2.1] using hValid
                            have hNotPromo : target2.rankNat ≠ pawnPromotionRank p.color :=
                              validEPRank_not_promotion target2 p.color hRankEP
                            have : False := by
                              exact hNotPromo (by simpa using hRank)
                            cases this
                          · cases (show False by simpa [hSqPos, hEnemy2, hEP2] using hAcc)
          | false =>
              by_cases hEP : gs.enPassantTarget = some target ∧ isEmpty board target ∧ enPassantFromHistory gs target = true
              · -- EP literal or accumulator: EP literal contradicts promotion rank.
                have hSplit :
                    m =
                        { piece := p
                          fromSq := src
                          toSq := target
                          isCapture := true
                          isEnPassant := true } ∨
                      m ∈ stepFn 1 [] := by
                  simpa [hSqNeg, hEnemy, hEP, stepFn] using hCapMem
                cases hSplit with
                | inl hEq =>
                    subst hEq
                    have hRankEP : target.rankNat = 2 ∨ target.rankNat = 5 := by
                      simpa [hasValidEPRank, hEP.1] using hValid
                    have hNotPromo : target.rankNat ≠ pawnPromotionRank p.color :=
                      validEPRank_not_promotion target p.color hRankEP
                    have : False := by
                      exact hNotPromo (by simpa using hRank)
                    cases this
                | inr hAcc =>
                    -- Must come from `df = 1` branch, handled similarly.
                    dsimp [stepFn] at hAcc
                    cases hSqPos : Movement.squareFromInts (src.fileInt + 1) (src.rankInt + dir) with
                    | none =>
                        cases (show False by simpa [hSqPos] using hAcc)
                    | some target2 =>
                        cases hEnemy2 : isEnemyNonKingAt board color target2 with
                        | true =>
                            have hInProm :
                                m ∈ promotionMoves { piece := p, fromSq := src, toSq := target2, isCapture := true } := by
                              simpa [hSqPos, hEnemy2] using hAcc
                            let base : Move := { piece := p, fromSq := src, toSq := target2, isCapture := true }
                            have hBaseProm : base.promotion = none := by rfl
                            have hPawnBase : base.piece.pieceType = PieceType.Pawn := by simpa [base] using hPawn
                            have hToEq : m.toSq = base.toSq := Chess.Parsing.promotionMoves_mem_toSq_eq m base hInProm
                            have hRankBase : base.toSq.rankNat = pawnPromotionRank base.piece.color := by
                              have : base.toSq.rankNat = pawnPromotionRank p.color := by
                                simpa [hToEq] using hRank
                              simpa [base] using this
                            exact promotionMoves_mem_promotion_if_at_rank m base hBaseProm hPawnBase hRankBase hInProm
                        | false =>
                            by_cases hEP2 : gs.enPassantTarget = some target2 ∧ isEmpty board target2 ∧ enPassantFromHistory gs target2 = true
                            · have hEq :
                                  m =
                                    { piece := p
                                      fromSq := src
                                      toSq := target2
                                      isCapture := true
                                      isEnPassant := true } := by
                                simpa [hSqPos, hEnemy2, hEP2] using hAcc
                              subst hEq
                              have hRankEP : target2.rankNat = 2 ∨ target2.rankNat = 5 := by
                                simpa [hasValidEPRank, hEP2.1] using hValid
                              have hNotPromo : target2.rankNat ≠ pawnPromotionRank p.color :=
                                validEPRank_not_promotion target2 p.color hRankEP
                              have : False := by
                                exact hNotPromo (by simpa using hRank)
                              cases this
                            · cases (show False by simpa [hSqPos, hEnemy2, hEP2] using hAcc)
              · -- Only accumulator.
                have : m ∈ stepFn 1 [] := by
                  simpa [hSqNeg, hEnemy, hEP, stepFn] using hCapMem
                dsimp [stepFn] at this
                cases hSqPos : Movement.squareFromInts (src.fileInt + 1) (src.rankInt + dir) with
                | none =>
                    cases (show False by simpa [hSqPos] using this)
                | some target2 =>
                    cases hEnemy2 : isEnemyNonKingAt board color target2 with
                    | true =>
                        have hInProm :
                            m ∈ promotionMoves { piece := p, fromSq := src, toSq := target2, isCapture := true } := by
                          simpa [hSqPos, hEnemy2] using this
                        let base : Move := { piece := p, fromSq := src, toSq := target2, isCapture := true }
                        have hBaseProm : base.promotion = none := by rfl
                        have hPawnBase : base.piece.pieceType = PieceType.Pawn := by simpa [base] using hPawn
                        have hToEq : m.toSq = base.toSq := Chess.Parsing.promotionMoves_mem_toSq_eq m base hInProm
                        have hRankBase : base.toSq.rankNat = pawnPromotionRank base.piece.color := by
                          have : base.toSq.rankNat = pawnPromotionRank p.color := by
                            simpa [hToEq] using hRank
                          simpa [base] using this
                        exact promotionMoves_mem_promotion_if_at_rank m base hBaseProm hPawnBase hRankBase hInProm
                    | false =>
                        by_cases hEP2 : gs.enPassantTarget = some target2 ∧ isEmpty board target2 ∧ enPassantFromHistory gs target2 = true
                        · have hEq :
                              m =
                                { piece := p
                                  fromSq := src
                                  toSq := target2
                                  isCapture := true
                                  isEnPassant := true } := by
                            simpa [hSqPos, hEnemy2, hEP2] using this
                          subst hEq
                          have hRankEP : target2.rankNat = 2 ∨ target2.rankNat = 5 := by
                            simpa [hasValidEPRank, hEP2.1] using hValid
                          have hNotPromo : target2.rankNat ≠ pawnPromotionRank p.color :=
                            validEPRank_not_promotion target2 p.color hRankEP
                          have : False := by
                            exact hNotPromo (by simpa using hRank)
                          cases this
                        · cases (show False by simpa [hSqPos, hEnemy2, hEP2] using this)

theorem mem_allLegalMoves_promotion_isSome_implies_pawn_and_rank (gs : GameState) (m : Move) :
    m ∈ allLegalMoves gs →
    m.promotion.isSome →
    m.piece.pieceType = PieceType.Pawn ∧
      m.toSq.rankNat = pawnPromotionRank m.piece.color := by
  intro hMem hSome
  have hSomeBool : m.promotion.isSome = true := by
    simpa using hSome
  -- Peel `allLegalMoves` to find the generating piece.
  unfold allLegalMoves at hMem
  let pins := pinnedSquares gs gs.toMove
  have hFold :
      m ∈ (Square.all).foldr (fun sq acc => legalMovesForCached gs sq pins ++ acc) [] := by
    simpa [allSquares, pins] using hMem
  have hExists :=
    (Chess.Parsing.List.mem_foldr_append_iff (f := fun sq => legalMovesForCached gs sq pins) (b := m) Square.all).1
      hFold
  rcases hExists with ⟨sq, _hSqMem, hInCached⟩
  unfold legalMovesForCached at hInCached
  cases hBoard : gs.board sq with
  | none =>
      simp [hBoard] at hInCached
  | some p =>
      by_cases hTurn : p.color ≠ gs.toMove
      · simp [hBoard, hTurn] at hInCached
      · simp [hBoard, hTurn] at hInCached
        rcases hInCached with ⟨hInTargets, _hSafe, _hPin⟩
        cases hpt : p.pieceType with
        | Pawn =>
            have hPawnGen : p.pieceType = PieceType.Pawn := by simp [hpt]
            have hPieceEq : m.piece = p :=
              (Chess.Parsing.mem_pawn_pieceTargets_piece_fromSq gs sq p m hPawnGen hInTargets).1
            have hToPromo :=
              mem_pawn_pieceTargets_promotion_isSome_implies_toPromotionRank
                gs sq p m hPawnGen hInTargets hSomeBool
            refine ⟨?_, ?_⟩
            · simp [hPieceEq, hpt]
            · simpa [hPieceEq] using hToPromo
        | King =>
            -- King moves (including castling) never set `promotion`.
            have hMemKing :
                m ∈
                  (Movement.kingTargets sq).filterMap (fun target =>
                      if destinationFriendlyFree gs { piece := p, fromSq := sq, toSq := target } then
                        match gs.board target with
                        | some _ => some { piece := p, fromSq := sq, toSq := target, isCapture := true }
                        | none => some { piece := p, fromSq := sq, toSq := target }
                      else none) ++
                    ([castleMoveIfLegal gs true, castleMoveIfLegal gs false]).filterMap id := by
              simpa [pieceTargets, hpt] using hInTargets
            cases List.mem_append.1 hMemKing with
            | inl hStd =>
                have : m.promotion = none :=
                  mem_standardFilterMap_promotion_none gs sq p (Movement.kingTargets sq) m hStd
                cases (show False by simpa [this] using hSomeBool)
            | inr hCastles =>
                rcases (List.mem_filterMap.1 hCastles) with ⟨opt, hOptMem, hOptEq⟩
                have hOptSome : opt = some m := by simpa using hOptEq
                have hOpt :
                    opt = castleMoveIfLegal gs true ∨ opt = castleMoveIfLegal gs false := by
                  simpa using hOptMem
                cases hOpt with
                | inl hEqOpt =>
                    subst hEqOpt
                    have hCM : castleMoveIfLegal gs true = some m := by simp [hOptSome]
                    have : m.promotion = none := castleMoveIfLegal_promotion_none gs true m hCM
                    cases (show False by simpa [this] using hSomeBool)
                | inr hEqOpt =>
                    subst hEqOpt
                    have hCM : castleMoveIfLegal gs false = some m := by simp [hOptSome]
                    have : m.promotion = none := castleMoveIfLegal_promotion_none gs false m hCM
                    cases (show False by simpa [this] using hSomeBool)
        | Queen =>
            have hMemQ :
                m ∈
                  slidingTargets gs sq p
                    [(1, 0), (-1, 0), (0, 1), (0, -1), (1, 1), (-1, -1), (1, -1), (-1, 1)] := by
              simpa [pieceTargets, hpt] using hInTargets
            have : m.promotion = none := mem_slidingTargets_promotion_none gs sq p _ m hMemQ
            cases (show False by simpa [this] using hSomeBool)
        | Rook =>
            have hMemR :
                m ∈ slidingTargets gs sq p [(1, 0), (-1, 0), (0, 1), (0, -1)] := by
              simpa [pieceTargets, hpt] using hInTargets
            have : m.promotion = none := mem_slidingTargets_promotion_none gs sq p _ m hMemR
            cases (show False by simpa [this] using hSomeBool)
        | Bishop =>
            have hMemB :
                m ∈ slidingTargets gs sq p [(1, 1), (-1, -1), (1, -1), (-1, 1)] := by
              simpa [pieceTargets, hpt] using hInTargets
            have : m.promotion = none := mem_slidingTargets_promotion_none gs sq p _ m hMemB
            cases (show False by simpa [this] using hSomeBool)
        | Knight =>
            have hMemN :
                m ∈
                  (Movement.knightTargets sq).filterMap (fun target =>
                      if destinationFriendlyFree gs { piece := p, fromSq := sq, toSq := target } then
                        match gs.board target with
                        | some _ => some { piece := p, fromSq := sq, toSq := target, isCapture := true }
                        | none => some { piece := p, fromSq := sq, toSq := target }
                      else none) := by
              simpa [pieceTargets, hpt] using hInTargets
            have : m.promotion = none :=
              mem_standardFilterMap_promotion_none gs sq p (Movement.knightTargets sq) m hMemN
            cases (show False by simpa [this] using hSomeBool)

theorem mem_allLegalMoves_pawn_toPromotionRank_implies_promotion_isSome (gs : GameState) (m : Move) :
    hasValidEPRank gs →
    m ∈ allLegalMoves gs →
    m.piece.pieceType = PieceType.Pawn →
    m.toSq.rankNat = pawnPromotionRank m.piece.color →
    m.promotion.isSome := by
  intro hValid hMem hPawn hRank
  have hNoCastle : m.isCastle = false := by
    cases hIs : m.isCastle with
    | false => simp [hIs]
    | true =>
        have hKing : m.piece.pieceType = PieceType.King :=
          mem_allLegalMoves_isCastle_implies_king gs m hMem (by simp [hIs])
        have : False := by
          have : (PieceType.Pawn : PieceType) = PieceType.King := by
            simpa [hPawn] using hKing.symm
          cases this
        cases this
  -- Peel `allLegalMoves` to find the generating square and piece.
  unfold allLegalMoves at hMem
  let pins := pinnedSquares gs gs.toMove
  have hFold :
      m ∈ (Square.all).foldr (fun sq acc => legalMovesForCached gs sq pins ++ acc) [] := by
    simpa [allSquares, pins] using hMem
  have hExists :=
    (Chess.Parsing.List.mem_foldr_append_iff (f := fun sq => legalMovesForCached gs sq pins) (b := m) Square.all).1
      hFold
  rcases hExists with ⟨sq, _hSqMem, hInCached⟩
  unfold legalMovesForCached at hInCached
  cases hBoard : gs.board sq with
  | none =>
      simp [hBoard] at hInCached
  | some p =>
      by_cases hTurn : p.color ≠ gs.toMove
      · simp [hBoard, hTurn] at hInCached
      · simp [hBoard, hTurn] at hInCached
        rcases hInCached with ⟨hInTargets, _hSafe, _hPin⟩
        have hPieceFrom : m.piece = p ∧ m.fromSq = sq :=
          Chess.Parsing.mem_pieceTargets_piece_fromSq_of_not_castle gs sq p m hInTargets hNoCastle
        have hPawnGen : p.pieceType = PieceType.Pawn := by
          simpa [hPieceFrom.1] using hPawn
        have hRankGen : m.toSq.rankNat = pawnPromotionRank p.color := by
          simpa [hPieceFrom.1] using hRank
        have hSomeBool :
            m.promotion.isSome = true :=
          mem_pawn_pieceTargets_toPromotionRank_implies_promotion_isSome
            gs sq p m hValid hPawnGen hInTargets hRankGen
        simpa using hSomeBool

end Rules
end Chess
