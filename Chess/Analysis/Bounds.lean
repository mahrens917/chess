import Chess.Analysis.MinimaxSpec

namespace Chess
namespace Analysis

open Rules

def maxMaterialNat : Nat :=
  64 * 900

theorem squareAll_length : Square.all.length = 64 := by
  native_decide

theorem pieceValue_natAbs_le (pt : PieceType) : (pieceValue pt).natAbs ≤ 900 := by
  cases pt <;> native_decide

def materialContrib (b : Board) (sq : Square) : Int :=
  match b sq with
  | none => 0
  | some p =>
      let v := pieceValue p.pieceType
      match p.color with
      | Color.White => v
      | Color.Black => -v

theorem materialContrib_natAbs_le (b : Board) (sq : Square) :
    (materialContrib b sq).natAbs ≤ 900 := by
  unfold materialContrib
  cases h : b sq with
  | none =>
      simp
  | some p =>
      cases hColor : p.color <;> simp [hColor, pieceValue_natAbs_le, Int.natAbs_neg]

theorem natAbs_foldl_add_le
    (xs : List α) (f : α → Int) (k : Nat)
    (h : ∀ x, x ∈ xs → (f x).natAbs ≤ k) :
    (xs.foldl (fun acc x => acc + f x) 0).natAbs ≤ xs.length * k := by
  -- Auxiliary: for this additive fold, left-addition commutes with folding.
  have foldl_add_left (xs : List α) (a b : Int) :
      xs.foldl (fun acc x => acc + f x) (a + b) =
        a + xs.foldl (fun acc x => acc + f x) b := by
    induction xs generalizing b with
    | nil =>
        simp
    | cons x xs ih =>
        simp [List.foldl, ih, Int.add_assoc]
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      have hHead : (f x).natAbs ≤ k := h x (by simp)
      have hTail : ∀ x', x' ∈ xs → (f x').natAbs ≤ k := by
        intro x' hx'
        exact h x' (by simp [hx'])
      have ih0 : (xs.foldl (fun acc x => acc + f x) 0).natAbs ≤ xs.length * k := ih hTail
      -- Unfold one step and apply the triangle inequality.
      have hAbs :
          (xs.foldl (fun acc x => acc + f x) (f x)).natAbs ≤
            (f x).natAbs + (xs.foldl (fun acc x => acc + f x) 0).natAbs := by
        have hFold :
            xs.foldl (fun acc x => acc + f x) (f x) =
              (f x) + xs.foldl (fun acc x => acc + f x) 0 := by
          simpa [Int.zero_add] using (foldl_add_left xs (f x) 0)
        simpa [hFold] using
          (Int.natAbs_add_le (f x) (xs.foldl (fun acc x => acc + f x) 0))
      have hAbs' :
          (xs.foldl (fun acc x => acc + f x) (f x)).natAbs ≤
            (f x).natAbs + xs.length * k := by
        exact Nat.le_trans hAbs (Nat.add_le_add_left ih0 _)
      -- Convert to the desired `(xs.length + 1) * k` bound.
      have hMul : (xs.length + 1) * k = xs.length * k + k := by
        simpa using (Nat.succ_mul xs.length k)
      have hSwap : (f x).natAbs + xs.length * k ≤ xs.length * k + k := by
        -- Use `hHead` and commute the addition.
        have : (f x).natAbs + xs.length * k ≤ k + xs.length * k := Nat.add_le_add_right hHead _
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
      have : (xs.foldl (fun acc x => acc + f x) (f x)).natAbs ≤ (xs.length + 1) * k := by
        exact Nat.le_trans (Nat.le_trans hAbs' hSwap) (by simp [hMul, Nat.add_comm])
      simpa [List.foldl, Int.zero_add] using this

theorem materialScore_natAbs_le (b : Board) :
    (materialScore b).natAbs ≤ maxMaterialNat := by
  have hFold :
      materialScore b =
        Square.all.foldl (fun acc sq => acc + materialContrib b sq) 0 := by
    unfold materialScore
    -- Rewrite the fold step to “add a signed contribution”.
    have hFun :
        (fun acc sq =>
            match (fun sq => b.get sq) sq with
            | none => acc
            | some p =>
                have v := pieceValue p.pieceType
                match p.color with
                | Color.White => acc + v
                | Color.Black => acc - v) =
          (fun acc sq => acc + materialContrib b sq) := by
      funext acc sq
      cases h : b.get sq with
      | none =>
          simp [materialContrib, h]
      | some p =>
          cases hColor : p.color <;>
            simp [materialContrib, h, hColor, Int.sub_eq_add_neg]
    -- Replace the fold step function via congruence.
    simpa using congrArg (fun f => List.foldl f 0 Square.all) hFun
  -- Apply the generic fold bound with `k = 900`.
  have hBound :
      (Square.all.foldl (fun acc sq => acc + materialContrib b sq) 0).natAbs ≤
        Square.all.length * 900 := by
    refine natAbs_foldl_add_le (xs := Square.all) (f := fun sq => materialContrib b sq) (k := 900) ?_
    intro sq hMem
    exact materialContrib_natAbs_le b sq
  -- Close by rewriting `Square.all.length` to 64.
  have : Square.all.length * 900 = maxMaterialNat := by
    simp [maxMaterialNat, squareAll_length]
  simpa [hFold, this] using hBound

theorem staticEval_natAbs_le (gs : GameState) :
    (staticEval gs).natAbs ≤ maxMaterialNat := by
  unfold staticEval
  cases gs.toMove with
  | White =>
      simpa using materialScore_natAbs_le gs.board
  | Black =>
      -- natAbs(-x) = natAbs(x)
      simpa [Int.natAbs_neg] using materialScore_natAbs_le gs.board

theorem neg_ofNat_le_ofNat (n : Nat) : -(Int.ofNat n) ≤ (Int.ofNat n) := by
  have hn : 0 ≤ (Int.ofNat n) := Int.natCast_nonneg n
  have h1 : -(Int.ofNat n) ≤ 0 := Int.neg_nonpos_of_nonneg hn
  exact Int.le_trans h1 hn

theorem neg_ofNat_natAbs_le (a : Int) : -(Int.ofNat a.natAbs) ≤ a := by
  cases Int.natAbs_eq a with
  | inl hEq =>
      -- `a = ↑a.natAbs`
      rw [hEq]
      exact neg_ofNat_le_ofNat a.natAbs
  | inr hEq =>
      -- `a = -↑a.natAbs`
      rw [hEq]
      simp

theorem le_of_natAbs_le (a : Int) (n : Nat) (h : a.natAbs ≤ n) : a ≤ (Int.ofNat n) := by
  have h1 : a ≤ (Int.ofNat a.natAbs) := by
    simpa using (Int.le_natAbs (a := a))
  have h2 : (Int.ofNat a.natAbs) ≤ (Int.ofNat n) := (Int.ofNat_le).2 h
  exact Int.le_trans h1 h2

theorem neg_le_of_natAbs_le (a : Int) (n : Nat) (h : a.natAbs ≤ n) : -(Int.ofNat n) ≤ a := by
  have hNat : (Int.ofNat a.natAbs) ≤ (Int.ofNat n) := (Int.ofNat_le).2 h
  have hNeg : -(Int.ofNat n) ≤ -(Int.ofNat a.natAbs) := Int.neg_le_neg hNat
  have hAbs : -(Int.ofNat a.natAbs) ≤ a := neg_ofNat_natAbs_le a
  exact Int.le_trans hNeg hAbs

theorem staticEval_le_maxMaterial (gs : GameState) : staticEval gs ≤ (Int.ofNat maxMaterialNat) := by
  exact le_of_natAbs_le (staticEval gs) maxMaterialNat (staticEval_natAbs_le gs)

theorem maxMaterial_le_mateScore : (Int.ofNat maxMaterialNat) ≤ mateScore := by
  native_decide

theorem staticEval_le_mateScore (gs : GameState) : staticEval gs ≤ mateScore := by
  exact Int.le_trans (staticEval_le_maxMaterial gs) maxMaterial_le_mateScore

theorem staticEval_ge_neg_mateScore (gs : GameState) : -mateScore ≤ staticEval gs := by
  have : -(Int.ofNat maxMaterialNat) ≤ staticEval gs :=
    neg_le_of_natAbs_le (staticEval gs) maxMaterialNat (staticEval_natAbs_le gs)
  have hMax : -mateScore ≤ -(Int.ofNat maxMaterialNat) := by
    exact Int.neg_le_neg maxMaterial_le_mateScore
  exact Int.le_trans hMax this

theorem minimaxValue_zero_bounds (gs : GameState) :
    -mateScore ≤ minimaxValue 0 gs ∧ minimaxValue 0 gs ≤ mateScore := by
  -- First, show terminal evaluations are bounded.
  have terminal_bounds (v : Int) (hTerm : terminalValue? gs = some v) :
      -mateScore ≤ v ∧ v ≤ mateScore := by
    unfold terminalValue? at hTerm
    cases hMate : isCheckmate gs with
    | true =>
        -- Checkmate: value is `-mateScore`.
        have hTerm' : some (-mateScore) = some v := by
          simpa [hMate] using hTerm
        have hv : v = -mateScore := (Option.some.inj hTerm').symm
        constructor
        · simp [hv]
        ·
          simp [hv]
          native_decide
    | false =>
        -- Not checkmate: match on `interpretResult`, then possibly `isStalemate`.
        simp [hMate] at hTerm
        cases hRes : interpretResult gs with
        | whiteWin =>
            -- `some (winnerColorScore ..) = some v`
            have hv : v = winnerColorScore gs.toMove Color.White := by
              exact (Option.some.inj (by simpa [hRes] using hTerm)).symm
            by_cases hEq : gs.toMove = Color.White <;>
              simp [winnerColorScore, hv, hEq] <;> native_decide
        | blackWin =>
            have hv : v = winnerColorScore gs.toMove Color.Black := by
              exact (Option.some.inj (by simpa [hRes] using hTerm)).symm
            by_cases hEq : gs.toMove = Color.Black <;>
              simp [winnerColorScore, hv, hEq] <;> native_decide
        | drawAuto _ =>
            have hv : v = 0 := (Option.some.inj (by simpa [hRes] using hTerm)).symm
            constructor <;> simpa [hv] using (by native_decide : (-mateScore ≤ (0 : Int) ∧ (0 : Int) ≤ mateScore))
        | drawClaim _ =>
            have hv : v = 0 := (Option.some.inj (by simpa [hRes] using hTerm)).symm
            constructor <;> simpa [hv] using (by native_decide : (-mateScore ≤ (0 : Int) ∧ (0 : Int) ≤ mateScore))
        | ongoing =>
            -- `if isStalemate then some 0 else none = some v`
            have hOng : (if isStalemate gs then some 0 else none) = some v := by
              simpa [hRes] using hTerm
            cases hStale : isStalemate gs with
            | false =>
                have : none = some v := by
                  have hOng' := hOng
                  simp [hStale] at hOng'
                cases this
            | true =>
                have hOng' : some 0 = some v := by
                  simpa [hStale] using hOng
                have hv : v = 0 := (Option.some.inj hOng').symm
                constructor <;> simpa [hv] using (by native_decide : (-mateScore ≤ (0 : Int) ∧ (0 : Int) ≤ mateScore))
  cases hTerm : terminalValue? gs with
  | some v =>
      have := terminal_bounds v hTerm
      simpa [minimaxValue, hTerm] using this
  | none =>
      constructor
      · simpa [minimaxValue, hTerm] using staticEval_ge_neg_mateScore gs
      · simpa [minimaxValue, hTerm] using staticEval_le_mateScore gs

theorem terminalValue?_bounds (gs : GameState) (v : Int) (h : terminalValue? gs = some v) :
    -mateScore ≤ v ∧ v ≤ mateScore := by
  -- Reuse the internal argument from `minimaxValue_zero_bounds`.
  have := minimaxValue_zero_bounds gs
  -- If `terminalValue? = some v`, then `minimaxValue 0 = v`.
  have hv : minimaxValue 0 gs = v := by
    simp [minimaxValue, h]  -- reduces to `v`
  -- Transport the bounds across the equality.
  constructor
  · have : -mateScore ≤ minimaxValue 0 gs := this.1
    simpa [hv] using this
  · have : minimaxValue 0 gs ≤ mateScore := this.2
    simpa [hv] using this

end Analysis
end Chess
