import Chess.Analysis.Baseline

namespace Chess
namespace Analysis

open Rules

def pvLegal : GameState → List Move → Prop
  | _gs, [] => True
  | gs, m :: ms =>
      m ∈ allLegalMoves gs ∧
        pvLegal (GameState.playMove gs m) ms

theorem pvLegal_nil (gs : GameState) : pvLegal gs [] := by
  simp [pvLegal]

theorem pvLegal_cons (gs : GameState) (m : Move) (ms : List Move) :
    pvLegal gs (m :: ms) ↔ m ∈ allLegalMoves gs ∧ pvLegal (GameState.playMove gs m) ms := by
  simp [pvLegal]

theorem pvLegal_foldl_step (d : Nat) (gs : GameState) (moves : List Move) (best : PVResult) :
    (∀ {m}, m ∈ moves → m ∈ allLegalMoves gs) →
    pvLegal gs best.pv →
    (∀ m, m ∈ moves → pvLegal (GameState.playMove gs m) (negamaxPV d (GameState.playMove gs m)).pv) →
    pvLegal gs
      ((moves.foldl
          (fun best m =>
            let child := GameState.playMove gs m
            let childRes := negamaxPV d child
            let score := -childRes.value
            if score > best.value then
              { value := score, pv := m :: childRes.pv }
            else
              best)
          best).pv) := by
  intro hSubset hBest hChild
  induction moves generalizing best with
  | nil =>
      simpa using hBest
  | cons m ms ih =>
      have hSubset' : ∀ {m'}, m' ∈ ms → m' ∈ allLegalMoves gs := by
        intro m' hm'
        exact hSubset (by simp [hm'])
      have hChild' :
          ∀ m', m' ∈ ms → pvLegal (GameState.playMove gs m') (negamaxPV d (GameState.playMove gs m')).pv := by
        intro m' hm'
        exact hChild m' (by simp [hm'])
      let step : PVResult → Move → PVResult :=
        fun best m =>
          let child := GameState.playMove gs m
          let childRes := negamaxPV d child
          let score := -childRes.value
          if score > best.value then
            { value := score, pv := m :: childRes.pv }
          else
            best
      have hMoveMem : m ∈ allLegalMoves gs :=
        hSubset (by simp)
      let child := GameState.playMove gs m
      let childRes := negamaxPV d child
      let score : Int := -childRes.value
      have hChildLegal0 : pvLegal child childRes.pv := by
        simpa [child, childRes] using hChild m (by simp)
      have hChildLegal : pvLegal (GameState.playMove gs m) childRes.pv := by
        simpa [child] using hChildLegal0
      by_cases hBetter : score > best.value
      ·
        have hBest' : pvLegal gs (m :: childRes.pv) := by
          simp [pvLegal, hMoveMem, hChildLegal]
        have hStepEq : step best m = { value := score, pv := m :: childRes.pv } := by
          simp [step, child, childRes, score, hBetter]
        -- Apply IH to the tail with the updated accumulator.
        simpa [List.foldl, step, hStepEq] using
          (ih (best := { value := score, pv := m :: childRes.pv }) hSubset' hBest' hChild')
      ·
        have hStepEq : step best m = best := by
          simp [step, child, childRes, score, hBetter]
        simpa [List.foldl, step, hStepEq] using
          (ih (best := best) hSubset' hBest hChild')

theorem pvLegal_negamaxPV (depth : Nat) (gs : GameState) :
    pvLegal gs (negamaxPV depth gs).pv := by
  induction depth generalizing gs with
  | zero =>
      cases hTerm : terminalValue? gs with
      | some v =>
          simp [negamaxPV, hTerm, pvLegal]
      | none =>
          simp [negamaxPV, hTerm, pvLegal]
  | succ d ih =>
      cases hTerm : terminalValue? gs with
      | some v =>
          simp [negamaxPV, hTerm, pvLegal]
      | none =>
          have hSubset : ∀ {m}, m ∈ allLegalMoves gs → m ∈ allLegalMoves gs := by
            intro m hm; exact hm
          have hChild : ∀ m, m ∈ allLegalMoves gs →
              pvLegal (GameState.playMove gs m) (negamaxPV d (GameState.playMove gs m)).pv := by
            intro m _hm
            exact ih (gs := GameState.playMove gs m)
          have hInit : pvLegal gs ([] : List Move) := pvLegal_nil gs
          simpa [negamaxPV, hTerm] using
            (pvLegal_foldl_step (d := d) (gs := gs) (moves := allLegalMoves gs) (best := { value := -mateScore - 1, pv := [] })
              hSubset hInit hChild)

theorem pvLegal_negamaxPV_head (depth : Nat) (gs : GameState) (m : Move) (ms : List Move) :
    (negamaxPV depth gs).pv = m :: ms →
    m ∈ allLegalMoves gs := by
  intro hEq
  have h := pvLegal_negamaxPV depth gs
  have h' : m ∈ allLegalMoves gs ∧ pvLegal (GameState.playMove gs m) ms := by
    simpa [pvLegal, hEq] using h
  exact h'.1

theorem pvLength_foldl_step (d : Nat) (gs : GameState) (moves : List Move) (best : PVResult) :
    best.pv.length ≤ d.succ →
    (∀ m, m ∈ moves → (negamaxPV d (GameState.playMove gs m)).pv.length ≤ d) →
    ((moves.foldl
        (fun best m =>
          let child := GameState.playMove gs m
          let childRes := negamaxPV d child
          let score := -childRes.value
          if score > best.value then
            { value := score, pv := m :: childRes.pv }
          else
            best)
        best).pv).length ≤ d.succ := by
  intro hBestLen hChildLen
  induction moves generalizing best with
  | nil =>
      simpa using hBestLen
  | cons m ms ih =>
      let child := GameState.playMove gs m
      let childRes := negamaxPV d child
      let score : Int := -childRes.value
      have hChildLenHere : childRes.pv.length ≤ d :=
        by simpa [child, childRes] using hChildLen m (by simp)
      have hChildLenTail :
          ∀ m', m' ∈ ms → (negamaxPV d (GameState.playMove gs m')).pv.length ≤ d := by
        intro m' hm'
        exact hChildLen m' (by simp [hm'])
      by_cases hBetter : score > best.value
      ·
        have hNewLen : (m :: childRes.pv).length ≤ d.succ := by
          simpa using Nat.succ_le_succ hChildLenHere
        have hStepEq :
            (fun best m =>
                  let child := GameState.playMove gs m;
                  let childRes := negamaxPV d child;
                  let score := -childRes.value;
                  if score > best.value then { value := score, pv := m :: childRes.pv } else best)
                best m =
              { value := score, pv := m :: childRes.pv } := by
          simp [child, childRes, score, hBetter]
        simpa [List.foldl, hStepEq] using
          (ih (best := { value := score, pv := m :: childRes.pv }) hNewLen hChildLenTail)
      ·
        have hStepEq :
            (fun best m =>
                  let child := GameState.playMove gs m;
                  let childRes := negamaxPV d child;
                  let score := -childRes.value;
                  if score > best.value then { value := score, pv := m :: childRes.pv } else best)
                best m =
              best := by
          simp [child, childRes, score, hBetter]
        simpa [List.foldl, hStepEq] using
          (ih (best := best) hBestLen hChildLenTail)

theorem pvLength_negamaxPV (depth : Nat) (gs : GameState) :
    (negamaxPV depth gs).pv.length ≤ depth := by
  induction depth generalizing gs with
  | zero =>
      cases hTerm : terminalValue? gs with
      | some v =>
          simp [negamaxPV, hTerm]
      | none =>
          simp [negamaxPV, hTerm]
  | succ d ih =>
      cases hTerm : terminalValue? gs with
      | some v =>
          simp [negamaxPV, hTerm]
      | none =>
          have hChildLen :
              ∀ m, m ∈ allLegalMoves gs → (negamaxPV d (GameState.playMove gs m)).pv.length ≤ d := by
            intro m _hm
            exact ih (gs := GameState.playMove gs m)
          have hInitLen : ([] : List Move).length ≤ d.succ := by
            simp
          simpa [negamaxPV, hTerm] using
            (pvLength_foldl_step (d := d) (gs := gs) (moves := allLegalMoves gs) (best := { value := -mateScore - 1, pv := [] })
              hInitLen hChildLen)

def negamaxScore (d : Nat) (gs : GameState) (m : Move) : Int :=
  -((negamaxPV d (GameState.playMove gs m)).value)

def pvHeadValueOk (d : Nat) (gs : GameState) (best : PVResult) : Prop :=
  best.pv = [] ∨
    ∃ m ms, best.pv = m :: ms ∧ best.value = negamaxScore d gs m

theorem pvHeadValueOk_step (d : Nat) (gs : GameState) (best : PVResult) (x : Move) :
    pvHeadValueOk d gs best →
    pvHeadValueOk d gs
      (let child := GameState.playMove gs x
       let childRes := negamaxPV d child
       let score := -childRes.value
       if score > best.value then
         { value := score, pv := x :: childRes.pv }
       else
         best) := by
  intro hOk
  let child := GameState.playMove gs x
  let childRes := negamaxPV d child
  let score : Int := -childRes.value
  by_cases hBetter : score > best.value
  ·
    right
    refine ⟨x, childRes.pv, ?_, ?_⟩
    · simp [child, childRes, score, hBetter]
    · simp [negamaxScore, child, childRes, score, hBetter]
  ·
    -- No update: return previous witness.
    cases hOk with
    | inl hNil =>
        left
        simpa [child, childRes, score, hBetter] using hNil
    | inr hW =>
        right
        rcases hW with ⟨m, ms, hPv, hVal⟩
        refine ⟨m, ms, ?_, ?_⟩
        · simpa [child, childRes, score, hBetter] using hPv
        · simpa [child, childRes, score, hBetter] using hVal

theorem pvHeadValueOk_foldl (d : Nat) (gs : GameState) (moves : List Move) (best : PVResult) :
    pvHeadValueOk d gs best →
    pvHeadValueOk d gs
      ((moves.foldl
          (fun best m =>
            let child := GameState.playMove gs m
            let childRes := negamaxPV d child
            let score := -childRes.value
            if score > best.value then
              { value := score, pv := m :: childRes.pv }
            else
              best)
          best)) := by
  intro h0
  induction moves generalizing best with
  | nil =>
      simpa [List.foldl] using h0
  | cons x xs ih =>
      let best1 :=
        (let child := GameState.playMove gs x
         let childRes := negamaxPV d child
         let score := -childRes.value
         if score > best.value then
           { value := score, pv := x :: childRes.pv }
         else
           best)
      have h1 : pvHeadValueOk d gs best1 := by
        simpa [best1] using (pvHeadValueOk_step (d := d) (gs := gs) (best := best) (x := x) h0)
      simpa [List.foldl, best1] using (ih (best := best1) h1)

theorem negamaxScore_le_foldl_value (d : Nat) (gs : GameState) (best : PVResult) :
    ∀ (moves : List Move) (m : Move),
      m ∈ moves →
      negamaxScore d gs m ≤
        (moves.foldl
            (fun best m =>
              let child := GameState.playMove gs m
              let childRes := negamaxPV d child
              let score := -childRes.value
              if score > best.value then
                { value := score, pv := m :: childRes.pv }
              else
                best)
            best).value := by
  let step : PVResult → Move → PVResult :=
    fun best m =>
      let child := GameState.playMove gs m
      let childRes := negamaxPV d child
      let score := -childRes.value
      if score > best.value then
        { value := score, pv := m :: childRes.pv }
      else
        best
  have foldl_value_ge_start :
      ∀ (moves : List Move) (best : PVResult), best.value ≤ (moves.foldl step best).value := by
    intro moves best
    induction moves generalizing best with
    | nil =>
        simp [List.foldl]
    | cons x xs ih =>
        -- `step` never decreases `value`; then apply IH to the tail.
        let child := GameState.playMove gs x
        let childRes := negamaxPV d child
        let score : Int := -childRes.value
        have hStep : best.value ≤ (step best x).value := by
          by_cases hBetter : score > best.value
          ·
            -- Updated: value becomes `score`, and `best.value < score`.
            have : best.value ≤ score := Int.le_of_lt hBetter
            simpa [step, child, childRes, score, hBetter] using this
          ·
            -- Not updated: value stays `best.value`.
            simp [step, child, childRes, score, hBetter]
        have hTail : (step best x).value ≤ (xs.foldl step (step best x)).value := by
          simpa using (ih (best := step best x))
        simpa [List.foldl] using (Int.le_trans hStep hTail)
  intro moves
  induction moves generalizing best with
  | nil =>
      intro m hMem
      cases hMem
  | cons x xs ih =>
      intro m hMem
      have hMem' : m = x ∨ m ∈ xs := by
        simpa using (List.mem_cons.1 hMem)
      cases hMem' with
      | inl hEq =>
          -- `m = x` in this branch.
          cases hEq
          let child := GameState.playMove gs x
          let childRes := negamaxPV d child
          let score : Int := -childRes.value
          have hScoreLeStep : negamaxScore d gs x ≤ (step best x).value := by
            by_cases hBetter : score > best.value
            · simp [negamaxScore, step, child, childRes, score, hBetter]
            ·
              have hLe : score ≤ best.value := Int.le_of_not_gt hBetter
              simpa [negamaxScore, step, child, childRes, score, hBetter] using hLe
          have hStepLeFold : (step best x).value ≤ (xs.foldl step (step best x)).value :=
            foldl_value_ge_start xs (step best x)
          have : negamaxScore d gs x ≤ (xs.foldl step (step best x)).value :=
            Int.le_trans hScoreLeStep hStepLeFold
          simpa [List.foldl, step] using this
      | inr hTail =>
          have := ih (best := step best x) m hTail
          simpa [List.foldl, step] using this

theorem negamaxPV_value_ge_moveScore (d : Nat) (gs : GameState) (m : Move) :
    terminalValue? gs = none →
    m ∈ allLegalMoves gs →
    negamaxScore d gs m ≤ (negamaxPV (Nat.succ d) gs).value := by
  intro hTerm hMem
  unfold negamaxPV
  simp [hTerm]
  have h := negamaxScore_le_foldl_value (d := d) (gs := gs) (best := { value := -mateScore - 1, pv := [] })
    (moves := allLegalMoves gs) (m := m) hMem
  simpa [negamaxScore] using h

theorem negamaxPV_value_eq_headScore (d : Nat) (gs : GameState) (m : Move) (ms : List Move) :
    terminalValue? gs = none →
    (negamaxPV (Nat.succ d) gs).pv = m :: ms →
    (negamaxPV (Nat.succ d) gs).value = negamaxScore d gs m := by
  intro hTerm hPv
  unfold negamaxPV at hPv ⊢
  simp [hTerm] at hPv ⊢
  -- Establish the head-value invariant for the fold result, then specialize to the given head.
  let moves := allLegalMoves gs
  let worst : PVResult := { value := -mateScore - 1, pv := [] }
  have hOk0 : pvHeadValueOk d gs worst := Or.inl rfl
  have hOk' :=
    pvHeadValueOk_foldl (d := d) (gs := gs) (moves := moves) (best := worst) hOk0
  cases hOk' with
  | inl hNil =>
      have hContra : (m :: ms) = ([] : List Move) := by
        -- Rewrite the fold PV via `hNil` and via `hPv`.
        simpa [moves, worst, hNil] using hPv
      cases hContra
  | inr hW =>
      rcases hW with ⟨m', ms', hPv', hVal⟩
      have hCons : m' :: ms' = m :: ms := by
        -- both are equal to the fold-produced PV
        simpa [moves, worst, hPv'] using hPv
      have hHead : (m' :: ms').head? = (m :: ms).head? :=
        congrArg List.head? hCons
      have hm' : m' = m := by
        have : (some m' : Option Move) = some m := by
          simpa using hHead
        exact Option.some.inj this
      subst hm'
      exact hVal

theorem negamaxPV_headScore_ge_moveScore
    (d : Nat) (gs : GameState) (mHead : Move) (ms : List Move) (m : Move) :
    terminalValue? gs = none →
    (negamaxPV (Nat.succ d) gs).pv = mHead :: ms →
    m ∈ allLegalMoves gs →
    negamaxScore d gs m ≤ negamaxScore d gs mHead := by
  intro hTerm hPv hMem
  have hLeVal : negamaxScore d gs m ≤ (negamaxPV (Nat.succ d) gs).value :=
    negamaxPV_value_ge_moveScore d gs m hTerm hMem
  have hValEq : (negamaxPV (Nat.succ d) gs).value = negamaxScore d gs mHead :=
    negamaxPV_value_eq_headScore d gs mHead ms hTerm hPv
  have : (negamaxPV (Nat.succ d) gs).value ≤ negamaxScore d gs mHead := by
    simp [hValEq]
  exact Int.le_trans hLeVal this

theorem negamax_eq_value_negamaxPV (depth : Nat) (gs : GameState) :
    negamax depth gs = (negamaxPV depth gs).value := by
  rfl

end Analysis
end Chess
