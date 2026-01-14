import Chess.Spec
import Chess.PathValidationProofs

namespace Chess
namespace Rules

open Movement

def isRookDelta : Int × Int → Prop
  | (df, dr) =>
      (df = 1 ∧ dr = 0) ∨
      (df = -1 ∧ dr = 0) ∨
      (df = 0 ∧ dr = 1) ∨
      (df = 0 ∧ dr = -1)

def isBishopDelta : Int × Int → Prop
  | (df, dr) =>
      (df = 1 ∧ dr = 1) ∨
      (df = -1 ∧ dr = -1) ∨
      (df = 1 ∧ dr = -1) ∨
      (df = -1 ∧ dr = 1)

def isQueenDelta (d : Int × Int) : Prop :=
  isRookDelta d ∨ isBishopDelta d

theorem isRookMove_of_rank_eq {src tgt : Square} (hRank : tgt.rankInt = src.rankInt)
    (hFileNe : tgt.fileInt ≠ src.fileInt) : Movement.isRookMove src tgt := by
  unfold Movement.isRookMove
  refine ⟨?_, ?_⟩
  · intro hEq
    apply hFileNe
    simp [hEq]
  · refine Or.inr ?_
    unfold Movement.rankDiff Movement.fileDiff
    constructor
    · simp [hRank]
    · intro hFd
      have : src.fileInt = tgt.fileInt := by
        omega
      exact hFileNe this.symm

theorem isRookMove_of_file_eq {src tgt : Square} (hFile : tgt.fileInt = src.fileInt)
    (hRankNe : tgt.rankInt ≠ src.rankInt) : Movement.isRookMove src tgt := by
  unfold Movement.isRookMove
  refine ⟨?_, ?_⟩
  · intro hEq
    apply hRankNe
    simp [hEq]
  · refine Or.inl ?_
    unfold Movement.rankDiff Movement.fileDiff
    constructor
    · simp [hFile]
    · intro hRd
      have : src.rankInt = tgt.rankInt := by
        omega
      exact hRankNe this.symm

theorem absInt_ofNat (n : Nat) : Movement.absInt (Int.ofNat n) = Int.ofNat n := by
  unfold Movement.absInt
  have h : (0 : Int) ≤ Int.ofNat n := Int.natCast_nonneg n
  simp [h]

theorem absInt_neg_ofNat (n : Nat) : Movement.absInt (-Int.ofNat n) = Int.ofNat n := by
  cases n with
  | zero =>
      simp [Movement.absInt]
  | succ n =>
      unfold Movement.absInt
      have hpos : (0 : Int) < Int.ofNat (Nat.succ n) := by
        have : (0 : Nat) < Nat.succ n := Nat.succ_pos n
        have : Int.ofNat 0 < Int.ofNat (Nat.succ n) := Int.ofNat_lt.mpr this
        simpa using this
      have h : ¬ (0 : Int) ≤ -Int.ofNat (Nat.succ n) := by
        intro hle
        omega
      rw [if_neg h]
      simp

theorem isDiagonal_of_coords
    {src tgt : Square} {k : Nat} {df dr : Int}
    (hSq :
      Movement.squareFromInts (src.fileInt + df * Int.ofNat k) (src.rankInt + dr * Int.ofNat k) =
        some tgt)
    (hkPos : 0 < k)
    (hDelta : isBishopDelta (df, dr)) :
    Movement.isDiagonal src tgt := by
  have hFile :
      tgt.fileInt = src.fileInt + df * Int.ofNat k :=
    Movement.squareFromInts_fileInt (src.fileInt + df * Int.ofNat k) (src.rankInt + dr * Int.ofNat k) tgt hSq
  have hRank :
      tgt.rankInt = src.rankInt + dr * Int.ofNat k :=
    Movement.squareFromInts_rankInt (src.fileInt + df * Int.ofNat k) (src.rankInt + dr * Int.ofNat k) tgt hSq
  unfold Movement.isDiagonal Movement.fileDiff Movement.rankDiff
  refine ⟨?_, ?_⟩
  · intro hEq
    -- Any bishop delta with k > 0 yields a distinct target square.
    have hkNe : k ≠ 0 := Nat.ne_of_gt hkPos
    have hOffNe : Int.ofNat k ≠ 0 := by
      intro h0
      have : k = 0 := by
        have := congrArg Int.toNat h0
        simpa using this
      exact hkNe this
    have hEqFile : tgt.fileInt = src.fileInt := by simp [hEq]
    -- From the coordinate equation, fileInt must shift by ±k, contradicting k > 0.
    cases hDelta with
    | inl h11 =>
        rcases h11 with ⟨hdf, hdr⟩
        subst hdf
        have hEqShift : src.fileInt + Int.ofNat k = src.fileInt := by
          have : src.fileInt = src.fileInt + Int.ofNat k := by
            calc
              src.fileInt = tgt.fileInt := by simpa using hEqFile.symm
              _ = src.fileInt + Int.ofNat k := by simp [hFile]
          exact this.symm
        have : src.fileInt + Int.ofNat k = src.fileInt + 0 := by
          simpa using hEqShift
        have : Int.ofNat k = 0 := Int.add_left_cancel this
        exact hOffNe this
    | inr hRest =>
        cases hRest with
        | inl hnn =>
            rcases hnn with ⟨hdf, hdr⟩
            subst hdf
            have hEqShift : src.fileInt + (-Int.ofNat k) = src.fileInt := by
              have : src.fileInt = src.fileInt + (-Int.ofNat k) := by
                calc
                  src.fileInt = tgt.fileInt := by simpa using hEqFile.symm
                  _ = src.fileInt + (-Int.ofNat k) := by simp [hFile]
              exact this.symm
            have : src.fileInt + (-Int.ofNat k) = src.fileInt + 0 := by
              simpa using hEqShift
            have : -Int.ofNat k = 0 := Int.add_left_cancel this
            have : Int.ofNat k = 0 := by
              have := congrArg (fun t => -t) this
              simpa using this
            exact hOffNe this
        | inr hRest2 =>
            cases hRest2 with
            | inl h1n =>
                rcases h1n with ⟨hdf, hdr⟩
                subst hdf
                have hEqShift : src.fileInt + Int.ofNat k = src.fileInt := by
                  have : src.fileInt = src.fileInt + Int.ofNat k := by
                    calc
                      src.fileInt = tgt.fileInt := by simpa using hEqFile.symm
                      _ = src.fileInt + Int.ofNat k := by simp [hFile]
                  exact this.symm
                have : src.fileInt + Int.ofNat k = src.fileInt + 0 := by
                  simpa using hEqShift
                have : Int.ofNat k = 0 := Int.add_left_cancel this
                exact hOffNe this
            | inr hn1 =>
                rcases hn1 with ⟨hdf, hdr⟩
                subst hdf
                have hEqShift : src.fileInt + (-Int.ofNat k) = src.fileInt := by
                  have : src.fileInt = src.fileInt + (-Int.ofNat k) := by
                    calc
                      src.fileInt = tgt.fileInt := by simpa using hEqFile.symm
                      _ = src.fileInt + (-Int.ofNat k) := by simp [hFile]
                  exact this.symm
                have : src.fileInt + (-Int.ofNat k) = src.fileInt + 0 := by
                  simpa using hEqShift
                have : -Int.ofNat k = 0 := Int.add_left_cancel this
                have : Int.ofNat k = 0 := by
                  have := congrArg (fun t => -t) this
                  simpa using this
                exact hOffNe this
  · -- Compute the file/rank diffs and show their absolute values agree (both are k).
    have hfd :
        src.fileInt - tgt.fileInt = -(df * Int.ofNat k) := by
      have : src.fileInt - (src.fileInt + df * Int.ofNat k) = -(df * Int.ofNat k) := by
        omega
      simpa [hFile] using this
    have hrd :
        src.rankInt - tgt.rankInt = -(dr * Int.ofNat k) := by
      have : src.rankInt - (src.rankInt + dr * Int.ofNat k) = -(dr * Int.ofNat k) := by
        omega
      simpa [hRank] using this
    -- Case split on the four bishop deltas and reduce to absInt (±k) = k.
    cases hDelta with
    | inl h11 =>
        rcases h11 with ⟨hdf, hdr⟩
        subst hdf; subst hdr
        simp [hfd, hrd, absInt_neg_ofNat]
    | inr hRest =>
        cases hRest with
        | inl hnn =>
            rcases hnn with ⟨hdf, hdr⟩
            subst hdf; subst hdr
            simp [hfd, hrd, absInt_ofNat, absInt_neg_ofNat]
        | inr hRest2 =>
            cases hRest2 with
            | inl h1n =>
                rcases h1n with ⟨hdf, hdr⟩
                subst hdf; subst hdr
                -- fileDiff = -k, rankDiff = k
                have hNeg : Movement.absInt (-Int.ofNat k) = Int.ofNat k := absInt_neg_ofNat k
                have hPos : Movement.absInt (Int.ofNat k) = Int.ofNat k := absInt_ofNat k
                -- Reduce to `absInt (-k) = absInt k` and rewrite both sides to `k`.
                have : Movement.absInt (-Int.ofNat k) = Movement.absInt (Int.ofNat k) := by
                  calc
                    Movement.absInt (-Int.ofNat k) = Int.ofNat k := hNeg
                    _ = Movement.absInt (Int.ofNat k) := by simpa using hPos.symm
                -- Now discharge the original goal.
                simpa [hfd, hrd] using this
            | inr hn1 =>
                rcases hn1 with ⟨hdf, hdr⟩
                subst hdf; subst hdr
                -- fileDiff = k, rankDiff = -k
                have hPos : Movement.absInt (Int.ofNat k) = Int.ofNat k := absInt_ofNat k
                have hNeg : Movement.absInt (-Int.ofNat k) = Int.ofNat k := absInt_neg_ofNat k
                have : Movement.absInt (Int.ofNat k) = Movement.absInt (-Int.ofNat k) := by
                  calc
                    Movement.absInt (Int.ofNat k) = Int.ofNat k := hPos
                    _ = Movement.absInt (-Int.ofNat k) := by simpa using hNeg.symm
                simpa [hfd, hrd] using this

theorem slidingTargets_walk_mem_isRookMove
    (src : Square) (p : Piece) (board : Board) (color : Color) (maxStep : Nat)
    (df dr : Int) (hDelta : isRookDelta (df, dr)) :
    ∀ (step : Nat) (acc : List Move) (m : Move),
      step ≤ maxStep →
      (∀ x ∈ acc, Movement.isRookMove src x.toSq) →
      m ∈ Rules.slidingTargets.walk src p board color maxStep df dr step acc →
      Movement.isRookMove src m.toSq := by
  intro step
  induction step with
  | zero =>
      intro acc m _hLe hAcc hMem
      simp [Rules.slidingTargets.walk] at hMem
      exact hAcc m hMem
  | succ s ih =>
      intro acc m hLe hAcc hMem
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
          -- Helper: rook-move geometry for this `target`.
          have hFile :
              target.fileInt = src.fileInt + df * Int.ofNat (maxStep - s) :=
            Movement.squareFromInts_fileInt
              (src.fileInt + df * Int.ofNat (maxStep - s))
              (src.rankInt + dr * Int.ofNat (maxStep - s))
              target hSq
          have hRank :
              target.rankInt = src.rankInt + dr * Int.ofNat (maxStep - s) :=
            Movement.squareFromInts_rankInt
              (src.fileInt + df * Int.ofNat (maxStep - s))
              (src.rankInt + dr * Int.ofNat (maxStep - s))
              target hSq
          have hslt : s < maxStep := Nat.lt_of_succ_le hLe
          have hkPos : 0 < maxStep - s := Nat.sub_pos_of_lt hslt
          have hkNe : maxStep - s ≠ 0 := Nat.ne_of_gt hkPos
          have hOffNe : Int.ofNat (maxStep - s) ≠ 0 := by
            intro h0
            have : maxStep - s = 0 := by
              have := congrArg Int.toNat h0
              simpa using this
            exact hkNe this
          have hTargetRook : Movement.isRookMove src target := by
            cases hDelta with
            | inl h10 =>
                rcases h10 with ⟨hdf, hdr⟩
                subst hdf; subst hdr
                have hRankEq : target.rankInt = src.rankInt := by
                  simp [hRank]
                have hFileNe : target.fileInt ≠ src.fileInt := by
                  intro hEq
                  have : src.fileInt + Int.ofNat (maxStep - s) = src.fileInt + 0 := by
                    simpa [hFile] using hEq
                  have : Int.ofNat (maxStep - s) = 0 := Int.add_left_cancel this
                  exact hOffNe this
                exact isRookMove_of_rank_eq hRankEq hFileNe
            | inr hRest =>
                cases hRest with
                | inl hn10 =>
                    rcases hn10 with ⟨hdf, hdr⟩
                    subst hdf; subst hdr
                    have hRankEq : target.rankInt = src.rankInt := by
                      simp [hRank]
                    have hFileNe : target.fileInt ≠ src.fileInt := by
                      intro hEq
                      have : src.fileInt + (-Int.ofNat (maxStep - s)) = src.fileInt + 0 := by
                        simpa [hFile] using hEq
                      have : -Int.ofNat (maxStep - s) = 0 := Int.add_left_cancel this
                      have : Int.ofNat (maxStep - s) = 0 := by
                        have := congrArg (fun t => -t) this
                        simpa using this
                      exact hOffNe this
                    exact isRookMove_of_rank_eq hRankEq hFileNe
                | inr hRest2 =>
                    cases hRest2 with
                    | inl h01 =>
                        rcases h01 with ⟨hdf, hdr⟩
                        subst hdf; subst hdr
                        have hFileEq : target.fileInt = src.fileInt := by
                          simp [hFile]
                        have hRankNe : target.rankInt ≠ src.rankInt := by
                          intro hEq
                          have : src.rankInt + Int.ofNat (maxStep - s) = src.rankInt + 0 := by
                            simpa [hRank] using hEq
                          have : Int.ofNat (maxStep - s) = 0 := Int.add_left_cancel this
                          exact hOffNe this
                        exact isRookMove_of_file_eq hFileEq hRankNe
                    | inr h0n1 =>
                        rcases h0n1 with ⟨hdf, hdr⟩
                        subst hdf; subst hdr
                        have hFileEq : target.fileInt = src.fileInt := by
                          simp [hFile]
                        have hRankNe : target.rankInt ≠ src.rankInt := by
                          intro hEq
                          have : src.rankInt + (-Int.ofNat (maxStep - s)) = src.rankInt + 0 := by
                            simpa [hRank] using hEq
                          have : -Int.ofNat (maxStep - s) = 0 := Int.add_left_cancel this
                          have : Int.ofNat (maxStep - s) = 0 := by
                            have := congrArg (fun t => -t) this
                            simpa using this
                          exact hOffNe this
                        exact isRookMove_of_file_eq hFileEq hRankNe
          by_cases hEmpty : Rules.isEmpty board target = true
          · have hRec :
                m ∈
                  Rules.slidingTargets.walk src p board color maxStep df dr s
                    ({ piece := p, fromSq := src, toSq := target } :: acc) := by
                simpa [hSq, hEmpty] using hMem'
            have hAcc' : ∀ x ∈ ({ piece := p, fromSq := src, toSq := target } :: acc), Movement.isRookMove src x.toSq := by
              intro x hx
              have hx' : x = { piece := p, fromSq := src, toSq := target } ∨ x ∈ acc := by
                simpa [List.mem_cons] using hx
              cases hx' with
              | inl hEq =>
                  simp [hEq, hTargetRook]
              | inr hIn =>
                  exact hAcc x hIn
            have hLe' : s ≤ maxStep := Nat.le_trans (Nat.le_succ s) hLe
            exact ih ({ piece := p, fromSq := src, toSq := target } :: acc) m hLe' hAcc' hRec
          · by_cases hEnemy : Rules.isEnemyNonKingAt board color target = true
            · have hMemCons :
                  m ∈ { piece := p, fromSq := src, toSq := target, isCapture := true } :: acc := by
                simpa [hSq, hEmpty, hEnemy] using hMem'
              have hSplit :
                  m = { piece := p, fromSq := src, toSq := target, isCapture := true } ∨ m ∈ acc := by
                simpa [List.mem_cons] using hMemCons
              cases hSplit with
              | inl hEq =>
                  subst hEq
                  simp [hTargetRook]
              | inr hIn =>
                  exact hAcc m hIn
            · have hIn : m ∈ acc := by
                simpa [hSq, hEmpty, hEnemy] using hMem'
              exact hAcc m hIn

theorem slidingTargets_walk_mem_isDiagonal
    (src : Square) (p : Piece) (board : Board) (color : Color) (maxStep : Nat)
    (df dr : Int) (hDelta : isBishopDelta (df, dr)) :
    ∀ (step : Nat) (acc : List Move) (m : Move),
      step ≤ maxStep →
      (∀ x ∈ acc, Movement.isDiagonal src x.toSq) →
      m ∈ Rules.slidingTargets.walk src p board color maxStep df dr step acc →
      Movement.isDiagonal src m.toSq := by
  intro step
  induction step with
  | zero =>
      intro acc m _hLe hAcc hMem
      simp [Rules.slidingTargets.walk] at hMem
      exact hAcc m hMem
  | succ s ih =>
      intro acc m hLe hAcc hMem
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
          have hTargetDiag : Movement.isDiagonal src target := by
            have hslt : s < maxStep := Nat.lt_of_succ_le hLe
            have hkPos : 0 < maxStep - s := Nat.sub_pos_of_lt hslt
            exact
              isDiagonal_of_coords (src := src) (tgt := target) (k := maxStep - s) (df := df) (dr := dr)
                hSq hkPos hDelta
          by_cases hEmpty : Rules.isEmpty board target = true
          · have hRec :
                m ∈
                  Rules.slidingTargets.walk src p board color maxStep df dr s
                    ({ piece := p, fromSq := src, toSq := target } :: acc) := by
                simpa [hSq, hEmpty] using hMem'
            have hAcc' : ∀ x ∈ ({ piece := p, fromSq := src, toSq := target } :: acc), Movement.isDiagonal src x.toSq := by
              intro x hx
              have hx' : x = { piece := p, fromSq := src, toSq := target } ∨ x ∈ acc := by
                simpa [List.mem_cons] using hx
              cases hx' with
              | inl hEq =>
                  simp [hEq, hTargetDiag]
              | inr hIn =>
                  exact hAcc x hIn
            have hLe' : s ≤ maxStep := Nat.le_trans (Nat.le_succ s) hLe
            exact ih ({ piece := p, fromSq := src, toSq := target } :: acc) m hLe' hAcc' hRec
          · by_cases hEnemy : Rules.isEnemyNonKingAt board color target = true
            · have hMemCons :
                  m ∈ { piece := p, fromSq := src, toSq := target, isCapture := true } :: acc := by
                simpa [hSq, hEmpty, hEnemy] using hMem'
              have hSplit :
                  m = { piece := p, fromSq := src, toSq := target, isCapture := true } ∨ m ∈ acc := by
                simpa [List.mem_cons] using hMemCons
              cases hSplit with
              | inl hEq =>
                  subst hEq
                  simp [hTargetDiag]
              | inr hIn =>
                  exact hAcc m hIn
            · have hIn : m ∈ acc := by
                simpa [hSq, hEmpty, hEnemy] using hMem'
              exact hAcc m hIn

theorem mem_slidingTargets_isRookMove
    (gs : GameState) (src : Square) (p : Piece) (deltas : List (Int × Int)) (m : Move)
    (hDeltas : ∀ d ∈ deltas, isRookDelta d) :
    m ∈ Rules.slidingTargets gs src p deltas →
    Movement.isRookMove src m.toSq := by
  revert m
  induction deltas with
  | nil =>
      intro m hMem
      cases (show False by simpa [Rules.slidingTargets] using hMem)
  | cons d rest ih =>
      intro m hMem
      rcases d with ⟨df, dr⟩
      have hDelta : isRookDelta (df, dr) := hDeltas (df, dr) (by simp)
      let acc :=
        List.foldr
          (fun d acc =>
            match d with
            | (df, dr) => Rules.slidingTargets.walk src p gs.board p.color 7 df dr 7 acc)
          [] rest
      have hAccAll : ∀ x ∈ acc, Movement.isRookMove src x.toSq := by
        intro x hx
        have hx' : x ∈ Rules.slidingTargets gs src p rest := by
          simpa [Rules.slidingTargets, acc] using hx
        have hDeltasRest : ∀ d ∈ rest, isRookDelta d := by
          intro d hd
          exact hDeltas d (by simp [hd])
        exact ih hDeltasRest x hx'
      have hMem' : m ∈ Rules.slidingTargets.walk src p gs.board p.color 7 df dr 7 acc := by
        simpa [Rules.slidingTargets, List.foldr, acc] using hMem
      exact
        slidingTargets_walk_mem_isRookMove src p gs.board p.color 7 df dr hDelta 7 acc m (by simp) hAccAll hMem'

theorem mem_slidingTargets_isDiagonal
    (gs : GameState) (src : Square) (p : Piece) (deltas : List (Int × Int)) (m : Move)
    (hDeltas : ∀ d ∈ deltas, isBishopDelta d) :
    m ∈ Rules.slidingTargets gs src p deltas →
    Movement.isDiagonal src m.toSq := by
  revert m
  induction deltas with
  | nil =>
      intro m hMem
      cases (show False by simpa [Rules.slidingTargets] using hMem)
  | cons d rest ih =>
      intro m hMem
      rcases d with ⟨df, dr⟩
      have hDelta : isBishopDelta (df, dr) := hDeltas (df, dr) (by simp)
      let acc :=
        List.foldr
          (fun d acc =>
            match d with
            | (df, dr) => Rules.slidingTargets.walk src p gs.board p.color 7 df dr 7 acc)
          [] rest
      have hAccAll : ∀ x ∈ acc, Movement.isDiagonal src x.toSq := by
        intro x hx
        have hx' : x ∈ Rules.slidingTargets gs src p rest := by
          simpa [Rules.slidingTargets, acc] using hx
        have hDeltasRest : ∀ d ∈ rest, isBishopDelta d := by
          intro d hd
          exact hDeltas d (by simp [hd])
        exact ih hDeltasRest x hx'
      have hMem' : m ∈ Rules.slidingTargets.walk src p gs.board p.color 7 df dr 7 acc := by
        simpa [Rules.slidingTargets, List.foldr, acc] using hMem
      exact
        slidingTargets_walk_mem_isDiagonal src p gs.board p.color 7 df dr hDelta 7 acc m (by simp) hAccAll hMem'

theorem mem_pieceTargets_rook_isRookMove
    (gs : GameState) (src : Square) (p : Piece) (m : Move)
    (hRook : p.pieceType = PieceType.Rook) :
    m ∈ pieceTargets gs src p →
    Movement.isRookMove src m.toSq := by
  intro hMem
  have hMem' :
      m ∈
        slidingTargets gs src p [(1, 0), (-1, 0), (0, 1), (0, -1)] := by
    simpa [pieceTargets, hRook] using hMem
  refine mem_slidingTargets_isRookMove gs src p _ m ?_ hMem'
  intro d hd
  -- All rook deltas satisfy `isRookDelta`.
  have hd' : d = (1, 0) ∨ d = (-1, 0) ∨ d = (0, 1) ∨ d = (0, -1) := by
    simpa using hd
  rcases hd' with rfl | hd'
  · simp [isRookDelta]
  rcases hd' with rfl | hd'
  · simp [isRookDelta]
  rcases hd' with rfl | hd'
  · simp [isRookDelta]
  · rcases hd' with rfl
    simp [isRookDelta]

theorem mem_pieceTargets_bishop_isDiagonal
    (gs : GameState) (src : Square) (p : Piece) (m : Move)
    (hBishop : p.pieceType = PieceType.Bishop) :
    m ∈ pieceTargets gs src p →
    Movement.isDiagonal src m.toSq := by
  intro hMem
  have hMem' :
      m ∈
        slidingTargets gs src p [(1, 1), (-1, -1), (1, -1), (-1, 1)] := by
    simpa [pieceTargets, hBishop] using hMem
  refine mem_slidingTargets_isDiagonal gs src p _ m ?_ hMem'
  intro d hd
  have hd' : d = (1, 1) ∨ d = (-1, -1) ∨ d = (1, -1) ∨ d = (-1, 1) := by
    simpa using hd
  rcases hd' with rfl | hd'
  · simp [isBishopDelta]
  rcases hd' with rfl | hd'
  · simp [isBishopDelta]
  rcases hd' with rfl | hd'
  · simp [isBishopDelta]
  · rcases hd' with rfl
    simp [isBishopDelta]

theorem isRookMove_of_coords
    {src tgt : Square} {k : Nat} {df dr : Int}
    (hSq :
      Movement.squareFromInts (src.fileInt + df * Int.ofNat k) (src.rankInt + dr * Int.ofNat k) =
        some tgt)
    (hkPos : 0 < k)
    (hDelta : isRookDelta (df, dr)) :
    Movement.isRookMove src tgt := by
  have hFile :
      tgt.fileInt = src.fileInt + df * Int.ofNat k :=
    Movement.squareFromInts_fileInt (src.fileInt + df * Int.ofNat k) (src.rankInt + dr * Int.ofNat k) tgt hSq
  have hRank :
      tgt.rankInt = src.rankInt + dr * Int.ofNat k :=
    Movement.squareFromInts_rankInt (src.fileInt + df * Int.ofNat k) (src.rankInt + dr * Int.ofNat k) tgt hSq
  have hkNe : k ≠ 0 := Nat.ne_of_gt hkPos
  have hOffNe : Int.ofNat k ≠ 0 := by
    intro h0
    have : k = 0 := by
      have := congrArg Int.toNat h0
      simpa using this
    exact hkNe this
  cases hDelta with
  | inl h10 =>
      rcases h10 with ⟨hdf, hdr⟩
      subst hdf; subst hdr
      have hRankEq : tgt.rankInt = src.rankInt := by
        simp [hRank]
      have hFileNe : tgt.fileInt ≠ src.fileInt := by
        intro hEq
        have : src.fileInt + Int.ofNat k = src.fileInt + 0 := by
          simpa [hFile] using hEq
        have : Int.ofNat k = 0 := Int.add_left_cancel this
        exact hOffNe this
      exact isRookMove_of_rank_eq hRankEq hFileNe
  | inr hRest =>
      cases hRest with
      | inl hn10 =>
          rcases hn10 with ⟨hdf, hdr⟩
          subst hdf; subst hdr
          have hRankEq : tgt.rankInt = src.rankInt := by
            simp [hRank]
          have hFileNe : tgt.fileInt ≠ src.fileInt := by
            intro hEq
            have : src.fileInt + (-Int.ofNat k) = src.fileInt + 0 := by
              simpa [hFile] using hEq
            have : -Int.ofNat k = 0 := Int.add_left_cancel this
            have : Int.ofNat k = 0 := by
              have := congrArg (fun t => -t) this
              simpa using this
            exact hOffNe this
          exact isRookMove_of_rank_eq hRankEq hFileNe
      | inr hRest2 =>
          cases hRest2 with
          | inl h01 =>
              rcases h01 with ⟨hdf, hdr⟩
              subst hdf; subst hdr
              have hFileEq : tgt.fileInt = src.fileInt := by
                simp [hFile]
              have hRankNe : tgt.rankInt ≠ src.rankInt := by
                intro hEq
                have : src.rankInt + Int.ofNat k = src.rankInt + 0 := by
                  simpa [hRank] using hEq
                have : Int.ofNat k = 0 := Int.add_left_cancel this
                exact hOffNe this
              exact isRookMove_of_file_eq hFileEq hRankNe
          | inr h0n1 =>
              rcases h0n1 with ⟨hdf, hdr⟩
              subst hdf; subst hdr
              have hFileEq : tgt.fileInt = src.fileInt := by
                simp [hFile]
              have hRankNe : tgt.rankInt ≠ src.rankInt := by
                intro hEq
                have : src.rankInt + (-Int.ofNat k) = src.rankInt + 0 := by
                  simpa [hRank] using hEq
                have : -Int.ofNat k = 0 := Int.add_left_cancel this
                have : Int.ofNat k = 0 := by
                  have := congrArg (fun t => -t) this
                  simpa using this
                exact hOffNe this
              exact isRookMove_of_file_eq hFileEq hRankNe

theorem slidingTargets_walk_mem_isQueenMove
    (src : Square) (p : Piece) (board : Board) (color : Color) (maxStep : Nat)
    (df dr : Int) (hDelta : isQueenDelta (df, dr)) :
    ∀ (step : Nat) (acc : List Move) (m : Move),
      step ≤ maxStep →
      (∀ x ∈ acc, Movement.isQueenMove src x.toSq) →
      m ∈ Rules.slidingTargets.walk src p board color maxStep df dr step acc →
      Movement.isQueenMove src m.toSq := by
  intro step
  induction step with
  | zero =>
      intro acc m _hLe hAcc hMem
      simp [Rules.slidingTargets.walk] at hMem
      exact hAcc m hMem
  | succ s ih =>
      intro acc m hLe hAcc hMem
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
          have hslt : s < maxStep := Nat.lt_of_succ_le hLe
          have hkPos : 0 < maxStep - s := Nat.sub_pos_of_lt hslt
          have hTargetQueen : Movement.isQueenMove src target := by
            cases hDelta with
            | inl hR =>
                exact Or.inl <|
                  isRookMove_of_coords (src := src) (tgt := target) (k := maxStep - s) (df := df) (dr := dr)
                    hSq hkPos hR
            | inr hB =>
                exact Or.inr <|
                  isDiagonal_of_coords (src := src) (tgt := target) (k := maxStep - s) (df := df) (dr := dr)
                    hSq hkPos hB
          by_cases hEmpty : Rules.isEmpty board target = true
          · have hRec :
                m ∈
                  Rules.slidingTargets.walk src p board color maxStep df dr s
                    ({ piece := p, fromSq := src, toSq := target } :: acc) := by
                simpa [hSq, hEmpty] using hMem'
            have hAcc' : ∀ x ∈ ({ piece := p, fromSq := src, toSq := target } :: acc), Movement.isQueenMove src x.toSq := by
              intro x hx
              have hx' : x = { piece := p, fromSq := src, toSq := target } ∨ x ∈ acc := by
                simpa [List.mem_cons] using hx
              cases hx' with
              | inl hEq =>
                  simp [hEq, hTargetQueen]
              | inr hIn =>
                  exact hAcc x hIn
            have hLe' : s ≤ maxStep := Nat.le_trans (Nat.le_succ s) hLe
            exact ih ({ piece := p, fromSq := src, toSq := target } :: acc) m hLe' hAcc' hRec
          · by_cases hEnemy : Rules.isEnemyNonKingAt board color target = true
            · have hMemCons :
                  m ∈ { piece := p, fromSq := src, toSq := target, isCapture := true } :: acc := by
                simpa [hSq, hEmpty, hEnemy] using hMem'
              have hSplit :
                  m = { piece := p, fromSq := src, toSq := target, isCapture := true } ∨ m ∈ acc := by
                simpa [List.mem_cons] using hMemCons
              cases hSplit with
              | inl hEq =>
                  subst hEq
                  simp [hTargetQueen]
              | inr hIn =>
                  exact hAcc m hIn
            · have hIn : m ∈ acc := by
                simpa [hSq, hEmpty, hEnemy] using hMem'
              exact hAcc m hIn

theorem mem_slidingTargets_isQueenMove
    (gs : GameState) (src : Square) (p : Piece) (deltas : List (Int × Int)) (m : Move)
    (hDeltas : ∀ d ∈ deltas, isQueenDelta d) :
    m ∈ Rules.slidingTargets gs src p deltas →
    Movement.isQueenMove src m.toSq := by
  revert m
  induction deltas with
  | nil =>
      intro m hMem
      cases (show False by simpa [Rules.slidingTargets] using hMem)
  | cons d rest ih =>
      intro m hMem
      rcases d with ⟨df, dr⟩
      have hDelta : isQueenDelta (df, dr) := hDeltas (df, dr) (by simp)
      let acc :=
        List.foldr
          (fun d acc =>
            match d with
            | (df, dr) => Rules.slidingTargets.walk src p gs.board p.color 7 df dr 7 acc)
          [] rest
      have hAccAll : ∀ x ∈ acc, Movement.isQueenMove src x.toSq := by
        intro x hx
        have hx' : x ∈ Rules.slidingTargets gs src p rest := by
          simpa [Rules.slidingTargets, acc] using hx
        have hDeltasRest : ∀ d ∈ rest, isQueenDelta d := by
          intro d hd
          exact hDeltas d (by simp [hd])
        exact ih hDeltasRest x hx'
      have hMem' : m ∈ Rules.slidingTargets.walk src p gs.board p.color 7 df dr 7 acc := by
        simpa [Rules.slidingTargets, List.foldr, acc] using hMem
      exact
        slidingTargets_walk_mem_isQueenMove src p gs.board p.color 7 df dr hDelta 7 acc m (by simp) hAccAll hMem'

theorem mem_pieceTargets_queen_isQueenMove
    (gs : GameState) (src : Square) (p : Piece) (m : Move)
    (hQueen : p.pieceType = PieceType.Queen) :
    m ∈ pieceTargets gs src p →
    Movement.isQueenMove src m.toSq := by
  intro hMem
  have hMem' :
      m ∈
        slidingTargets gs src p
          [(1, 0), (-1, 0), (0, 1), (0, -1), (1, 1), (-1, -1), (1, -1), (-1, 1)] := by
    simpa [pieceTargets, hQueen] using hMem
  refine mem_slidingTargets_isQueenMove gs src p _ m ?_ hMem'
  intro d hd
  have hd' :
      d = (1, 0) ∨ d = (-1, 0) ∨ d = (0, 1) ∨ d = (0, -1) ∨
        d = (1, 1) ∨ d = (-1, -1) ∨ d = (1, -1) ∨ d = (-1, 1) := by
    simpa using hd
  rcases hd' with rfl | hd'
  · simp [isQueenDelta, isRookDelta, isBishopDelta]
  rcases hd' with rfl | hd'
  · simp [isQueenDelta, isRookDelta, isBishopDelta]
  rcases hd' with rfl | hd'
  · simp [isQueenDelta, isRookDelta, isBishopDelta]
  rcases hd' with rfl | hd'
  · simp [isQueenDelta, isRookDelta, isBishopDelta]
  rcases hd' with rfl | hd'
  · simp [isQueenDelta, isRookDelta, isBishopDelta]
  rcases hd' with rfl | hd'
  · simp [isQueenDelta, isRookDelta, isBishopDelta]
  rcases hd' with rfl | hd'
  · simp [isQueenDelta, isRookDelta, isBishopDelta]
  · rcases hd' with rfl
    simp [isQueenDelta, isRookDelta, isBishopDelta]

end Rules
end Chess
