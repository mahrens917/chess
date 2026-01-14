import Init.Omega
import Chess.PathValidationProofs

namespace Chess

open Movement

namespace Movement

theorem signInt_mul_natAbs (x : Int) : Movement.signInt x * (x.natAbs : Int) = x := by
  cases x with
  | ofNat n =>
      cases n with
      | zero =>
          simp [Movement.signInt]
      | succ n =>
          have hNe : (↑(Nat.succ n) : Int) ≠ 0 := by
            exact Int.ofNat_ne_zero.mpr (Nat.succ_ne_zero _)
          have hGt : (↑(Nat.succ n) : Int) > 0 := by
            simpa using (Int.ofNat_pos.mpr (Nat.succ_pos n))
          have hNe' : (↑n + 1 : Int) ≠ 0 := by
            simpa [Int.natCast_succ] using hNe
          have hGt' : (↑n + 1 : Int) > 0 := by
            simpa [Int.natCast_succ] using hGt
          have hSign : Movement.signInt (↑n + 1 : Int) = 1 := by
            unfold Movement.signInt
            simp [hNe', hGt']
          -- Normalize `↑(Nat.succ n)` into the `↑n + 1` form for the remaining simp steps.
          have hNatAbs : ((↑n : Int) + 1).natAbs = n + 1 := by
            rw [← Int.natCast_succ n]
            rfl
          simp [hSign, hNatAbs]
  | negSucc n =>
      have hNotGt : ¬(Int.negSucc n > 0) := by
        omega
      have hNe : (Int.negSucc n) ≠ 0 := by
        simp
      have hSign : Movement.signInt (Int.negSucc n) = -1 := by
        unfold Movement.signInt
        simp [hNe, hNotGt]
      have hNatAbs : (Int.negSucc n).natAbs = n.succ := by
        simpa using Int.natAbs_negSucc n
      calc
        Movement.signInt (Int.negSucc n) * ((Int.negSucc n).natAbs : Int)
            = (-1) * (n.succ : Int) := by
              simp [hSign, hNatAbs]
        _ = -(↑n.succ : Int) := by
              simp
        _ = Int.negSucc n := by
              simpa using (Int.neg_ofNat_succ n)

theorem squareFromInts_rookDelta_rookOffset (src tgt : Square) (hRook : Movement.isRookMove src tgt) :
    Movement.squareFromInts
        (src.fileInt + (Movement.rookDelta src tgt).1 * (Movement.rookOffset src tgt : Int))
        (src.rankInt + (Movement.rookDelta src tgt).2 * (Movement.rookOffset src tgt : Int)) =
      some tgt := by
  by_cases hFileZero : Movement.fileDiff src tgt = 0
  · -- Vertical move: file stays fixed; rank changes.
    have hLine : Movement.fileDiff src tgt = 0 ∧ Movement.rankDiff src tgt ≠ 0 := by
      cases hRook.2 with
      | inl h =>
          simpa using h
      | inr h =>
          have hFileNe : Movement.fileDiff src tgt ≠ 0 := h.2
          have : False := hFileNe hFileZero
          cases this
    have hFileEq : tgt.fileInt = src.fileInt := by
      unfold Movement.fileDiff at hFileZero
      omega
    have hMul :
        Movement.signInt (-Movement.rankDiff src tgt) * ((Movement.rankDiff src tgt).natAbs : Int) =
          -Movement.rankDiff src tgt := by
      have := Movement.signInt_mul_natAbs (-Movement.rankDiff src tgt)
      simpa [Int.natAbs_neg] using this
    have hRankEq :
        src.rankInt + Movement.signInt (-Movement.rankDiff src tgt) * ((Movement.rankDiff src tgt).natAbs : Int) =
          tgt.rankInt := by
      have hBase : src.rankInt + (-Movement.rankDiff src tgt) = tgt.rankInt := by
        unfold Movement.rankDiff
        omega
      simpa [hMul] using hBase
    -- Reduce to `squareFromInts` at the target coordinates.
    have hSq : Movement.squareFromInts tgt.fileInt tgt.rankInt = some tgt :=
      Movement.squareFromInts_of_coords tgt
    -- In the vertical branch, `rookDelta = (0, signInt(-rankDiff))` and `rookOffset = rankDiff.natAbs`.
    simpa [Movement.rookDelta, Movement.rookOffset, hFileZero, hFileEq, hRankEq] using hSq
  · -- Horizontal move: rank stays fixed; file changes.
    have hLine : Movement.rankDiff src tgt = 0 ∧ Movement.fileDiff src tgt ≠ 0 := by
      cases hRook.2 with
      | inl h =>
          cases (hFileZero (by simpa using h.1))
      | inr h =>
          simpa using h
    have hRankEq : tgt.rankInt = src.rankInt := by
      unfold Movement.rankDiff at hLine
      omega
    have hMul :
        Movement.signInt (-Movement.fileDiff src tgt) * ((Movement.fileDiff src tgt).natAbs : Int) =
          -Movement.fileDiff src tgt := by
      have := Movement.signInt_mul_natAbs (-Movement.fileDiff src tgt)
      simpa [Int.natAbs_neg] using this
    have hFileEq :
        src.fileInt + Movement.signInt (-Movement.fileDiff src tgt) * ((Movement.fileDiff src tgt).natAbs : Int) =
          tgt.fileInt := by
      have hBase : src.fileInt + (-Movement.fileDiff src tgt) = tgt.fileInt := by
        unfold Movement.fileDiff
        omega
      simpa [hMul] using hBase
    have hSq : Movement.squareFromInts tgt.fileInt tgt.rankInt = some tgt :=
      Movement.squareFromInts_of_coords tgt
    simpa [Movement.rookDelta, Movement.rookOffset, hFileZero, hLine.1, hRankEq, hFileEq] using hSq

theorem squareFromInts_rookDelta_step_some (src tgt : Square) (hRook : Movement.isRookMove src tgt) (t : Nat)
    (ht : t ≤ Movement.rookOffset src tgt) :
    ∃ sq,
      Movement.squareFromInts (src.fileInt + (Movement.rookDelta src tgt).1 * (t : Int))
          (src.rankInt + (Movement.rookDelta src tgt).2 * (t : Int)) =
        some sq := by
  -- Split on vertical vs horizontal.
  by_cases hFileZero : Movement.fileDiff src tgt = 0
  · -- Vertical: file fixed, rank moves.
    have hRankNe : Movement.rankDiff src tgt ≠ 0 := by
      cases hRook.2 with
      | inl h => exact h.2
      | inr h =>
          -- Contradiction: horizontal case would require fileDiff ≠ 0.
          exact (h.2 hFileZero).elim

    have hDelta : Movement.rookDelta src tgt = (0, Movement.signInt (-Movement.rankDiff src tgt)) := by
      simp [Movement.rookDelta, hFileZero]
    have hOffset : Movement.rookOffset src tgt = (Movement.rankDiff src tgt).natAbs := by
      simp [Movement.rookOffset, hFileZero, Int.natAbs_neg]

    have ht' : (t : Int) ≤ (Movement.rookOffset src tgt : Int) := Int.ofNat_le.mpr ht

    -- Bounds for file coordinate.
    have hf0 : 0 ≤ src.fileInt := Square.fileInt_nonneg src
    have hf8 : src.fileInt < 8 := Square.fileInt_lt_8 src

    -- Use the target equation at full offset to relate the ray endpoint to `tgt`.
    have hTgt := Movement.squareFromInts_rookDelta_rookOffset src tgt hRook
    have hRankEnd :
        tgt.rankInt =
          src.rankInt + Movement.signInt (-Movement.rankDiff src tgt) * (Movement.rookOffset src tgt : Int) := by
      have :=
        Movement.squareFromInts_rankInt
          (src.fileInt + (Movement.rookDelta src tgt).1 * (Movement.rookOffset src tgt : Int))
          (src.rankInt + (Movement.rookDelta src tgt).2 * (Movement.rookOffset src tgt : Int))
          tgt hTgt
      simpa [hDelta] using this

    -- Bounds for rank coordinate at step `t` (between src and tgt).
    have hr0 : 0 ≤ src.rankInt := Square.rankInt_nonneg src
    have hr8 : src.rankInt < 8 := Square.rankInt_lt_8 src
    have htgt0 : 0 ≤ tgt.rankInt := Square.rankInt_nonneg tgt
    have htgt8 : tgt.rankInt < 8 := Square.rankInt_lt_8 tgt

    have hDirCases :
        Movement.signInt (-Movement.rankDiff src tgt) = 1 ∨
          Movement.signInt (-Movement.rankDiff src tgt) = -1 := by
      have h0 : (-Movement.rankDiff src tgt) ≠ 0 := by
        intro h
        have : Movement.rankDiff src tgt = 0 := by omega
        exact hRankNe this
      by_cases hPos : (-Movement.rankDiff src tgt) > 0
      · left
        unfold Movement.signInt
        rw [if_neg h0]
        rw [if_pos hPos]
      · right
        unfold Movement.signInt
        rw [if_neg h0]
        rw [if_neg hPos]

    -- Prove in-bounds for the rank coordinate via the direction case split.
    have hrBound : 0 ≤ src.rankInt + Movement.signInt (-Movement.rankDiff src tgt) * (t : Int) ∧
        src.rankInt + Movement.signInt (-Movement.rankDiff src tgt) * (t : Int) < 8 := by
      cases hDirCases with
      | inl hDir =>
          -- Increasing: between src.rankInt and tgt.rankInt.
          have htNonneg : 0 ≤ (t : Int) := Int.natCast_nonneg t
          have hLeEnd :
              src.rankInt + (t : Int) ≤
                src.rankInt + (Movement.rookOffset src tgt : Int) := by
            omega
          have hLeTgt :
              src.rankInt + (t : Int) ≤ tgt.rankInt := by
            -- Use the endpoint equality and monotonicity.
            have : src.rankInt + (Movement.rookOffset src tgt : Int) = tgt.rankInt := by
              simpa [hDir] using hRankEnd.symm
            omega
          have hGe0 : 0 ≤ src.rankInt + (t : Int) := by omega
          have hLt8 : src.rankInt + (t : Int) < 8 := by
            omega
          simpa [hDir] using ⟨hGe0, hLt8⟩
      | inr hDir =>
          -- Decreasing: between tgt.rankInt and src.rankInt.
          have htNonneg : 0 ≤ (t : Int) := Int.natCast_nonneg t
          have hLeEnd :
              src.rankInt - (t : Int) ≥
                src.rankInt - (Movement.rookOffset src tgt : Int) := by
            omega
          have hGeTgt :
              tgt.rankInt ≤ src.rankInt - (t : Int) := by
            have : src.rankInt - (Movement.rookOffset src tgt : Int) = tgt.rankInt := by
              -- From endpoint: src + (-1)*k = tgt.
              have : src.rankInt + (-1 : Int) * (Movement.rookOffset src tgt : Int) = tgt.rankInt := by
                simpa [hDir] using hRankEnd.symm
              simpa using this
            omega
          have hGe0 : 0 ≤ src.rankInt - (t : Int) := by
            omega
          have hLt8 : src.rankInt - (t : Int) < 8 := by
            omega
          simpa [hDir] using ⟨hGe0, hLt8⟩

    -- Now build the witness by unfolding `squareFromInts` with the bounds.
    let f : Int := src.fileInt
    let r : Int := src.rankInt + Movement.signInt (-Movement.rankDiff src tgt) * (t : Int)
    have hBounds : 0 ≤ f ∧ f < 8 ∧ 0 ≤ r ∧ r < 8 := by
      exact ⟨hf0, hf8, hrBound.1, hrBound.2⟩
    refine ⟨Square.mkUnsafe (Int.toNat f) (Int.toNat r), ?_⟩
    unfold Movement.squareFromInts
    simp [hBounds, f, r, hDelta]
  · -- Horizontal: rank fixed, file moves (symmetric to the vertical case; reuse bounds reasoning).
    -- We only need existence, and we can mirror the vertical argument by swapping file/rank.
    have hFileNe : Movement.fileDiff src tgt ≠ 0 := by
      intro h0
      exact hFileZero h0
    have hDelta : Movement.rookDelta src tgt = (Movement.signInt (-Movement.fileDiff src tgt), 0) := by
      simp [Movement.rookDelta, hFileZero]
    have hStraight : Movement.rankDiff src tgt = 0 := by
      cases hRook.2 with
      | inl h =>
          -- Contradiction: vertical case would require fileDiff = 0.
          cases (hFileZero h.1)
      | inr h => exact h.1
    have hOffset : Movement.rookOffset src tgt = (Movement.fileDiff src tgt).natAbs := by
      simp [Movement.rookOffset, hStraight]

    have hf0 : 0 ≤ src.fileInt := Square.fileInt_nonneg src
    have hf8 : src.fileInt < 8 := Square.fileInt_lt_8 src
    have hr0 : 0 ≤ src.rankInt := Square.rankInt_nonneg src
    have hr8 : src.rankInt < 8 := Square.rankInt_lt_8 src

    have hTgt := Movement.squareFromInts_rookDelta_rookOffset src tgt hRook
    have hFileEnd :
        tgt.fileInt =
          src.fileInt + Movement.signInt (-Movement.fileDiff src tgt) * (Movement.rookOffset src tgt : Int) := by
      have :=
        Movement.squareFromInts_fileInt
          (src.fileInt + (Movement.rookDelta src tgt).1 * (Movement.rookOffset src tgt : Int))
          (src.rankInt + (Movement.rookDelta src tgt).2 * (Movement.rookOffset src tgt : Int))
          tgt hTgt
      simpa [hDelta] using this

    have ht' : (t : Int) ≤ (Movement.rookOffset src tgt : Int) := Int.ofNat_le.mpr ht

    have hDirCases :
        Movement.signInt (-Movement.fileDiff src tgt) = 1 ∨
          Movement.signInt (-Movement.fileDiff src tgt) = -1 := by
      have h0 : (-Movement.fileDiff src tgt) ≠ 0 := by
        intro h
        have : Movement.fileDiff src tgt = 0 := by omega
        exact hFileNe this
      by_cases hPos : (-Movement.fileDiff src tgt) > 0
      · left
        unfold Movement.signInt
        rw [if_neg h0]
        rw [if_pos hPos]
      · right
        unfold Movement.signInt
        rw [if_neg h0]
        rw [if_neg hPos]

    have hFileBound : 0 ≤ src.fileInt + Movement.signInt (-Movement.fileDiff src tgt) * (t : Int) ∧
        src.fileInt + Movement.signInt (-Movement.fileDiff src tgt) * (t : Int) < 8 := by
      cases hDirCases with
      | inl hDir =>
          have hLeTgt :
              src.fileInt + (t : Int) ≤ tgt.fileInt := by
            have : src.fileInt + (Movement.rookOffset src tgt : Int) = tgt.fileInt := by
              simpa [hDir] using hFileEnd.symm
            omega
          have hGe0 : 0 ≤ src.fileInt + (t : Int) := by omega
          have hLt8 : src.fileInt + (t : Int) < 8 := by
            have htgt8 : tgt.fileInt < 8 := Square.fileInt_lt_8 tgt
            omega
          have hPair : 0 ≤ src.fileInt + (t : Int) ∧ src.fileInt + (t : Int) < 8 := ⟨hGe0, hLt8⟩
          simpa [hDir] using hPair
      | inr hDir =>
          have hGeTgt :
              tgt.fileInt ≤ src.fileInt - (t : Int) := by
            have : src.fileInt + (-1 : Int) * (Movement.rookOffset src tgt : Int) = tgt.fileInt := by
              simpa [hDir] using hFileEnd.symm
            -- Use `t ≤ rookOffset` to weaken the subtraction.
            omega
          have htNonneg : 0 ≤ (t : Int) := Int.natCast_nonneg t
          have htgt0 : 0 ≤ tgt.fileInt := Square.fileInt_nonneg tgt
          have hGe0le : (t : Int) ≤ src.fileInt := by
            -- From `tgt.fileInt ≤ src.fileInt - t` and `0 ≤ tgt.fileInt`, we get `0 ≤ src.fileInt - t`.
            have : 0 ≤ src.fileInt - (t : Int) := by omega
            exact (Int.sub_nonneg).1 this
          have hGe0Add : 0 ≤ src.fileInt + (-(t : Int)) := by
            have : 0 ≤ src.fileInt - (t : Int) := (Int.sub_nonneg).2 hGe0le
            simpa [Int.sub_eq_add_neg] using this
          have hLt8Sub : src.fileInt - (t : Int) < 8 := by omega
          have hLt8Add : src.fileInt + (-(t : Int)) < 8 := by
            simpa [Int.sub_eq_add_neg] using hLt8Sub
          have hGe0' : 0 ≤ src.fileInt + (-1 : Int) * (t : Int) := by simpa using hGe0Add
          have hLt8' : src.fileInt + (-1 : Int) * (t : Int) < 8 := by simpa using hLt8Add
          simpa [hDir] using (And.intro hGe0' hLt8')

    let f : Int := src.fileInt + Movement.signInt (-Movement.fileDiff src tgt) * (t : Int)
    let r : Int := src.rankInt
    have hBounds : 0 ≤ f ∧ f < 8 ∧ 0 ≤ r ∧ r < 8 := by
      exact ⟨hFileBound.1, hFileBound.2, hr0, hr8⟩
    refine ⟨Square.mkUnsafe (Int.toNat f) (Int.toNat r), ?_⟩
    unfold Movement.squareFromInts
    simp [hBounds, f, r, hDelta]

theorem squareFromInts_bishopDelta_bishopOffset (src tgt : Square) (hDiag : Movement.isDiagonal src tgt) :
    Movement.squareFromInts
        (src.fileInt + (Movement.bishopDelta src tgt).1 * (Movement.bishopOffset src tgt : Int))
        (src.rankInt + (Movement.bishopDelta src tgt).2 * (Movement.bishopOffset src tgt : Int)) =
      some tgt := by
  simp [Movement.bishopDelta, Movement.bishopOffset]
  have hAbs :
      Movement.absInt (Movement.fileDiff src tgt) = Movement.absInt (Movement.rankDiff src tgt) := by
    simpa using hDiag.2
  by_cases hFileZero : Movement.fileDiff src tgt = 0
  · -- Diagonal with fileDelta = 0 forces rankDelta = 0, contradicting `src ≠ tgt`.
    have hRankAbs0 : Movement.absInt (Movement.rankDiff src tgt) = 0 := by
      simpa [hFileZero, Movement.absInt] using Eq.trans (Eq.symm hAbs) rfl
    have hRankZero : Movement.rankDiff src tgt = 0 := by
      by_cases hNonneg : 0 ≤ Movement.rankDiff src tgt
      · simpa [Movement.absInt, hNonneg] using hRankAbs0
      ·
        have : -Movement.rankDiff src tgt = 0 := by
          simpa [Movement.absInt, hNonneg] using hRankAbs0
        omega
    have hFileEq : tgt.fileInt = src.fileInt := by
      unfold Movement.fileDiff at hFileZero
      omega
    have hRankEq : tgt.rankInt = src.rankInt := by
      unfold Movement.rankDiff at hRankZero
      omega
    have hEq : src = tgt := by
      cases src with
      | mk srcFile srcRank =>
          cases tgt with
          | mk tgtFile tgtRank =>
              -- Use `fileInt` / `rankInt` equality to show Fin coordinates match.
              have hFileVal : srcFile.val = tgtFile.val := by
                -- unfold the coordinate equations
                unfold Square.fileInt File.toNat at hFileEq
                exact Int.ofNat.inj hFileEq.symm
              have hRankVal : srcRank.val = tgtRank.val := by
                unfold Square.rankInt Rank.toNat at hRankEq
                exact Int.ofNat.inj hRankEq.symm
              have hFile : srcFile = tgtFile := Fin.ext hFileVal
              have hRank : srcRank = tgtRank := Fin.ext hRankVal
              simp [hFile, hRank]
    cases hDiag.1 hEq
  · -- Proper diagonal: use the sign/abs decomposition for both coordinates.
    have hFileMul :
        Movement.signInt (-Movement.fileDiff src tgt) * ((Movement.fileDiff src tgt).natAbs : Int) =
          -Movement.fileDiff src tgt := by
      have := Movement.signInt_mul_natAbs (-Movement.fileDiff src tgt)
      simpa [Int.natAbs_neg] using this
    have hRankMul :
        Movement.signInt (-Movement.rankDiff src tgt) * ((Movement.rankDiff src tgt).natAbs : Int) =
          -Movement.rankDiff src tgt := by
      have := Movement.signInt_mul_natAbs (-Movement.rankDiff src tgt)
      simpa [Int.natAbs_neg] using this
    -- Use diagonal equality of absolute values to rewrite `rankDelta.natAbs` as `fileDelta.natAbs`.
    have hNatAbs : (Movement.rankDiff src tgt).natAbs = (Movement.fileDiff src tgt).natAbs := by
      have hToNat := congrArg Int.toNat hAbs
      -- `Int.toNat (absInt x) = natAbs x` for our local `absInt` definition.
      have hToNatAbs (x : Int) : Int.toNat (Movement.absInt x) = x.natAbs := by
        cases x with
        | ofNat n =>
            simp [Movement.absInt]
        | negSucc n =>
            simp [Movement.absInt]
      -- `toNat` produces equality in the opposite direction; flip it for convenience.
      simpa [hToNatAbs] using Eq.symm hToNat
    have hFileEq :
        src.fileInt +
            Movement.signInt (-Movement.fileDiff src tgt) * ((Movement.fileDiff src tgt).natAbs : Int) =
          tgt.fileInt := by
      have hBase : src.fileInt + (-Movement.fileDiff src tgt) = tgt.fileInt := by
        unfold Movement.fileDiff
        omega
      simpa [hFileMul] using hBase
    have hRankEq :
        src.rankInt +
            Movement.signInt (-Movement.rankDiff src tgt) * ((Movement.fileDiff src tgt).natAbs : Int) =
          tgt.rankInt := by
      -- Rewrite natAbs via diagonal equality, then apply the multiplication lemma.
      have hRankMul' :
          Movement.signInt (-Movement.rankDiff src tgt) * ((Movement.fileDiff src tgt).natAbs : Int) =
            -Movement.rankDiff src tgt := by
        simpa [hNatAbs] using hRankMul
      have hBase : src.rankInt + (-Movement.rankDiff src tgt) = tgt.rankInt := by
        unfold Movement.rankDiff
        omega
      simpa [hRankMul'] using hBase
    simp [hFileEq, hRankEq, Movement.squareFromInts_of_coords tgt]

theorem squareFromInts_bishopDelta_step_some (src tgt : Square) (hDiag : Movement.isDiagonal src tgt) (t : Nat)
    (ht : t ≤ Movement.bishopOffset src tgt) :
    ∃ sq,
      Movement.squareFromInts (src.fileInt + (Movement.bishopDelta src tgt).1 * (t : Int))
          (src.rankInt + (Movement.bishopDelta src tgt).2 * (t : Int)) =
        some sq := by
  -- Extract the endpoint equality at full offset.
  have hTgt := Movement.squareFromInts_bishopDelta_bishopOffset src tgt hDiag
  have hFileEnd :
      tgt.fileInt =
        src.fileInt + Movement.signInt (-Movement.fileDiff src tgt) * (Movement.bishopOffset src tgt : Int) := by
    have :=
      Movement.squareFromInts_fileInt
        (src.fileInt + (Movement.bishopDelta src tgt).1 * (Movement.bishopOffset src tgt : Int))
        (src.rankInt + (Movement.bishopDelta src tgt).2 * (Movement.bishopOffset src tgt : Int))
        tgt hTgt
    simpa [Movement.bishopDelta] using this
  have hRankEnd :
      tgt.rankInt =
        src.rankInt + Movement.signInt (-Movement.rankDiff src tgt) * (Movement.bishopOffset src tgt : Int) := by
    have :=
      Movement.squareFromInts_rankInt
        (src.fileInt + (Movement.bishopDelta src tgt).1 * (Movement.bishopOffset src tgt : Int))
        (src.rankInt + (Movement.bishopDelta src tgt).2 * (Movement.bishopOffset src tgt : Int))
        tgt hTgt
    simpa [Movement.bishopDelta] using this

  have hFdNe : Movement.fileDiff src tgt ≠ 0 := by
    intro hFd0
    have hAbs0 : Movement.absInt (Movement.rankDiff src tgt) = 0 := by
      simpa [hFd0, Movement.absInt] using (Eq.symm hDiag.2)
    have hRd0 : Movement.rankDiff src tgt = 0 := by
      by_cases hNonneg : 0 ≤ Movement.rankDiff src tgt
      · simpa [Movement.absInt, hNonneg] using hAbs0
      ·
        have : -Movement.rankDiff src tgt = 0 := by
          simpa [Movement.absInt, hNonneg] using hAbs0
        omega
    have hFileEq : tgt.fileInt = src.fileInt := by
      unfold Movement.fileDiff at hFd0
      omega
    have hRankEq : tgt.rankInt = src.rankInt := by
      unfold Movement.rankDiff at hRd0
      omega
    have hEq : src = tgt := by
      cases src with
      | mk srcFile srcRank =>
          cases tgt with
          | mk tgtFile tgtRank =>
              have hFileVal : srcFile.val = tgtFile.val := by
                unfold Square.fileInt File.toNat at hFileEq
                exact Int.ofNat.inj hFileEq.symm
              have hRankVal : srcRank.val = tgtRank.val := by
                unfold Square.rankInt Rank.toNat at hRankEq
                exact Int.ofNat.inj hRankEq.symm
              have hFile : srcFile = tgtFile := Fin.ext hFileVal
              have hRank : srcRank = tgtRank := Fin.ext hRankVal
              simp [hFile, hRank]
    exact hDiag.1 hEq

  have hRdNe : Movement.rankDiff src tgt ≠ 0 := by
    intro hRd0
    have hAbs0 : Movement.absInt (Movement.fileDiff src tgt) = 0 := by
      simpa [hRd0, Movement.absInt] using hDiag.2
    have hFd0 : Movement.fileDiff src tgt = 0 := by
      by_cases hNonneg : 0 ≤ Movement.fileDiff src tgt
      · simpa [Movement.absInt, hNonneg] using hAbs0
      ·
        have : -Movement.fileDiff src tgt = 0 := by
          simpa [Movement.absInt, hNonneg] using hAbs0
        omega
    exact hFdNe hFd0

  have ht' : (t : Int) ≤ (Movement.bishopOffset src tgt : Int) := Int.ofNat_le.mpr ht

  have hFileDirCases :
      Movement.signInt (-Movement.fileDiff src tgt) = 1 ∨
        Movement.signInt (-Movement.fileDiff src tgt) = -1 := by
    have h0 : (-Movement.fileDiff src tgt) ≠ 0 := by
      intro h
      have : Movement.fileDiff src tgt = 0 := by omega
      exact hFdNe this
    by_cases hPos : (-Movement.fileDiff src tgt) > 0
    · left
      unfold Movement.signInt
      rw [if_neg h0]
      rw [if_pos hPos]
    · right
      unfold Movement.signInt
      rw [if_neg h0]
      rw [if_neg hPos]

  have hRankDirCases :
      Movement.signInt (-Movement.rankDiff src tgt) = 1 ∨
        Movement.signInt (-Movement.rankDiff src tgt) = -1 := by
    have h0 : (-Movement.rankDiff src tgt) ≠ 0 := by
      intro h
      have : Movement.rankDiff src tgt = 0 := by omega
      exact hRdNe this
    by_cases hPos : (-Movement.rankDiff src tgt) > 0
    · left
      unfold Movement.signInt
      rw [if_neg h0]
      rw [if_pos hPos]
    · right
      unfold Movement.signInt
      rw [if_neg h0]
      rw [if_neg hPos]

  have hf0 : 0 ≤ src.fileInt := Square.fileInt_nonneg src
  have hf8 : src.fileInt < 8 := Square.fileInt_lt_8 src
  have hr0 : 0 ≤ src.rankInt := Square.rankInt_nonneg src
  have hr8 : src.rankInt < 8 := Square.rankInt_lt_8 src
  have htgtFile0 : 0 ≤ tgt.fileInt := Square.fileInt_nonneg tgt
  have htgtFile8 : tgt.fileInt < 8 := Square.fileInt_lt_8 tgt
  have htgtRank0 : 0 ≤ tgt.rankInt := Square.rankInt_nonneg tgt
  have htgtRank8 : tgt.rankInt < 8 := Square.rankInt_lt_8 tgt

  have hfBound :
      0 ≤ src.fileInt + Movement.signInt (-Movement.fileDiff src tgt) * (t : Int) ∧
        src.fileInt + Movement.signInt (-Movement.fileDiff src tgt) * (t : Int) < 8 := by
    cases hFileDirCases with
    | inl hDir =>
        have hLeTgt :
            src.fileInt + (t : Int) ≤ tgt.fileInt := by
          have : src.fileInt + (Movement.bishopOffset src tgt : Int) = tgt.fileInt := by
            simpa [hDir] using hFileEnd.symm
          omega
        have hGe0 : 0 ≤ src.fileInt + (t : Int) := by omega
        have hLt8 : src.fileInt + (t : Int) < 8 := by omega
        simpa [hDir] using ⟨hGe0, hLt8⟩
    | inr hDir =>
        have hGeTgt :
            tgt.fileInt ≤ src.fileInt + (-1 : Int) * (t : Int) := by
          have : src.fileInt + (-1 : Int) * (Movement.bishopOffset src tgt : Int) = tgt.fileInt := by
            simpa [hDir] using hFileEnd.symm
          omega
        have hGe0 : 0 ≤ src.fileInt + (-1 : Int) * (t : Int) := by omega
        have hLt8 : src.fileInt + (-1 : Int) * (t : Int) < 8 := by omega
        have hGe0' : 0 ≤ src.fileInt + (-(t : Int)) := by
          simpa [Int.neg_one_mul] using hGe0
        have hLt8' : src.fileInt + (-(t : Int)) < 8 := by
          simpa [Int.neg_one_mul] using hLt8
        simpa [hDir] using ⟨hGe0', hLt8'⟩

  have hrBound :
      0 ≤ src.rankInt + Movement.signInt (-Movement.rankDiff src tgt) * (t : Int) ∧
        src.rankInt + Movement.signInt (-Movement.rankDiff src tgt) * (t : Int) < 8 := by
    cases hRankDirCases with
    | inl hDir =>
        have hLeTgt :
            src.rankInt + (t : Int) ≤ tgt.rankInt := by
          have : src.rankInt + (Movement.bishopOffset src tgt : Int) = tgt.rankInt := by
            simpa [hDir] using hRankEnd.symm
          omega
        have hGe0 : 0 ≤ src.rankInt + (t : Int) := by omega
        have hLt8 : src.rankInt + (t : Int) < 8 := by omega
        simpa [hDir] using ⟨hGe0, hLt8⟩
    | inr hDir =>
        have hGeTgt :
            tgt.rankInt ≤ src.rankInt + (-1 : Int) * (t : Int) := by
          have : src.rankInt + (-1 : Int) * (Movement.bishopOffset src tgt : Int) = tgt.rankInt := by
            simpa [hDir] using hRankEnd.symm
          omega
        have hGe0 : 0 ≤ src.rankInt + (-1 : Int) * (t : Int) := by omega
        have hLt8 : src.rankInt + (-1 : Int) * (t : Int) < 8 := by omega
        have hGe0' : 0 ≤ src.rankInt + (-(t : Int)) := by
          simpa [Int.neg_one_mul] using hGe0
        have hLt8' : src.rankInt + (-(t : Int)) < 8 := by
          simpa [Int.neg_one_mul] using hLt8
        simpa [hDir] using ⟨hGe0', hLt8'⟩

  let f : Int := src.fileInt + Movement.signInt (-Movement.fileDiff src tgt) * (t : Int)
  let r : Int := src.rankInt + Movement.signInt (-Movement.rankDiff src tgt) * (t : Int)
  have hBounds : 0 ≤ f ∧ f < 8 ∧ 0 ≤ r ∧ r < 8 := by
    exact ⟨by simpa [f] using hfBound.1, by simpa [f] using hfBound.2, by simpa [r] using hrBound.1,
      by simpa [r] using hrBound.2⟩
  refine ⟨Square.mkUnsafe (Int.toNat f) (Int.toNat r), ?_⟩
  unfold Movement.squareFromInts
  simp [hBounds, f, r, Movement.bishopDelta]

theorem bishopDelta_mem_bishopDeltas (src tgt : Square) (hDiag : Movement.isDiagonal src tgt) :
    Movement.bishopDelta src tgt ∈ [(1, 1), (-1, -1), (1, -1), (-1, 1)] := by
  have hFdNe : Movement.fileDiff src tgt ≠ 0 := by
    intro hFd0
    have hAbs0 : Movement.absInt (Movement.rankDiff src tgt) = 0 := by
      simpa [hFd0, Movement.absInt] using (Eq.symm hDiag.2)
    have hRd0 : Movement.rankDiff src tgt = 0 := by
      by_cases hNonneg : 0 ≤ Movement.rankDiff src tgt
      · simpa [Movement.absInt, hNonneg] using hAbs0
      ·
        have : -Movement.rankDiff src tgt = 0 := by
          simpa [Movement.absInt, hNonneg] using hAbs0
        omega
    have hFileEq : tgt.fileInt = src.fileInt := by
      unfold Movement.fileDiff at hFd0
      omega
    have hRankEq : tgt.rankInt = src.rankInt := by
      unfold Movement.rankDiff at hRd0
      omega
    have hEq : src = tgt := by
      cases src with
      | mk srcFile srcRank =>
          cases tgt with
          | mk tgtFile tgtRank =>
              have hFileVal : srcFile.val = tgtFile.val := by
                unfold Square.fileInt File.toNat at hFileEq
                exact Int.ofNat.inj hFileEq.symm
              have hRankVal : srcRank.val = tgtRank.val := by
                unfold Square.rankInt Rank.toNat at hRankEq
                exact Int.ofNat.inj hRankEq.symm
              have hFile : srcFile = tgtFile := Fin.ext hFileVal
              have hRank : srcRank = tgtRank := Fin.ext hRankVal
              simp [hFile, hRank]
    exact hDiag.1 hEq
  have hRdNe : Movement.rankDiff src tgt ≠ 0 := by
    intro hRd0
    have hAbs0 : Movement.absInt (Movement.fileDiff src tgt) = 0 := by
      simpa [hRd0, Movement.absInt] using hDiag.2
    have hFd0 : Movement.fileDiff src tgt = 0 := by
      by_cases hNonneg : 0 ≤ Movement.fileDiff src tgt
      · simpa [Movement.absInt, hNonneg] using hAbs0
      ·
        have : -Movement.fileDiff src tgt = 0 := by
          simpa [Movement.absInt, hNonneg] using hAbs0
        omega
    exact hFdNe hFd0

  have hFileDir :
      Movement.signInt (-Movement.fileDiff src tgt) = 1 ∨
        Movement.signInt (-Movement.fileDiff src tgt) = -1 := by
    have h0 : (-Movement.fileDiff src tgt) ≠ 0 := by
      intro h
      have : Movement.fileDiff src tgt = 0 := by omega
      exact hFdNe this
    by_cases hPos : (-Movement.fileDiff src tgt) > 0
    · left
      unfold Movement.signInt
      rw [if_neg h0]
      rw [if_pos hPos]
    · right
      unfold Movement.signInt
      rw [if_neg h0]
      rw [if_neg hPos]

  have hRankDir :
      Movement.signInt (-Movement.rankDiff src tgt) = 1 ∨
        Movement.signInt (-Movement.rankDiff src tgt) = -1 := by
    have h0 : (-Movement.rankDiff src tgt) ≠ 0 := by
      intro h
      have : Movement.rankDiff src tgt = 0 := by omega
      exact hRdNe this
    by_cases hPos : (-Movement.rankDiff src tgt) > 0
    · left
      unfold Movement.signInt
      rw [if_neg h0]
      rw [if_pos hPos]
    · right
      unfold Movement.signInt
      rw [if_neg h0]
      rw [if_neg hPos]

  unfold Movement.bishopDelta
  simp
  cases hFileDir with
  | inl hF =>
      cases hRankDir with
      | inl hR => simp [hF, hR]
      | inr hR => simp [hF, hR]
  | inr hF =>
      cases hRankDir with
      | inl hR => simp [hF, hR]
      | inr hR => simp [hF, hR]

theorem bishop_step_square_mem_squaresBetween
    (src tgt : Square) (hDiag : Movement.isDiagonal src tgt)
    (t : Nat) (ht1 : 1 ≤ t) (htLt : t < Movement.bishopOffset src tgt)
    (sq : Square)
    (hSq :
      Movement.squareFromInts (src.fileInt + (Movement.bishopDelta src tgt).1 * (t : Int))
          (src.rankInt + (Movement.bishopDelta src tgt).2 * (t : Int)) =
        some sq) :
    sq ∈ Movement.squaresBetween src tgt := by
  have htLt' : t < (Movement.fileDiff src tgt).natAbs := by
    simpa [Movement.bishopOffset] using htLt
  have hStepsGt1 : 1 < (Movement.fileDiff src tgt).natAbs := Nat.lt_of_le_of_lt ht1 htLt'
  unfold Movement.squaresBetween
  simp [hDiag]
  refine ⟨hStepsGt1, ⟨t - 1, ?_, ?_⟩⟩
  · have htPos : 0 < t := Nat.lt_of_lt_of_le Nat.zero_lt_one ht1
    have : t - 1 < (Movement.fileDiff src tgt).natAbs - 1 :=
      Movement.range_membership_of_offset (Movement.fileDiff src tgt).natAbs t htPos htLt'
    simpa using this
  · have hStep : ((t - 1 : Nat) : Int) + 1 = (t : Int) := by
      have htNat : (t - 1) + 1 = t := Nat.sub_add_cancel ht1
      have htSucc : (t - 1).succ = t := by
        simpa [Nat.succ_eq_add_one] using htNat
      calc
        ((t - 1 : Nat) : Int) + 1 = ((t - 1).succ : Int) := by
          simpa using (Eq.symm (Int.natCast_succ (t - 1)))
        _ = (t : Int) := congrArg (fun n : Nat => (n : Int)) htSucc
    have hSq' :
        Movement.squareFromInts
            (src.fileInt + Movement.signInt (-Movement.fileDiff src tgt) * (t : Int))
            (src.rankInt + Movement.signInt (-Movement.rankDiff src tgt) * (t : Int)) =
          some sq := by
      simpa [Movement.bishopDelta] using hSq
    simpa [hStep] using hSq'

theorem rookDelta_mem_rookDeltas (src tgt : Square) (hRook : Movement.isRookMove src tgt) :
    Movement.rookDelta src tgt ∈ [(1, 0), (-1, 0), (0, 1), (0, -1)] := by
  -- Split on vertical vs horizontal.
  by_cases hFileZero : Movement.fileDiff src tgt = 0
  · have hRankNe : Movement.rankDiff src tgt ≠ 0 := by
      cases hRook.2 with
      | inl h => exact h.2
      | inr h => exact (h.2 hFileZero).elim
    have h0 : (-Movement.rankDiff src tgt) ≠ 0 := by
      intro h
      have : Movement.rankDiff src tgt = 0 := by omega
      exact hRankNe this
    have hSign : Movement.signInt (-Movement.rankDiff src tgt) = 1 ∨
        Movement.signInt (-Movement.rankDiff src tgt) = -1 := by
      by_cases hPos : (-Movement.rankDiff src tgt) > 0
      · left
        unfold Movement.signInt
        rw [if_neg h0]
        rw [if_pos hPos]
      · right
        unfold Movement.signInt
        rw [if_neg h0]
        rw [if_neg hPos]
    -- `rookDelta = (0, signInt(-rankDiff))`.
    simp [Movement.rookDelta, hFileZero]
    rcases hSign with hSign | hSign <;> simp [hSign]
  · have hRankZero : Movement.rankDiff src tgt = 0 := by
      cases hRook.2 with
      | inl h => exact (hFileZero h.1).elim
      | inr h => exact h.1
    have hFileNe : Movement.fileDiff src tgt ≠ 0 := by
      intro h0
      exact hFileZero h0
    have h0 : (-Movement.fileDiff src tgt) ≠ 0 := by
      intro h
      have : Movement.fileDiff src tgt = 0 := by omega
      exact hFileNe this
    have hSign : Movement.signInt (-Movement.fileDiff src tgt) = 1 ∨
        Movement.signInt (-Movement.fileDiff src tgt) = -1 := by
      by_cases hPos : (-Movement.fileDiff src tgt) > 0
      · left
        unfold Movement.signInt
        rw [if_neg h0]
        rw [if_pos hPos]
      · right
        unfold Movement.signInt
        rw [if_neg h0]
        rw [if_neg hPos]
    -- `rookDelta = (signInt(-fileDiff), 0)`.
    simp [Movement.rookDelta, hFileZero, hRankZero]
    rcases hSign with hSign | hSign <;> simp [hSign]

theorem rook_step_square_mem_squaresBetween
    (src tgt : Square) (hRook : Movement.isRookMove src tgt)
    (t : Nat) (ht1 : 1 ≤ t) (htLt : t < Movement.rookOffset src tgt)
    (sq : Square)
    (hSq :
      Movement.squareFromInts (src.fileInt + (Movement.rookDelta src tgt).1 * (t : Int))
          (src.rankInt + (Movement.rookDelta src tgt).2 * (t : Int)) =
        some sq) :
    sq ∈ Movement.squaresBetween src tgt := by
  have hStep : ((t - 1 : Nat) : Int) + 1 = (t : Int) := by
    have htNat : (t - 1) + 1 = t := Nat.sub_add_cancel ht1
    have htSucc : (t - 1).succ = t := by
      simpa [Nat.succ_eq_add_one] using htNat
    calc
      ((t - 1 : Nat) : Int) + 1 = ((t - 1).succ : Int) := by
        simpa using (Eq.symm (Int.natCast_succ (t - 1)))
      _ = (t : Int) := by
        exact congrArg (fun n : Nat => (n : Int)) htSucc

  have hNotDiag : ¬ Movement.isDiagonal src tgt := by
    intro hDiag
    have hStraight := Movement.rook_move_straight hRook
    cases hStraight with
    | inl hfd0 =>
        have hLine : Movement.rankDiff src tgt ≠ 0 := by
          cases hRook.2 with
          | inl h => exact h.2
          | inr h =>
              exfalso
              exact h.2 hfd0
        have hAbs0 : (0 : Int) = Movement.absInt (Movement.rankDiff src tgt) := by
          simpa [hfd0, Movement.absInt] using hDiag.2
        have hAbs : Movement.absInt (Movement.rankDiff src tgt) = 0 := by
          exact Eq.symm hAbs0
        have hrd0 : Movement.rankDiff src tgt = 0 := by
          by_cases hNonneg : 0 ≤ Movement.rankDiff src tgt
          · simpa [Movement.absInt, hNonneg] using hAbs
          ·
            have : -Movement.rankDiff src tgt = 0 := by
              simpa [Movement.absInt, hNonneg] using hAbs
            omega
        exact hLine hrd0
    | inr hrd0 =>
        have hLine : Movement.fileDiff src tgt ≠ 0 := by
          cases hRook.2 with
          | inl h =>
              exfalso
              exact h.2 hrd0
          | inr h => exact h.2
        have hAbs : Movement.absInt (Movement.fileDiff src tgt) = 0 := by
          simpa [hrd0, Movement.absInt] using hDiag.2
        have hfd0 : Movement.fileDiff src tgt = 0 := by
          by_cases hNonneg : 0 ≤ Movement.fileDiff src tgt
          · simpa [Movement.absInt, hNonneg] using hAbs
          ·
            have : -Movement.fileDiff src tgt = 0 := by
              simpa [Movement.absInt, hNonneg] using hAbs
            omega
        exact hLine hfd0

  unfold Movement.squaresBetween
  simp [hNotDiag, hRook]
  have htPos : 0 < t := Nat.lt_of_lt_of_le Nat.zero_lt_one ht1
  have hStepsGt1 : 1 < Movement.rookOffset src tgt := Nat.lt_of_le_of_lt ht1 htLt
  refine ⟨hStepsGt1, ⟨t - 1, ?_⟩⟩
  refine ⟨?_, ?_⟩
  · have : t - 1 < Movement.rookOffset src tgt - 1 :=
      Movement.range_membership_of_offset (Movement.rookOffset src tgt) t htPos htLt
    simpa using this
  · by_cases hfd0 : Movement.fileDiff src tgt = 0
    · have hStepFile : Movement.signInt (-Movement.fileDiff src tgt) = 0 := by
        simp [hfd0, Movement.signInt]
      have hEqDelta :
          Movement.rookDelta src tgt = (0, Movement.signInt (-Movement.rankDiff src tgt)) := by
        simp [Movement.rookDelta, hfd0]
      have hSq' :
          Movement.squareFromInts (src.fileInt + 0 * (t : Int))
              (src.rankInt + Movement.signInt (-Movement.rankDiff src tgt) * (t : Int)) =
            some sq := by
        simpa [hEqDelta] using hSq
      have hSqStep :
          Movement.squareFromInts (src.fileInt + 0 * (((t - 1 : Nat) : Int) + 1))
              (src.rankInt +
                  Movement.signInt (-Movement.rankDiff src tgt) * (((t - 1 : Nat) : Int) + 1)) =
            some sq := by
        simpa [hStep] using hSq'
      simpa [hStepFile] using hSqStep
    · have hrd0 : Movement.rankDiff src tgt = 0 := by
        have hStraight := Movement.rook_move_straight hRook
        cases hStraight with
        | inl h => exact (hfd0 h).elim
        | inr h => exact h
      have hStepRank : Movement.signInt (-Movement.rankDiff src tgt) = 0 := by
        simp [hrd0, Movement.signInt]
      have hEqDelta :
          Movement.rookDelta src tgt = (Movement.signInt (-Movement.fileDiff src tgt), 0) := by
        simp [Movement.rookDelta, hfd0]
      have hSq' :
          Movement.squareFromInts
              (src.fileInt + Movement.signInt (-Movement.fileDiff src tgt) * (t : Int))
              (src.rankInt + 0 * (t : Int)) =
            some sq := by
        simpa [hEqDelta] using hSq
      have hSqStep :
          Movement.squareFromInts
              (src.fileInt +
                  Movement.signInt (-Movement.fileDiff src tgt) * (((t - 1 : Nat) : Int) + 1))
              (src.rankInt + 0 * (((t - 1 : Nat) : Int) + 1)) =
            some sq := by
        simpa [hStep] using hSq'
      simpa [hStepRank] using hSqStep

theorem fileDiff_natAbs_le_7 (src tgt : Square) : (Movement.fileDiff src tgt).natAbs ≤ 7 := by
  by_cases hLe : tgt.fileNat ≤ src.fileNat
  · have hDiff : Movement.fileDiff src tgt = Int.ofNat (src.fileNat - tgt.fileNat) := by
      unfold Movement.fileDiff Square.fileInt
      simpa [Square.fileNat] using (Eq.symm (Int.ofNat_sub (m := tgt.fileNat) (n := src.fileNat) hLe))
    have hSrcLe : src.fileNat ≤ 7 := by
      simpa [Square.fileNat, File.toNat] using (Nat.lt_succ_iff.mp src.file.isLt)
    have hSubLe : src.fileNat - tgt.fileNat ≤ 7 := Nat.le_trans (Nat.sub_le _ _) hSrcLe
    simpa [hDiff] using hSubLe
  · have hLt : src.fileNat < tgt.fileNat := Nat.lt_of_not_ge hLe
    have hLe' : src.fileNat ≤ tgt.fileNat := Nat.le_of_lt hLt
    have hDiff : Movement.fileDiff src tgt = -Int.ofNat (tgt.fileNat - src.fileNat) := by
      unfold Movement.fileDiff Square.fileInt
      have hOfNatSub :
          (Int.ofNat tgt.fileNat - Int.ofNat src.fileNat) = (Int.ofNat (tgt.fileNat - src.fileNat)) := by
        simpa using (Eq.symm (Int.ofNat_sub (m := src.fileNat) (n := tgt.fileNat) hLe'))
      have hNegSub :
          (Int.ofNat src.fileNat - Int.ofNat tgt.fileNat) = -(Int.ofNat tgt.fileNat - Int.ofNat src.fileNat) := by
        simp [Int.sub_eq_add_neg, Int.neg_add, Int.add_assoc, Int.add_comm, Int.add_left_comm]
      have hNegSub' :
          Movement.fileDiff src tgt = -(Int.ofNat tgt.fileNat - Int.ofNat src.fileNat) := by
        simpa [Square.fileNat, Movement.fileDiff, Square.fileInt] using hNegSub
      calc
        Movement.fileDiff src tgt = -(Int.ofNat tgt.fileNat - Int.ofNat src.fileNat) := hNegSub'
        _ = -Int.ofNat (tgt.fileNat - src.fileNat) := by simpa [hOfNatSub]
    have hTgtLe : tgt.fileNat ≤ 7 := by
      simpa [Square.fileNat, File.toNat] using (Nat.lt_succ_iff.mp tgt.file.isLt)
    have hSubLe : tgt.fileNat - src.fileNat ≤ 7 := Nat.le_trans (Nat.sub_le _ _) hTgtLe
    simpa [hDiff] using hSubLe

theorem rankDiff_natAbs_le_7 (src tgt : Square) : (Movement.rankDiff src tgt).natAbs ≤ 7 := by
  by_cases hLe : tgt.rankNat ≤ src.rankNat
  · have hDiff : Movement.rankDiff src tgt = Int.ofNat (src.rankNat - tgt.rankNat) := by
      unfold Movement.rankDiff Square.rankInt
      simpa [Square.rankNat] using (Eq.symm (Int.ofNat_sub (m := tgt.rankNat) (n := src.rankNat) hLe))
    have hSrcLe : src.rankNat ≤ 7 := by
      simpa [Square.rankNat, Rank.toNat] using (Nat.lt_succ_iff.mp src.rank.isLt)
    have hSubLe : src.rankNat - tgt.rankNat ≤ 7 := Nat.le_trans (Nat.sub_le _ _) hSrcLe
    simpa [hDiff] using hSubLe
  · have hLt : src.rankNat < tgt.rankNat := Nat.lt_of_not_ge hLe
    have hLe' : src.rankNat ≤ tgt.rankNat := Nat.le_of_lt hLt
    have hDiff : Movement.rankDiff src tgt = -Int.ofNat (tgt.rankNat - src.rankNat) := by
      unfold Movement.rankDiff Square.rankInt
      have hOfNatSub :
          (Int.ofNat tgt.rankNat - Int.ofNat src.rankNat) = (Int.ofNat (tgt.rankNat - src.rankNat)) := by
        simpa using (Eq.symm (Int.ofNat_sub (m := src.rankNat) (n := tgt.rankNat) hLe'))
      have hNegSub :
          (Int.ofNat src.rankNat - Int.ofNat tgt.rankNat) = -(Int.ofNat tgt.rankNat - Int.ofNat src.rankNat) := by
        simp [Int.sub_eq_add_neg, Int.neg_add, Int.add_assoc, Int.add_comm, Int.add_left_comm]
      have hNegSub' :
          Movement.rankDiff src tgt = -(Int.ofNat tgt.rankNat - Int.ofNat src.rankNat) := by
        simpa [Square.rankNat, Movement.rankDiff, Square.rankInt] using hNegSub
      calc
        Movement.rankDiff src tgt = -(Int.ofNat tgt.rankNat - Int.ofNat src.rankNat) := hNegSub'
        _ = -Int.ofNat (tgt.rankNat - src.rankNat) := by simpa [hOfNatSub]
    have hTgtLe : tgt.rankNat ≤ 7 := by
      simpa [Square.rankNat, Rank.toNat] using (Nat.lt_succ_iff.mp tgt.rank.isLt)
    have hSubLe : tgt.rankNat - src.rankNat ≤ 7 := Nat.le_trans (Nat.sub_le _ _) hTgtLe
    simpa [hDiff] using hSubLe

theorem rookOffset_le_7 (src tgt : Square) (hRook : Movement.isRookMove src tgt) :
    Movement.rookOffset src tgt ≤ 7 := by
  unfold Movement.rookOffset
  cases hRook.2 with
  | inl h =>
      -- fileDiff = 0
      simpa [h.1] using (rankDiff_natAbs_le_7 src tgt)
  | inr h =>
      -- rankDiff = 0
      simpa [h.1] using (fileDiff_natAbs_le_7 src tgt)

end Movement

end Chess
