import Chess.Core

namespace Chess

namespace Board

private def pairsFromSquares (b : Board) : List Square → List (Square × Piece)
  | [] => []
  | sq :: rest =>
      match b.get sq with
      | some p => (sq, p) :: pairsFromSquares b rest
      | none => pairsFromSquares b rest

private theorem pairsFromSquares_eq_filterMap (b : Board) (l : List Square) :
    pairsFromSquares b l =
      l.filterMap (fun sq =>
        match b.get sq with
        | some p => some (sq, p)
        | none => none) := by
  induction l with
  | nil =>
      simp [pairsFromSquares]
  | cons sq rest ih =>
      cases h : b.get sq <;> simp [pairsFromSquares, h, ih]

private theorem mem_pairsFromSquares_iff (b : Board) (l : List Square) (sq : Square) (p : Piece) :
    (sq, p) ∈ pairsFromSquares b l ↔ sq ∈ l ∧ b.get sq = some p := by
  induction l with
  | nil =>
      simp [pairsFromSquares]
  | cons head tail ih =>
      cases hHead : b.get head with
      | none =>
          constructor
          · intro h
            have ht := (ih).1 (by simpa [pairsFromSquares, hHead] using h)
            exact ⟨by simp [ht.1], ht.2⟩
          · rintro ⟨hMem, hEq⟩
            have hTail : sq ∈ tail := by
              have : sq = head ∨ sq ∈ tail := by simpa [List.mem_cons] using hMem
              cases this with
              | inl hSq =>
                  subst hSq
                  have hContra := hEq
                  simp [hHead] at hContra
              | inr ht =>
                  exact ht
            have : (sq, p) ∈ pairsFromSquares b tail := (ih).2 ⟨hTail, hEq⟩
            simpa [pairsFromSquares, hHead] using this
      | some q =>
          constructor
          · intro h
            have : (sq, p) = (head, q) ∨ (sq, p) ∈ pairsFromSquares b tail := by
              simpa [pairsFromSquares, hHead] using h
            cases this with
            | inl hEq =>
                have hSq : sq = head := congrArg Prod.fst hEq
                have hP : p = q := congrArg Prod.snd hEq
                subst hSq
                subst hP
                exact ⟨by simp, by simp [hHead]⟩
            | inr hTail =>
                have ht := (ih).1 hTail
                exact ⟨by simp [ht.1], ht.2⟩
          · rintro ⟨hMem, hEq⟩
            have : sq = head ∨ sq ∈ tail := by simpa [List.mem_cons] using hMem
            cases this with
            | inl hSq =>
                subst hSq
                have : q = p := by
                  have : some q = some p := by simpa [hHead] using hEq
                  exact Option.some.inj this
                subst this
                simp [pairsFromSquares, hHead]
            | inr hTail =>
                have hTail' : (sq, p) ∈ pairsFromSquares b tail := (ih).2 ⟨hTail, hEq⟩
                simp [pairsFromSquares, hHead, hTail']

private theorem toList_eq_pairsFromSquares (b : Board) :
    b.toList = pairsFromSquares b allSquares := by
  unfold Board.toList
  rw [pairsFromSquares_eq_filterMap]
  rfl

private def foldStep (b : Board) (e : Square × Piece) : Board :=
  b.update e.fst (some e.snd)

private theorem empty_get (sq : Square) : Board.empty.get sq = none := by
  unfold Board.get Board.empty
  simp

private theorem foldl_get_of_forall_ne (ps : List (Square × Piece)) (base : Board) (sq : Square)
    (hne : ∀ e ∈ ps, e.fst ≠ sq) :
    (ps.foldl foldStep base).get sq = base.get sq := by
  induction ps generalizing base with
  | nil =>
      simp
  | cons head tail ih =>
      have hHeadNe : head.fst ≠ sq := hne head (by simp)
      have hTailNe : ∀ e ∈ tail, e.fst ≠ sq := by
        intro e he
        exact hne e (by simp [he])
      have hGetStep : (foldStep base head).get sq = base.get sq := by
        apply Board.update_ne
        intro hEq
        apply hHeadNe
        simpa using hEq.symm
      simp [List.foldl, hGetStep, ih _ hTailNe]

private theorem foldl_get_preserve_value (ps : List (Square × Piece)) (base : Board) (sq : Square) (p : Piece)
    (hBase : base.get sq = some p)
    (hUniq : ∀ q, (sq, q) ∈ ps → q = p) :
    (ps.foldl foldStep base).get sq = some p := by
  induction ps generalizing base with
  | nil =>
      simpa using hBase
  | cons head tail ih =>
      rcases head with ⟨s0, p0⟩
      by_cases hEq : s0 = sq
      · have hP0 : p0 = p := hUniq p0 (by simp [hEq])
        have hBase' : (foldStep base (s0, p0)).get sq = some p := by
          subst hEq
          simp [foldStep, hP0, Board.update_eq]
        have hUniqTail : ∀ q, (sq, q) ∈ tail → q = p := by
          intro q hq
          exact hUniq q (by simp [hq])
        simpa [List.foldl] using ih (base := foldStep base (s0, p0)) hBase' hUniqTail
      · have hNe : sq ≠ s0 := by
          intro h
          apply hEq
          simpa using h.symm
        have hBase' : (foldStep base (s0, p0)).get sq = some p := by
          simpa [foldStep, hBase] using (Board.update_ne base s0 (some p0) hNe)
        have hUniqTail : ∀ q, (sq, q) ∈ tail → q = p := by
          intro q hq
          exact hUniq q (by simp [hq])
        simpa [List.foldl] using ih (base := foldStep base (s0, p0)) hBase' hUniqTail

private theorem foldl_get_of_mem_and_uniq (ps : List (Square × Piece)) (base : Board) (sq : Square) (p : Piece)
    (hBase : base.get sq = none)
    (hMem : (sq, p) ∈ ps)
    (hUniq : ∀ q, (sq, q) ∈ ps → q = p) :
    (ps.foldl foldStep base).get sq = some p := by
  induction ps generalizing base with
  | nil =>
      cases hMem
  | cons head tail ih =>
      rcases head with ⟨s0, p0⟩
      by_cases hEq : s0 = sq
      · have hP0 : p0 = p := hUniq p0 (by simp [hEq])
        have hBase' : (foldStep base (s0, p0)).get sq = some p := by
          subst hEq
          simp [foldStep, hP0, Board.update_eq]
        have hUniqTail : ∀ q, (sq, q) ∈ tail → q = p := by
          intro q hq
          exact hUniq q (by simp [hq])
        exact foldl_get_preserve_value tail (foldStep base (s0, p0)) sq p hBase' hUniqTail
      · have hNe : sq ≠ s0 := by
          intro h
          apply hEq
          simpa using h.symm
        have hBase' : (foldStep base (s0, p0)).get sq = none := by
          simpa [foldStep, hBase] using (Board.update_ne base s0 (some p0) hNe)
        have hMemTail : (sq, p) ∈ tail := by
          have : (sq, p) = (s0, p0) ∨ (sq, p) ∈ tail := by
            simpa [List.mem_cons] using hMem
          cases this with
          | inl hContra =>
              have : sq = s0 := congrArg Prod.fst hContra
              exact (hEq this.symm).elim
          | inr hTail =>
              exact hTail
        have hUniqTail : ∀ q, (sq, q) ∈ tail → q = p := by
          intro q hq
          exact hUniq q (by simp [hq])
        simpa [List.foldl] using ih (base := foldStep base (s0, p0)) hBase' hMemTail hUniqTail

theorem fromList_get_eq_none_of_forall_ne (ps : List (Square × Piece)) (sq : Square)
    (hne : ∀ e ∈ ps, e.fst ≠ sq) :
    (Board.fromList ps).get sq = none := by
  have hKeep : (ps.foldl foldStep Board.empty).get sq = Board.empty.get sq :=
    foldl_get_of_forall_ne ps Board.empty sq hne
  have : (Board.fromList ps).get sq = Board.empty.get sq := by
    simpa [Board.fromList, foldStep] using hKeep
  simpa [empty_get] using this

theorem fromList_get_eq_some_of_mem_unique (ps : List (Square × Piece)) (sq : Square) (p : Piece)
    (hMem : (sq, p) ∈ ps)
    (hUniq : ∀ q, (sq, q) ∈ ps → q = p) :
    (Board.fromList ps).get sq = some p := by
  simpa [Board.fromList, foldStep, empty_get] using
    foldl_get_of_mem_and_uniq ps Board.empty sq p (empty_get sq) hMem hUniq

theorem fromList_toList (b : Board) : Board.fromList (Board.toList b) = b := by
  apply Board.ext_get
  intro sq
  classical
  let ps : List (Square × Piece) := pairsFromSquares b allSquares
  have hps : Board.toList b = ps := by
    simp [ps, toList_eq_pairsFromSquares]
  cases hGet : b.get sq with
  | none =>
      have hNe : ∀ e ∈ ps, e.fst ≠ sq := by
        intro e he
        rcases e with ⟨s, p⟩
        have hb : b.get s = some p := by
          exact (mem_pairsFromSquares_iff b allSquares s p).1 (by simpa [ps] using he) |>.2
        intro hEq
        subst hEq
        have hContra := hb
        simp [hGet] at hContra
      have :
          (Board.fromList ps).get sq = Board.empty.get sq := by
        simpa [Board.fromList, foldStep] using foldl_get_of_forall_ne ps Board.empty sq hNe
      simpa [hps, hGet, empty_get] using this
  | some p =>
      have hMem : (sq, p) ∈ ps := by
        have hs : sq ∈ allSquares := Square.mem_all sq
        exact (mem_pairsFromSquares_iff b allSquares sq p).2 ⟨hs, by simp [hGet]⟩
      have hUniq : ∀ q, (sq, q) ∈ ps → q = p := by
        intro q hq
        have hb : b.get sq = some q := by
          exact (mem_pairsFromSquares_iff b allSquares sq q).1 (by simpa [ps] using hq) |>.2
        have : some q = some p := by simpa [hGet] using hb.symm
        exact Option.some.inj this
      have :
          (Board.fromList ps).get sq = some p := by
        simpa [Board.fromList, foldStep, empty_get] using
          foldl_get_of_mem_and_uniq ps Board.empty sq p (empty_get sq) hMem hUniq
      simpa [hps, hGet] using this

end Board

end Chess
