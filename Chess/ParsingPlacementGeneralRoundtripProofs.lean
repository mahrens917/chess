import Chess.BoardRoundtripProofs
import Chess.Parsing
import Chess.ParsingPlacementRankNoSlashProofs
import Chess.ParsingPlacementRankParsingLemmas
import Chess.ParsingPlacementRankStepLemmas

namespace Chess
namespace Parsing

open Chess

@[simp] theorem except_bind_error {ε α β : Type} (e : ε) (f : α → Except ε β) :
    (Except.error e).bind f = Except.error e := by
  rfl

@[simp] theorem except_bind_ok {ε α β : Type} (a : α) (f : α → Except ε β) :
    (Except.ok a).bind f = f a := by
  rfl

@[simp] theorem except_map_error {ε α β : Type} (f : α → β) (e : ε) :
    f <$> (Except.error e : Except ε α) = Except.error e := by
  rfl

@[simp] theorem except_map_ok {ε α β : Type} (f : α → β) (a : α) :
    f <$> (Except.ok a : Except ε α) = Except.ok (f a) := by
  rfl

theorem Square.mkUnsafe_eq (sq : Square) :
    Square.mkUnsafe sq.fileNat sq.rankNat = sq := by
  unfold Square.mkUnsafe Square.mk?
  have hf : sq.fileNat < 8 := sq.file.isLt
  have hr : sq.rankNat < 8 := sq.rank.isLt
  simp [Square.fileNat, Square.rankNat, File.toNat, Rank.toNat, hf, hr]

private def rankPairsFromCount (board : Board) (rank file : Nat) : Nat → List (Square × Piece)
  | 0 => []
  | Nat.succ n =>
      let rest := rankPairsFromCount board rank (file + 1) n
      match board.get (Square.mkUnsafe file rank) with
      | some p => rest ++ [(Square.mkUnsafe file rank, p)]
      | none => rest

private def rankPairsFrom (board : Board) (rank file : Nat) : List (Square × Piece) :=
  rankPairsFromCount board rank file (8 - file)

private theorem rankPairsFromCount_succ_none (board : Board) (rank file n : Nat)
    (hGet : board.get (Square.mkUnsafe file rank) = none) :
    rankPairsFromCount board rank file (Nat.succ n) = rankPairsFromCount board rank (file + 1) n := by
  simp [rankPairsFromCount, hGet]

private theorem rankPairsFromCount_succ_some (board : Board) (rank file n : Nat) (p : Piece)
    (hGet : board.get (Square.mkUnsafe file rank) = some p) :
    rankPairsFromCount board rank file (Nat.succ n) =
      rankPairsFromCount board rank (file + 1) n ++ [(Square.mkUnsafe file rank, p)] := by
  simp [rankPairsFromCount, hGet]

private theorem rankPairsFrom_succ_none (board : Board) (rank file : Nat)
    (hFile : file < 8)
    (hGet : board.get (Square.mkUnsafe file rank) = none) :
    rankPairsFrom board rank file = rankPairsFrom board rank (file + 1) := by
  unfold rankPairsFrom
  have hSub : 8 - file = Nat.succ (8 - (file + 1)) := by
    have : 8 - file > 0 := Nat.sub_pos_of_lt hFile
    exact (Nat.succ_pred_eq_of_pos this).symm
  rw [hSub]
  simpa using rankPairsFromCount_succ_none (board := board) (rank := rank) (file := file)
    (n := 8 - (file + 1)) hGet

private theorem rankPairsFrom_succ_some (board : Board) (rank file : Nat) (p : Piece)
    (hFile : file < 8)
    (hGet : board.get (Square.mkUnsafe file rank) = some p) :
    rankPairsFrom board rank file =
      rankPairsFrom board rank (file + 1) ++ [(Square.mkUnsafe file rank, p)] := by
  unfold rankPairsFrom
  have hSub : 8 - file = Nat.succ (8 - (file + 1)) := by
    have : 8 - file > 0 := Nat.sub_pos_of_lt hFile
    exact (Nat.succ_pred_eq_of_pos this).symm
  rw [hSub]
  simpa using rankPairsFromCount_succ_some (board := board) (rank := rank) (file := file)
    (n := 8 - (file + 1)) (p := p) hGet

private theorem parsePlacementRankChars_rankToFenCharsAux_ok
    (board : Board) (rank file emptyCount start : Nat) (acc : List (Square × Piece))
    (hLe : file ≤ 8)
    (hStart : start + emptyCount = file) :
    parsePlacementRankChars rank start (rankToFenCharsAux board rank file emptyCount) acc =
      .ok (rankPairsFrom board rank file ++ acc) := by
  -- Induct on the remaining files (`8 - file`).
  induction hK : (8 - file) generalizing file emptyCount start acc with
  | zero =>
      have hge : 8 ≤ file := Nat.le_of_sub_eq_zero hK
      have hEq : file = 8 := Nat.le_antisymm hLe hge
      subst hEq
      have hChars :
          rankToFenCharsAux board rank 8 emptyCount =
            (if emptyCount = 0 then [] else [digitChar emptyCount]) :=
        rankToFenCharsAux_done (board := board) (rank := rank) (file := 8) (emptyCount := emptyCount) (by decide)
      -- `rankPairsFrom` is empty at file 8.
      by_cases h0 : emptyCount = 0
      · subst h0
        have hStartEq : start = 8 := by
          simpa using hStart
        simp [hChars, rankPairsFrom, rankPairsFromCount, parsePlacementRankChars, hStartEq]
        rfl
      · have hLe8 : emptyCount ≤ 8 := by
          have : emptyCount ≤ start + emptyCount := Nat.le_add_left _ _
          simpa [hStart] using this
        have hDigit :
            parsePlacementRankChars rank start [digitChar emptyCount] acc =
              parsePlacementRankChars rank (start + emptyCount) [] acc := by
          simpa using
            (parsePlacementRankChars_digitChar (rank := rank) (file := start) (n := emptyCount)
              (cs := []) (acc := acc) hLe8 h0)
        -- Now `start + emptyCount = 8`, so the parser returns `acc`.
        have hStartEq : start + emptyCount = 8 := by
          simpa using hStart
        -- Reduce to parsing a single digit, then finish by `hDigit`.
        have :
            parsePlacementRankChars rank start (if emptyCount = 0 then [] else [digitChar emptyCount]) acc =
              .ok acc := by
          -- `emptyCount ≠ 0`, so the printer emits exactly one digit.
          simpa [h0, parsePlacementRankChars, hStartEq] using congrArg id hDigit
        simpa [hChars, h0, rankPairsFrom, rankPairsFromCount] using this
  | succ k ih =>
      have hlt : file < 8 := Nat.lt_of_sub_eq_succ hK
      have hLe' : file + 1 ≤ 8 := Nat.succ_le_of_lt hlt
      have hK' : 8 - (file + 1) = k := by
        calc
          8 - (file + 1) = (8 - file).pred := by
            simpa using (Nat.sub_succ 8 file)
          _ = (Nat.succ k).pred := by simp [hK]
          _ = k := by simp
      cases hGet : board.get (Square.mkUnsafe file rank) with
      | none =>
          have hStep :=
            rankToFenCharsAux_step_none (board := board) (rank := rank) (file := file) (emptyCount := emptyCount)
              hlt hGet
          have hStart' : start + (emptyCount + 1) = file + 1 := by
            calc
              start + (emptyCount + 1) = (start + emptyCount) + 1 := by
                simp [Nat.add_assoc]
              _ = file + 1 := by
                simp [hStart]
          have hPairs : rankPairsFrom board rank file = rankPairsFrom board rank (file + 1) :=
            rankPairsFrom_succ_none board rank file hlt hGet
          simpa [hStep, hPairs] using
            (ih (file := file + 1) (emptyCount := emptyCount + 1) (start := start) (acc := acc) hLe' hStart' hK')
      | some p =>
          have hStep :=
            rankToFenCharsAux_step_some (board := board) (rank := rank) (file := file) (emptyCount := emptyCount) (p := p)
              hlt hGet
          have hPairs :
              rankPairsFrom board rank file =
                rankPairsFrom board rank (file + 1) ++ [(Square.mkUnsafe file rank, p)] :=
            rankPairsFrom_succ_some board rank file p hlt hGet
          by_cases h0 : emptyCount = 0
          · subst h0
            have hStartEq : start = file := by simpa [Nat.add_zero] using hStart
            have hPiece :=
              parsePlacementRankChars_pieceToChar (rank := rank) (file := file) (p := p)
                (cs := rankToFenCharsAux board rank (file + 1) 0) (acc := acc) hlt
            have hTail :=
              ih (file := file + 1) (emptyCount := 0) (start := file + 1)
                (acc := (Square.mkUnsafe file rank, p) :: acc) hLe' (by simp) hK'
            -- Rewrite the result list into the `++ acc` shape.
            have hAssoc :
                rankPairsFrom board rank (file + 1) ++ (Square.mkUnsafe file rank, p) :: acc =
                  (rankPairsFrom board rank (file + 1) ++ [(Square.mkUnsafe file rank, p)]) ++ acc := by
              simp [List.append_assoc]
            have hStep0 :
                rankToFenCharsAux board rank file 0 =
                  pieceToChar p :: rankToFenCharsAux board rank (file + 1) 0 := by
              simpa using hStep
            calc
              parsePlacementRankChars rank start (rankToFenCharsAux board rank file 0) acc
                  = parsePlacementRankChars rank file (rankToFenCharsAux board rank file 0) acc := by
                      simp [hStartEq]
              _ = parsePlacementRankChars rank file (pieceToChar p :: rankToFenCharsAux board rank (file + 1) 0) acc := by
                      simp [hStep0]
              _ = parsePlacementRankChars rank (file + 1) (rankToFenCharsAux board rank (file + 1) 0)
                    ((Square.mkUnsafe file rank, p) :: acc) := by
                      simpa using hPiece
              _ = .ok (rankPairsFrom board rank (file + 1) ++ (Square.mkUnsafe file rank, p) :: acc) := by
                      simpa using hTail
              _ = .ok ((rankPairsFrom board rank (file + 1) ++ [(Square.mkUnsafe file rank, p)]) ++ acc) := by
                      rw [hAssoc]
              _ = .ok (rankPairsFrom board rank file ++ acc) := by
                      rw [hPairs]
          · have hLe8 : emptyCount ≤ 8 := by
              have : emptyCount ≤ file := by
                have : emptyCount ≤ start + emptyCount := Nat.le_add_left _ _
                simpa [hStart] using this
              exact Nat.le_trans this hLe
            have hDigit :=
              parsePlacementRankChars_digitChar (rank := rank) (file := start) (n := emptyCount)
                (cs := pieceToChar p :: rankToFenCharsAux board rank (file + 1) 0) (acc := acc) hLe8 h0
            have hPiece :=
              parsePlacementRankChars_pieceToChar (rank := rank) (file := file) (p := p)
                (cs := rankToFenCharsAux board rank (file + 1) 0) (acc := acc) hlt
            have hTail :=
              ih (file := file + 1) (emptyCount := 0) (start := file + 1)
                (acc := (Square.mkUnsafe file rank, p) :: acc) hLe' (by simp) hK'
            have hAssoc :
                rankPairsFrom board rank (file + 1) ++ (Square.mkUnsafe file rank, p) :: acc =
                  (rankPairsFrom board rank (file + 1) ++ [(Square.mkUnsafe file rank, p)]) ++ acc := by
              simp [List.append_assoc]
            -- Unfold the printer one step and consume digit+piece.
            -- `start + emptyCount = file`, so digit consumption reaches `file`.
            have hStartFile : start + emptyCount = file := hStart
            -- Assemble.
            -- Rewrite `rankToFenCharsAux` using the printer step, then apply digit/piece steps, then the IH tail.
            -- Finally rewrite the expected pair list using `hPairs`.
            -- The `simp` below uses the previously established equalities as rewrite rules.
            calc
              parsePlacementRankChars rank start (rankToFenCharsAux board rank file emptyCount) acc
                  = parsePlacementRankChars rank start
                      (digitChar emptyCount :: pieceToChar p :: rankToFenCharsAux board rank (file + 1) 0) acc := by
                        simp [hStep, h0, List.append_assoc]
              _ = parsePlacementRankChars rank (start + emptyCount)
                    (pieceToChar p :: rankToFenCharsAux board rank (file + 1) 0) acc := by
                      simpa using hDigit
              _ = parsePlacementRankChars rank file
                    (pieceToChar p :: rankToFenCharsAux board rank (file + 1) 0) acc := by
                      simp [hStartFile]
              _ = parsePlacementRankChars rank (file + 1)
                    (rankToFenCharsAux board rank (file + 1) 0) ((Square.mkUnsafe file rank, p) :: acc) := by
                      simpa using hPiece
              _ = .ok (rankPairsFrom board rank (file + 1) ++ (Square.mkUnsafe file rank, p) :: acc) := by
                      simpa using hTail
              _ = .ok ((rankPairsFrom board rank (file + 1) ++ [(Square.mkUnsafe file rank, p)]) ++ acc) := by
                      rw [hAssoc]
              _ = .ok (rankPairsFrom board rank file ++ acc) := by
                      rw [hPairs]

private theorem parsePlacementRankChars_rankToFenChars_ok (board : Board) (rank : Nat) :
    parsePlacementRankChars rank 0 (rankToFenChars board rank) [] =
      .ok (rankPairsFrom board rank 0) := by
  unfold rankToFenChars
  simpa using
    (parsePlacementRankChars_rankToFenCharsAux_ok (board := board) (rank := rank) (file := 0) (emptyCount := 0)
      (start := 0) (acc := []) (by decide) (by simp))

private def placementPairsAux (board : Board) : List Nat → List (Square × Piece)
  | [] => []
  | r :: rs => rankPairsFrom board r 0 ++ placementPairsAux board rs

private def placementPairs (board : Board) : List (Square × Piece) :=
  placementPairsAux board (List.range 8).reverse

private theorem foldl_append_eq_placementPairsAux
    (board : Board) (ranks : List Nat) (acc0 : List (Square × Piece)) :
    ranks.foldl (fun acc r => acc ++ rankPairsFrom board r 0) acc0 =
      acc0 ++ placementPairsAux board ranks := by
  induction ranks generalizing acc0 with
  | nil =>
      simp [placementPairsAux]
  | cons r rs ih =>
      simp [List.foldl, placementPairsAux, ih, List.append_assoc]

private theorem zip_ranks_map (ranks : List Nat) (f : Nat → List Char) :
    List.zip ranks (ranks.map f) = ranks.map (fun r => (r, f r)) := by
  induction ranks with
  | nil =>
      simp
  | cons r rs ih =>
      simp [ih]

private theorem foldlM_parseRanks
    (board : Board) (ranks : List Nat) (acc0 : List (Square × Piece)) :
    (ranks.map (fun r => (r, rankToFenChars board r))).foldlM
        (fun acc entry =>
          (HAppend.hAppend acc) <$> parsePlacementRankChars entry.fst 0 entry.snd [])
        acc0 =
      .ok (ranks.foldl (fun acc r => acc ++ rankPairsFrom board r 0) acc0) := by
  induction ranks generalizing acc0 with
  | nil =>
      simp [List.foldlM]
      rfl
  | cons r rs ih =>
      have hRank : parsePlacementRankChars r 0 (rankToFenChars board r) [] = .ok (rankPairsFrom board r 0) :=
        parsePlacementRankChars_rankToFenChars_ok board r
      -- Unfold one `foldlM` step and use `hRank` for the head rank.
      simp [List.foldlM, hRank]
      -- Apply the induction hypothesis to the updated accumulator.
      simpa [List.foldl] using ih (acc0 := acc0 ++ rankPairsFrom board r 0)

private theorem mem_rankPairsFromCount_implies_get
    (board : Board) (rank file n : Nat) {sq : Square} {p : Piece} :
    (sq, p) ∈ rankPairsFromCount board rank file n → board.get sq = some p := by
  induction n generalizing file with
  | zero =>
      intro hMem
      cases hMem
  | succ n ih =>
      intro hMem
      cases hBase : board.get (Square.mkUnsafe file rank) with
      | none =>
          -- The head file contributes nothing.
          simpa [rankPairsFromCount, hBase] using ih (file := file + 1) (by simpa [rankPairsFromCount, hBase] using hMem)
      | some q =>
          -- Either membership comes from the rest, or from the appended singleton.
          have hMem' :
              (sq, p) ∈
                rankPairsFromCount board rank (file + 1) n ++ [(Square.mkUnsafe file rank, q)] := by
            simpa [rankPairsFromCount, hBase] using hMem
          rcases (List.mem_append.1 hMem') with hRest | hLast
          · exact ih (file := file + 1) hRest
          · have hEq : (sq, p) = (Square.mkUnsafe file rank, q) := by
              simpa using hLast
            cases hEq
            simp [hBase]

private theorem mem_rankPairsFrom_implies_get
    (board : Board) (rank file : Nat) {sq : Square} {p : Piece} :
    (sq, p) ∈ rankPairsFrom board rank file → board.get sq = some p := by
  intro hMem
  unfold rankPairsFrom at hMem
  exact mem_rankPairsFromCount_implies_get (board := board) (rank := rank) (file := file) (n := 8 - file) hMem

private theorem mem_rankPairsFromCount_of_get_some_offset
    (board : Board) (rank base : Nat) :
    ∀ (n off : Nat) (p : Piece),
      off < n →
        board.get (Square.mkUnsafe (base + off) rank) = some p →
          (Square.mkUnsafe (base + off) rank, p) ∈ rankPairsFromCount board rank base n := by
  intro n
  induction n generalizing base with
  | zero =>
      intro off p hoff
      cases (Nat.not_lt_zero _ hoff)
  | succ n ih =>
      intro off p hoff hGet
      cases off with
      | zero =>
          -- The target is the current base square.
          cases hBase : board.get (Square.mkUnsafe base rank) with
          | none =>
              have : False := by
                -- `base + 0 = base`.
                simpa [Nat.add_zero, hBase] using hGet
              cases this
          | some q =>
              have hGet0 : board.get (Square.mkUnsafe base rank) = some p := by
                simpa [Nat.add_zero] using hGet
              have hEq : q = p := by
                have : some q = some p := by simpa [hBase] using hGet0
                exact Option.some.inj this
              subst hEq
              -- Membership comes from the appended singleton.
              simp [rankPairsFromCount, hBase]
      | succ off' =>
          have hoff' : off' < n := Nat.lt_of_succ_lt_succ hoff
          -- The target lies in the recursive `rest`.
          have hGet' : board.get (Square.mkUnsafe ((base + 1) + off') rank) = some p := by
            simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hGet
          have hRec :
              (Square.mkUnsafe ((base + 1) + off') rank, p) ∈
                rankPairsFromCount board rank (base + 1) n :=
            ih (base := base + 1) off' p hoff' hGet'
          have hRec' :
              (Square.mkUnsafe (base + (off' + 1)) rank, p) ∈
                rankPairsFromCount board rank (base + 1) n := by
            simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hRec
          cases hBase : board.get (Square.mkUnsafe base rank) with
          | none =>
              simpa [rankPairsFromCount, hBase] using hRec'
          | some q =>
              -- `rest` is a prefix of `rest ++ [..]`.
              have : (Square.mkUnsafe (base + (off' + 1)) rank, p) ∈
                    rankPairsFromCount board rank (base + 1) n ++ [(Square.mkUnsafe base rank, q)] :=
                List.mem_append_left _ hRec'
              simpa [rankPairsFromCount, hBase] using this

private theorem mem_rankPairsFrom_of_get_some
    (board : Board) (rank file : Nat) (p : Piece)
    (hFile : file < 8)
    (hGet : board.get (Square.mkUnsafe file rank) = some p) :
    (Square.mkUnsafe file rank, p) ∈ rankPairsFrom board rank 0 := by
  unfold rankPairsFrom
  -- Enumerate all 8 files starting at 0.
  have hMem :=
    mem_rankPairsFromCount_of_get_some_offset (board := board) (rank := rank) (base := 0) (n := 8)
      (off := file) (p := p) hFile (by simpa using hGet)
  simpa using hMem

private theorem mem_placementPairsAux_of_mem_rank (board : Board) :
    ∀ (ranks : List Nat) (rank : Nat) {sq : Square} {p : Piece},
      rank ∈ ranks →
        (sq, p) ∈ rankPairsFrom board rank 0 →
          (sq, p) ∈ placementPairsAux board ranks := by
  intro ranks
  induction ranks with
  | nil =>
      intro rank sq p hRank
      cases hRank
  | cons r rs ih =>
      intro rank sq p hRank hMem
      have hRank' : rank = r ∨ rank ∈ rs := by
        simpa [List.mem_cons] using hRank
      cases hRank' with
      | inl hEq =>
          have hMem' : (sq, p) ∈ rankPairsFrom board r 0 := by
            simpa [hEq] using hMem
          have : (sq, p) ∈ rankPairsFrom board r 0 ++ placementPairsAux board rs :=
            List.mem_append_left _ hMem'
          simpa [placementPairsAux] using this
      | inr hIn =>
          have hRec : (sq, p) ∈ placementPairsAux board rs :=
            ih rank (sq := sq) (p := p) hIn hMem
          have : (sq, p) ∈ rankPairsFrom board r 0 ++ placementPairsAux board rs :=
            List.mem_append_right _ hRec
          simpa [placementPairsAux] using this

private theorem mem_placementPairsAux_implies_get (board : Board) :
    ∀ (ranks : List Nat) {sq : Square} {p : Piece},
      (sq, p) ∈ placementPairsAux board ranks → board.get sq = some p := by
  intro ranks
  induction ranks with
  | nil =>
      intro sq p hMem
      cases hMem
  | cons r rs ih =>
      intro sq p hMem
      have hMem' : (sq, p) ∈ rankPairsFrom board r 0 ++ placementPairsAux board rs := by
        simpa [placementPairsAux] using hMem
      rcases (List.mem_append.1 hMem') with hHere | hThere
      · exact mem_rankPairsFrom_implies_get (board := board) (rank := r) (file := 0) hHere
      · exact ih (sq := sq) (p := p) hThere

private theorem mem_placementPairs_of_mem_rank
    (board : Board) (rank : Nat) {sq : Square} {p : Piece}
    (hRank : rank ∈ (List.range 8).reverse)
    (hMem : (sq, p) ∈ rankPairsFrom board rank 0) :
    (sq, p) ∈ placementPairs board := by
  unfold placementPairs
  exact mem_placementPairsAux_of_mem_rank board (List.range 8).reverse rank hRank hMem

private theorem mem_placementPairs_implies_get
    (board : Board) {sq : Square} {p : Piece} :
    (sq, p) ∈ placementPairs board → board.get sq = some p := by
  intro hMem
  unfold placementPairs at hMem
  exact mem_placementPairsAux_implies_get board (List.range 8).reverse hMem

theorem parsePlacement_boardToFenPlacement (board : Board) :
    parsePlacement (boardToFenPlacement board) = .ok (placementPairs board) := by
  unfold parsePlacement
  have hRows :
      splitPlacementChars (boardToFenPlacement board).toList =
        (List.range 8).reverse.map (fun r => rankToFenChars board r) :=
    splitPlacementChars_boardToFenPlacement board
  -- Rewrite `rows` and reduce the length check.
  simp [hRows, placementPairs, placementPairsAux]
  -- Replace the `zip` with a `map`.
  have hZip :
      List.zip (List.range 8).reverse ((List.range 8).reverse.map (fun r => rankToFenChars board r)) =
        (List.range 8).reverse.map (fun r => (r, rankToFenChars board r)) := by
    simpa using zip_ranks_map (ranks := (List.range 8).reverse) (f := fun r => rankToFenChars board r)
  -- Normalize `(map f l).reverse` into `map f l.reverse` so it matches `hZip`.
  have hReverseMap :
      (List.map (fun r => rankToFenChars board r) (List.range 8)).reverse =
        List.map (fun r => rankToFenChars board r) (List.range 8).reverse := by
    simp
  -- Rewrite the `zip` argument, then apply `hZip`.
  rw [hReverseMap]
  rw [hZip]
  -- Evaluate the fold using rank-level correctness.
  rw [foldlM_parseRanks (board := board) (ranks := (List.range 8).reverse) (acc0 := [])]
  -- Turn the pure fold into the explicit concatenation.
  have hFold :=
    foldl_append_eq_placementPairsAux (board := board) (ranks := (List.range 8).reverse) (acc0 := [])
  -- `[] ++ xs = xs`.
  simp [hFold, placementPairs, placementPairsAux]

theorem parsePlacement_boardToFenPlacement_roundtrip (board : Board) :
    Except.map Board.fromList (parsePlacement (boardToFenPlacement board)) = .ok board := by
  -- Parse and then rebuild.
  have hParse := parsePlacement_boardToFenPlacement board
  simp [Except.map, hParse, placementPairs]
  -- `Board.fromList` of the printer-derived pairs reconstructs the original board.
  apply Board.ext_get
  intro sq
  classical
  -- Split by occupancy of `sq`.
  cases hGet : board.get sq with
  | none =>
      -- Show no entry updates `sq`.
      apply Board.fromList_get_eq_none_of_forall_ne
      intro e he
      rcases e with ⟨s, p⟩
      intro hEq
      have hOccS : board.get s = some p :=
        mem_placementPairs_implies_get (board := board) (sq := s) (p := p) he
      have hOcc : board.get sq = some p := by
        simpa [hEq.symm] using hOccS
      have : False := by
        simpa [hGet] using hOcc
      cases this
  | some p =>
      -- Show membership and uniqueness.
      have hRankMem : sq.rankNat ∈ (List.range 8).reverse := by
        -- `sq.rankNat < 8` by finiteness.
        have : sq.rankNat < 8 := sq.rank.isLt
        have hInRange : sq.rankNat ∈ List.range 8 := (List.mem_range).2 this
        exact (List.mem_reverse).2 hInRange
      have hMemRank : (Square.mkUnsafe sq.fileNat sq.rankNat, p) ∈ rankPairsFrom board sq.rankNat 0 := by
        have hf : sq.fileNat < 8 := sq.file.isLt
        -- Rewrite `Square.mkUnsafe sq.fileNat sq.rankNat` to `sq`.
        have hGet' : board.get (Square.mkUnsafe sq.fileNat sq.rankNat) = some p := by
          simpa [Square.mkUnsafe_eq sq] using hGet
        exact mem_rankPairsFrom_of_get_some (board := board) (rank := sq.rankNat) (file := sq.fileNat) (p := p) hf hGet'
      have hMemPairs : (sq, p) ∈ placementPairs board := by
        have hMem' : (Square.mkUnsafe sq.fileNat sq.rankNat, p) ∈ placementPairs board :=
          mem_placementPairs_of_mem_rank (board := board) (rank := sq.rankNat) (sq := Square.mkUnsafe sq.fileNat sq.rankNat)
            (p := p) hRankMem hMemRank
        simpa [Square.mkUnsafe_eq sq] using hMem'
      refine Board.fromList_get_eq_some_of_mem_unique (ps := placementPairs board) (sq := sq) (p := p) ?_ ?_
      · exact hMemPairs
      · intro q hq
        have hOcc : board.get sq = some q :=
          mem_placementPairs_implies_get (board := board) (sq := sq) (p := q) hq
        have : some q = some p := by simpa [hGet] using hOcc.symm
        exact Option.some.inj this

end Parsing
end Chess
