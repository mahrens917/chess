import Chess.Rules

namespace Chess
namespace Rules

theorem slidingTargets_walk_acc_subset
    (src : Square) (p : Piece) (board : Board) (color : Color) (maxStep : Nat)
    (df dr : Int) :
    ∀ (step : Nat) (acc : List Move) {m : Move},
      m ∈ acc →
      m ∈ Rules.slidingTargets.walk src p board color maxStep df dr step acc := by
  intro step
  induction step with
  | zero =>
      intro acc m hMem
      simpa [Rules.slidingTargets.walk] using hMem
  | succ s ih =>
      intro acc m hMem
      -- Expand one layer of `walk`.
      simp [Rules.slidingTargets.walk]
      cases hSq :
          Movement.squareFromInts (src.fileInt + df * Int.ofNat (maxStep - s))
            (src.rankInt + dr * Int.ofNat (maxStep - s)) with
      | none =>
          simpa [hSq] using hMem
      | some target =>
          by_cases hEmpty : isEmpty board target = true
          · -- Recurse with `({ piece := p, fromSq := src, toSq := target } :: acc)`.
            have hMem' : m ∈ ({ piece := p, fromSq := src, toSq := target } :: acc) :=
              List.mem_cons_of_mem _ hMem
            simpa [hSq, hEmpty] using ih ({ piece := p, fromSq := src, toSq := target } :: acc) hMem'
          · by_cases hEnemy : isEnemyNonKingAt board color target = true
            · -- In the enemy case we stop, returning `{captureMove} :: acc`.
              simpa [hSq, hEmpty, hEnemy] using List.mem_cons_of_mem _ hMem
            · -- Friendly piece blocks: return `acc`.
              simpa [hSq, hEmpty, hEnemy] using hMem

theorem slidingTargets_walk_mem_of_empty_square
    (src : Square) (p : Piece) (board : Board) (color : Color) (maxStep : Nat)
    (df dr : Int) (s : Nat) (acc : List Move) (target : Square)
    (hSq :
      Movement.squareFromInts (src.fileInt + df * Int.ofNat (maxStep - s))
        (src.rankInt + dr * Int.ofNat (maxStep - s)) = some target)
    (hEmpty : isEmpty board target = true) :
    ({ piece := p, fromSq := src, toSq := target } : Move) ∈
      Rules.slidingTargets.walk src p board color maxStep df dr (Nat.succ s) acc := by
  have hSq' :
      Movement.squareFromInts (src.fileInt + df * (↑(maxStep - s) : Int))
          (src.rankInt + dr * (↑(maxStep - s) : Int)) =
        some target := by
    simpa using hSq
  simp [Rules.slidingTargets.walk]
  rw [hSq']
  simp [hEmpty]
  exact
    slidingTargets_walk_acc_subset src p board color maxStep df dr s
      ({ piece := p, fromSq := src, toSq := target } :: acc) (by simp)

theorem slidingTargets_walk_mem_of_enemy_square
    (src : Square) (p : Piece) (board : Board) (color : Color) (maxStep : Nat)
    (df dr : Int) (s : Nat) (acc : List Move) (target : Square)
    (hSq :
      Movement.squareFromInts (src.fileInt + df * Int.ofNat (maxStep - s))
        (src.rankInt + dr * Int.ofNat (maxStep - s)) = some target)
    (hEmpty : isEmpty board target = false)
    (hEnemy : isEnemyNonKingAt board color target = true) :
    ({ piece := p, fromSq := src, toSq := target, isCapture := true } : Move) ∈
      Rules.slidingTargets.walk src p board color maxStep df dr (Nat.succ s) acc := by
  have hSq' :
      Movement.squareFromInts (src.fileInt + df * (↑(maxStep - s) : Int))
          (src.rankInt + dr * (↑(maxStep - s) : Int)) =
        some target := by
    simpa using hSq
  -- The enemy-square branch stops and returns the capture move as the head.
  simp [Rules.slidingTargets.walk]
  rw [hSq']
  simp [hEmpty, hEnemy]

end Rules
end Chess
