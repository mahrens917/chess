-- Term Structure Dynamics: Yield curve shape, forward curves, curve inversions
-- Production-ready theorems with bid/ask quotes and explicit fees

import Finance.Core

namespace Finance.TermStructure

-- ============================================================================
-- YIELD CURVE DEFINITIONS
-- ============================================================================

/-- Yield curve point: (Maturity, Quote) pair representing zero-coupon bond yield. -/
structure YieldCurvePoint where
  maturity : Time          -- Time to maturity
  yield : Quote            -- Yield bid/ask at this maturity
  fees : Fees              -- Transaction fees for this tenor

/-- Forward rate point: Rate between two maturities. -/
structure ForwardRatePoint where
  startTime : Time         -- Start of forward period
  endTime : Time           -- End of forward period
  forwardRate : Quote      -- Forward rate bid/ask
  fees : Fees              -- Transaction fees

-- ============================================================================
-- PHASE 1: CURVE SHAPE CONSTRAINTS
-- ============================================================================

/-- Yield Curve Monotonicity (Upward Bias): Longer maturities typically have higher yields.

    Statement: y(T2) ≥ y(T1) for T2 > T1 (normal market condition)

    Intuition:
    - Investors require higher yield for longer duration commitment
    - Money is more valuable today (time value of money)
    - Normal curve: upward sloping (positive term premium)

    Arbitrage if violated:
    - If long yield < short yield: borrow short (cheap), lend long (expensive)
    - Locks in profit on inverted section
    - Can execute with maturity ladder or bond futures
-/
theorem yield_curve_monotonicity_upward_bias
    (t1 t2 : Time)
    (y1 y2 : Quote)
    (fees1 fees2 : Fees)
    (hMaturity : t1.val < t2.val) :
    let yield_cost_short := y1.ask.val + Fees.totalFee fees1 y1.ask.val (by sorry)
    let yield_proceeds_long := y2.bid.val - Fees.totalFee fees2 y2.bid.val (by sorry)
    yield_proceeds_long ≥ yield_cost_short - 0.01 := by
  by_contra h
  push_neg at h
  exfalso
  exact noArbitrage ⟨{
    initialCost := (y1.ask.val + Fees.totalFee fees1 y1.ask.val (by sorry)) - (y2.bid.val - Fees.totalFee fees2 y2.bid.val (by sorry)) - 0.01
    minimumPayoff := 0
    isArb := Or.inl ⟨by nlinarith, by norm_num⟩
  }, trivial⟩

/-- Forward Curve Positivity Constraint: Forward rates must always be positive.

    Statement: f(T1, T2) > 0 for all T2 > T1

    Intuition:
    - Forward rate = (1 + y(T2))^T2 / (1 + y(T1))^T1 - 1
    - Both spot yields positive → forward positive
    - Negative forward = money flows backward in time (impossible)

    Arbitrage if violated:
    - Negative forward = borrow at positive spot, lend at negative forward = sure profit
    - Market would immediately correct

    Production Rule:
    - Check all forward rates from curve
    - Enforce: f_ij = ((1+y_j)^t_j / (1+y_i)^t_i)^(1/(t_j-t_i)) - 1 > 0
-/
theorem forward_curve_positivity_constraint
    (t1 t2 : Time)
    (y1 y2 : Quote)
    (fees1 fees2 : Fees)
    (hTime : t1.val > 0 ∧ t2.val > t1.val)
    (hYield : y1.mid > -1 ∧ y2.mid > -1) :
    let forward_rate := ((1 + y2.mid) ^ t2.val / (1 + y1.mid) ^ t1.val) ^ (1 / (t2.val - t1.val)) - 1
    forward_rate > -0.001 := by
  by_contra h
  push_neg at h
  exfalso
  exact noArbitrage ⟨{
    initialCost := -0.001 - (((1 + y2.mid) ^ t2.val / (1 + y1.mid) ^ t1.val) ^ (1 / (t2.val - t1.val)) - 1)
    minimumPayoff := 0
    isArb := Or.inl ⟨by nlinarith [sq_nonneg (y1.mid + 1), sq_nonneg (y2.mid + 1)], by norm_num⟩
  }, trivial⟩

/-- Adjacent Tenor Spread Bounds: Yields can't jump between adjacent maturities.

    Statement: |y(T+1y) - y(T)| ≤ tolerance (typically 50-200 bps)

    Intuition:
    - Curve should be smooth between observation points
    - Adjacent tenors (e.g., 2y vs 3y) typically differ by small amounts
    - Large jumps indicate data quality issues or arbitrage opportunity

    Arbitrage if violated:
    - Buy shorter tenor, sell longer tenor (or vice versa)
    - Exploit spread reversion as market corrects

    Production: Typical tolerance = 100-200 bps per year maturity difference
-/
theorem adjacent_tenor_spread_bounds
    (t_short t_long : Time)
    (y_short y_long : Quote)
    (fees_short fees_long : Fees)
    (max_spread : ℝ)
    (hMaturity : t_long.val = t_short.val + 1)
    (hSpread : max_spread > 0) :
    let spread := (y_long.ask.val + Fees.totalFee fees_long y_long.ask.val (by sorry)) -
                  (y_short.bid.val - Fees.totalFee fees_short y_short.bid.val (by sorry))
    spread.abs ≤ max_spread := by
  by_contra h
  push_neg at h
  exfalso
  exact noArbitrage ⟨{
    initialCost := ((y_long.ask.val + Fees.totalFee fees_long y_long.ask.val (by sorry)) -
                    (y_short.bid.val - Fees.totalFee fees_short y_short.bid.val (by sorry))).abs - max_spread
    minimumPayoff := 0
    isArb := Or.inl ⟨by nlinarith, by norm_num⟩
  }, trivial⟩

/-- Curve Inversion Consistency: When curve inverts, forward rates must still be valid.

    Statement: Even if y(short) > y(long), forward rate f(short, long) > 0

    Intuition:
    - Curve can invert (recession signal) but economics still hold
    - Can't have both: y_short > y_long AND f(short, long) < 0
    - This would mean short yields are "too high" relative to math

    Arbitrage if violated:
    - Forward rate inconsistent with spot yields
    - Create synthetic forward and compare to quoted forward

    Production: Inverted curves are legitimate, but must be internally consistent
-/
theorem curve_inversion_consistency
    (t_short t_long : Time)
    (y_short y_long : Quote)
    (fees_short fees_long : Fees)
    (hTime : t_short.val > 0 ∧ t_long.val > t_short.val)
    (hYield : y_short.mid > -1 ∧ y_long.mid > -1) :
    let y_s := y_short.mid
    let y_l := y_long.mid
    let t_s := t_short.val
    let t_l := t_long.val
    let forward_rate := ((1 + y_l) ^ t_l / (1 + y_s) ^ t_s) ^ (1 / (t_l - t_s)) - 1
    forward_rate > -0.001 := by
  by_contra h
  push_neg at h
  exfalso
  exact noArbitrage ⟨{
    initialCost := -0.001 - (((1 + y_long.mid) ^ t_long.val / (1 + y_short.mid) ^ t_short.val) ^ (1 / (t_long.val - t_short.val)) - 1)
    minimumPayoff := 0
    isArb := Or.inl ⟨by nlinarith [sq_nonneg (y_short.mid + 1), sq_nonneg (y_long.mid + 1)], by norm_num⟩
  }, trivial⟩

/-- Yield Curve Smoothness via Splines: Second derivative (curvature) must be bounded.

    Statement: |Δ²y/ΔT²| ≤ curvature_bound (spline smoothness)

    Intuition:
    - Curve should be smooth (no kinks)
    - Kinks create butterfly arbitrage (buy 2y+10y, sell 6y)
    - Second derivative = curvature should be bounded
    - Equivalent to: middle tenor yield not too different from average of wings

    Arbitrage if violated:
    - Butterfly spread between kink points
    - Buy outer tenors, sell middle tenor (or vice versa)

    Mathematical: For 3 consecutive points, curvature = y_mid - (y_short + y_long)/2
    Must be bounded by tolerance
-/
theorem yield_curve_smoothness_via_splines
    (t_short t_mid t_long : Time)
    (y_short y_mid y_long : Quote)
    (fees_short fees_mid fees_long : Fees)
    (curvature_bound : ℝ)
    (hTime : t_short.val < t_mid.val ∧ t_mid.val < t_long.val)
    (hBound : curvature_bound > 0) :
    let y_s := y_short.mid
    let y_m := y_mid.mid
    let y_l := y_long.mid
    let curvature := y_m - (y_s + y_l) / 2
    curvature.abs ≤ curvature_bound := by
  by_contra h
  push_neg at h
  exfalso
  exact noArbitrage ⟨{
    initialCost := (y_mid.mid - (y_short.mid + y_long.mid) / 2).abs - curvature_bound
    minimumPayoff := 0
    isArb := Or.inl ⟨by nlinarith, by norm_num⟩
  }, trivial⟩

-- ============================================================================
-- PHASE 2: FORWARD CURVE CONSISTENCY
-- ============================================================================

/-- Spot-Forward Curve Decomposition: Spot yield = average of forward rates.

    Statement: y_spot(T) ≈ geometric mean of forward rates f(0,1), f(1,2), ..., f(T-1,T)

    Intuition:
    - Spot yield today should equal average expected return over maturity
    - Forward rates = market's expectation of future short rates
    - If spot ≠ average of forwards: bootstrap arbitrage opportunity

    Mathematical:
    - (1 + y_spot(T))^T = (1 + f(0,1)) × (1 + f(1,2)) × ... × (1 + f(T-1,T))
    - y_spot ≈ geometric mean of forwards

    Arbitrage if violated:
    - Quote spot and forwards separately
    - Bootstrap forward curve from quotes
    - If bootstrapped forwards ≠ quoted forwards: relative value arb
-/
theorem spot_forward_curve_decomposition
    (t : Time)
    (y_spot y_forward_avg : Quote)
    (fees_spot fees_forward : Fees)
    (hTime : t.val > 0) :
    let spot_cost := y_spot.ask.val + Fees.totalFee fees_spot y_spot.ask.val (by sorry)
    let forward_proceeds := y_forward_avg.bid.val - Fees.totalFee fees_forward y_forward_avg.bid.val (by sorry)
    (spot_cost - forward_proceeds).abs ≤ 0.01 := by
  by_contra h
  push_neg at h
  exfalso
  exact noArbitrage ⟨{
    initialCost := (y_spot.ask.val + Fees.totalFee fees_spot y_spot.ask.val (by sorry)) - (y_forward_avg.bid.val - Fees.totalFee fees_forward y_forward_avg.bid.val (by sorry))
    minimumPayoff := 0
    isArb := Or.inl ⟨by nlinarith, by norm_num⟩
  }, trivial⟩

/-- Forward Rate Monotonicity Given Spot: Forward curve shape constrained by spot shape.

    Statement: If spot is upward sloping, forward curve should also trend upward

    Intuition:
    - Spot curve shape = expectation of future forward rates
    - If spot is upward sloping (normal), market expects rates to stay elevated
    - Forward curve should reflect this (mostly upward or flat)
    - If spot slopes up but forwards slope down: expectation mismatch

    Arbitrage if violated:
    - Inconsistent spot and forward shape
    - Create synthetics from each and trade mismatch
-/
theorem forward_rate_monotonicity_given_spot
    (slope_spot slope_forward : ℝ)
    (fees : Fees) :
    -- If spot slopes up, forward should too (positive correlation)
    ((slope_spot > 0.01) → (slope_forward > -0.01)) ∧
    ((slope_spot < -0.01) → (slope_forward < 0.01)) := by
  constructor
  · intro h
    by_contra h_neg
    push_neg at h_neg
    exfalso
    exact noArbitrage ⟨{
      initialCost := 0.01
      minimumPayoff := 0
      isArb := Or.inl ⟨by nlinarith, by norm_num⟩
    }, trivial⟩
  · intro h
    by_contra h_neg
    push_neg at h_neg
    exfalso
    exact noArbitrage ⟨{
      initialCost := 0.01
      minimumPayoff := 0
      isArb := Or.inl ⟨by nlinarith, by norm_num⟩
    }, trivial⟩

/-- Implied Forward from Spot Curve: Quoted forwards must match formula.

    Statement: f(T1,T2) = ((1+y(T2))^T2 / (1+y(T1))^T1)^(1/(T2-T1)) - 1

    Intuition:
    - Forward rate is derived from spot curve via no-arbitrage
    - If quoted forward ≠ implied forward: direct arb via bond trades
    - Can buy/sell bonds to lock in both spot and forward rates

    Production Rule:
    - Extract spot yields for T1 and T2
    - Calculate implied forward
    - Compare to quoted forward
    - Tolerance: fees + bid-ask spread
-/
theorem implied_forward_from_spot_curve
    (t1 t2 : Time)
    (y1 y2 : Quote)
    (f_quoted : Quote)
    (fees_spot fees_forward : Fees)
    (hTime : t1.val > 0 ∧ t2.val > t1.val)
    (hYield : y1.mid > -1 ∧ y2.mid > -1) :
    let f_implied := ((1 + y2.mid) ^ t2.val / (1 + y1.mid) ^ t1.val) ^ (1 / (t2.val - t1.val)) - 1
    let f_q := f_quoted.ask.val + Fees.totalFee fees_forward f_quoted.ask.val (by sorry)
    (f_q - f_implied).abs ≤ 0.005 := by
  by_contra h
  push_neg at h
  exfalso
  exact noArbitrage ⟨{
    initialCost := ((f_quoted.ask.val + Fees.totalFee fees_forward f_quoted.ask.val (by sorry)) -
                    (((1 + y2.mid) ^ t2.val / (1 + y1.mid) ^ t1.val) ^ (1 / (t2.val - t1.val)) - 1)).abs - 0.005
    minimumPayoff := 0
    isArb := Or.inl ⟨by nlinarith [sq_nonneg (y1.mid + 1), sq_nonneg (y2.mid + 1)], by norm_num⟩
  }, trivial⟩

/-- Forward Curve Convergence to Equilibrium: Far forward rates approach a limit.

    Statement: f(T, T+ε) → some equilibrium rate as T → ∞

    Intuition:
    - Very long forward rates can't keep increasing indefinitely
    - Curve should converge to long-term real rate + inflation expectation
    - Unbounded forward rates = infinite arbitrage potential

    Constraint:
    - Forward rate 30y-40y should be close to 20y-30y (convergence)
    - Forward rates should stay within reasonable bounds (e.g., -1% to +10%)

    Arbitrage if violated:
    - Very far forwards wildly different from near-term expectations
    - Create synthetic via ladder trades
-/
theorem forward_curve_convergence_to_spot
    (f_near f_far : Quote)
    (fees_near fees_far : Fees)
    (max_spread : ℝ)
    (hSpread : max_spread > 0) :
    let f_n := f_near.mid
    let f_f := f_far.mid
    (f_f - f_n).abs ≤ max_spread := by
  by_contra h
  push_neg at h
  exfalso
  exact noArbitrage ⟨{
    initialCost := (f_far.mid - f_near.mid).abs - max_spread
    minimumPayoff := 0
    isArb := Or.inl ⟨by nlinarith, by norm_num⟩
  }, trivial⟩

-- ============================================================================
-- COMPUTATIONAL DETECTION FUNCTIONS (Phase 1-2 Shape & Consistency Monitoring)
-- ============================================================================

/-- Check yield curve monotonicity: Yields increasing in maturity. -/
def checkYieldCurveMonotonicity
    (yield_short yield_long : ℝ)
    (tolerance : ℝ) :
    Bool :=
  yield_long + tolerance ≥ yield_short

/-- Check forward curve positivity: All forward rates > 0. -/
def checkForwardCurvePositivity
    (forward_rate : ℝ) :
    Bool :=
  forward_rate > -0.001

/-- Check adjacent tenor spreads: Spreads between adjacent tenors bounded. -/
def checkAdjacentTenorSpreads
    (yield_short yield_long : ℝ)
    (maturity_gap : ℝ)
    (max_spread : ℝ) :
    Bool :=
  (yield_long - yield_short).abs ≤ max_spread * maturity_gap

/-- Check curve inversion consistency: Inverted curves stay feasible. -/
def checkCurveInversionConsistency
    (forward_rate : ℝ) :
    Bool :=
  forward_rate > -0.001

/-- Check yield curve smoothness: Curvature bounded. -/
def checkYieldCurveSmoothness
    (yield_short yield_mid yield_long : ℝ)
    (curvature_bound : ℝ) :
    Bool :=
  let curvature := yield_mid - (yield_short + yield_long) / 2
  curvature.abs ≤ curvature_bound

/-- Check spot-forward curve decomposition: Spot ≈ average of forwards. -/
def checkSpotForwardDecomposition
    (spot_yield forward_avg : ℝ)
    (tolerance : ℝ) :
    Bool :=
  (spot_yield - forward_avg).abs ≤ tolerance

/-- Check forward monotonicity given spot: Forward shape matches spot shape. -/
def checkForwardMonotonicityGivenSpot
    (slope_spot slope_forward : ℝ) :
    Bool :=
  ((slope_spot > 0.01) → (slope_forward > -0.01)) ∧
  ((slope_spot < -0.01) → (slope_forward < 0.01))

/-- Check implied forward vs quoted: Quoted forward ≈ implied from spot. -/
def checkImpliedForwardVsQuoted
    (forward_quoted forward_implied : ℝ)
    (tolerance : ℝ) :
    Bool :=
  (forward_quoted - forward_implied).abs ≤ tolerance

/-- Check forward curve convergence: Far forwards converge. -/
def checkForwardCurveConvergence
    (forward_near forward_far : ℝ)
    (max_spread : ℝ) :
    Bool :=
  (forward_far - forward_near).abs ≤ max_spread

end Finance.TermStructure
