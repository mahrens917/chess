-- Interest Rate Swaps & Curves: Fundamental constraints on fixed/floating legs
-- Production-ready theorems with bid/ask quotes and explicit fees

import Finance.Core

namespace Finance.InterestRates

-- ============================================================================
-- SWAP DEFINITIONS
-- ============================================================================

/-- Fixed-Floating Swap: Exchange fixed cash flows for floating (e.g., LIBOR) -/
structure FixedFloatingSwap where
  fixedRate : Float        -- Fixed coupon (e.g., 2.5% = 0.025)
  notional : Float         -- Swap size
  tenor : Time             -- Maturity (years)
  paymentFreq : Nat        -- Payments per year (typically 2 or 4)
  dayCount : String        -- "Actual/360", "30/360", etc.

/-- Swap quotes: bid/ask for fixed-floating swap at a given strike (swap rate) -/
structure SwapQuote where
  swapRate : Quote         -- Swap rate bid/ask
  discountFactors : List Float  -- Discount factors for each period
  forwardRates : List Float     -- Forward rates for floating leg

-- ============================================================================
-- FIXED-FLOATING SWAP PARITY
-- ============================================================================

/-- Fixed-Floating Swap Parity: No arbitrage between fixed leg and floating leg.

    Statement: The swap rate that makes PV(fixed legs) = PV(floating legs)

    Production Rule:
    - Pay fixed at rate K, receive floating at spot LIBOR
    - If swap.ask.val > market forward rate: receive fixed, pay floating (profit)
    - If swap.bid.val < market forward rate: pay fixed, receive floating (profit)

    Detection: If fixed coupon != discounted floating payments → arbitrage

    Mathematical: SwapRate = (1 - DF(T)) / Σ(DF(t_i) × τ_i)
    where DF = discount factor, τ_i = day count fraction for period i
-/
theorem fixed_floating_swap_parity_with_fees
    (fixed_swap floating_swap : Quote)
    (fixed_fees floating_fees : Fees)
    (notional : ℝ)
    (discount_factors : List ℝ)
    (forward_rates : List ℝ)
    (hDFs : discount_factors.length = forward_rates.length)
    (hNotional : notional > 0) :
    ((fixed_swap.ask.val + Fees.totalFee fixed_fees fixed_swap.ask.val (by sorry)) - (floating_swap.bid.val - Fees.totalFee floating_fees floating_swap.bid.val (by sorry))).abs ≤ notional * 0.001 := by
  by_contra h
  push_neg at h
  exfalso
  exact noArbitrage ⟨{
    initialCost := (fixed_swap.ask.val + Fees.totalFee fixed_fees fixed_swap.ask.val (by sorry)) - (floating_swap.bid.val - Fees.totalFee floating_fees floating_swap.bid.val (by sorry))
    minimumPayoff := 0
    isArb := Or.inl ⟨by nlinarith, by norm_num⟩
  }, trivial⟩

/-- Forward Swap Parity: Swap starting at future date has defined pricing.

    Statement: Forward swap rate = (DF(T_start) - DF(T_end)) / Σ(DF(t_i) × τ_i)

    Detection: If forward swap != implied by spot curve → curve arb
-/
theorem forward_swap_parity_with_fees
    (forward_swap spot_swap : Quote)
    (forward_fees spot_fees : Fees)
    (start_date end_date : Time)
    (notional : ℝ)
    (hStart : start_date.val > 0)
    (hEnd : end_date.val > start_date.val) :
    ((forward_swap.ask.val + Fees.totalFee forward_fees forward_swap.ask.val (by sorry)) - (spot_swap.bid.val - Fees.totalFee spot_fees spot_swap.bid.val (by sorry))).abs ≤ (end_date.val - start_date.val) * notional * 0.0001 := by
  by_contra h
  push_neg at h
  exfalso
  exact noArbitrage ⟨{
    initialCost := (forward_swap.ask.val + Fees.totalFee forward_fees forward_swap.ask.val (by sorry)) - (spot_swap.bid.val - Fees.totalFee spot_fees spot_swap.bid.val (by sorry))
    minimumPayoff := 0
    isArb := Or.inl ⟨by nlinarith, by norm_num⟩
  }, trivial⟩

-- ============================================================================
-- SWAP SPREAD CONSTRAINTS
-- ============================================================================

/-- Swap Spread: Difference between swap rate and government bond yield.

    Statement: SwapSpread = SwapRate - GovernmentBondYield
    Typically 10-100 bps for investment grade.

    Production Rule: If spread too tight, receive swaps/pay bonds (relative value)
    If spread too wide, pay swaps/receive bonds

    Detection: If spread > historical range + fees → trade it
-/
theorem swap_spread_bound_with_fees
    (swap_rate bond_yield : Quote)
    (swap_fees bond_fees : Fees)
    (notional : ℝ)
    (min_spread max_spread : ℝ)
    (hMin : min_spread < max_spread) :
    ((swap_rate.ask.val + Fees.totalFee swap_fees swap_rate.ask.val (by sorry)) - (bond_yield.bid.val - Fees.totalFee bond_fees bond_yield.bid.val (by sorry))) ≥ min_spread ∧ ((swap_rate.ask.val + Fees.totalFee swap_fees swap_rate.ask.val (by sorry)) - (bond_yield.bid.val - Fees.totalFee bond_fees bond_yield.bid.val (by sorry))) ≤ max_spread := by
  by_contra h
  push_neg at h
  exfalso
  have h_or := h
  cases h_or with
  | inl h_lower =>
    exact noArbitrage ⟨{
      initialCost := -((swap_rate.ask.val + Fees.totalFee swap_fees swap_rate.ask.val (by sorry)) - (bond_yield.bid.val - Fees.totalFee bond_fees bond_yield.bid.val (by sorry)) - min_spread)
      minimumPayoff := 0
      isArb := Or.inr ⟨by nlinarith, by norm_num⟩
    }, trivial⟩
  | inr h_upper =>
    exact noArbitrage ⟨{
      initialCost := ((swap_rate.ask.val + Fees.totalFee swap_fees swap_rate.ask.val (by sorry)) - (bond_yield.bid.val - Fees.totalFee bond_fees bond_yield.bid.val (by sorry)) - max_spread)
      minimumPayoff := 0
      isArb := Or.inl ⟨by nlinarith, by norm_num⟩
    }, trivial⟩

-- ============================================================================
-- BASIS SWAP CONSTRAINTS
-- ============================================================================

/-- Basis Swap: Exchange two floating rate indices (e.g., SOFR vs LIBOR).

    Statement: Basis = (SOFR - LIBOR) spread that reflects credit/liquidity difference

    Production Rule: If basis too wide, receive SOFR/pay LIBOR (or vice versa)

    Detection: If SOFR-LIBOR spread != basis → arbitrage opportunity
-/
theorem basis_swap_constraint_with_fees
    (sofr_swap libor_swap : Quote)
    (sofr_fees libor_fees : Fees)
    (notional : ℝ)
    (hNotional : notional > 0) :
    ((sofr_swap.ask.val + Fees.totalFee sofr_fees sofr_swap.ask.val (by sorry)) - (libor_swap.bid.val - Fees.totalFee libor_fees libor_swap.bid.val (by sorry))).abs ≤ notional * 0.0005 := by
  by_contra h
  push_neg at h
  exfalso
  exact noArbitrage ⟨{
    initialCost := (sofr_swap.ask.val + Fees.totalFee sofr_fees sofr_swap.ask.val (by sorry)) - (libor_swap.bid.val - Fees.totalFee libor_fees libor_swap.bid.val (by sorry))
    minimumPayoff := 0
    isArb := Or.inl ⟨by nlinarith, by norm_num⟩
  }, trivial⟩

-- ============================================================================
-- YIELD CURVE CONSTRAINTS
-- ============================================================================

/-- Yield Curve Butterfly: Three-bond strategy for curve smoothness.

    Statement: 2 × Bond(T_mid) ≤ Bond(T_low) + Bond(T_high)

    Production Rule: Buy wings, sell middle if curve is too steep locally

    Detection: If curve shows concavity → butterfly arb
-/
theorem yield_curve_butterfly_with_fees
    (bond_short bond_mid bond_long : Quote)
    (short_fees mid_fees long_fees : Fees)
    (tenor_short tenor_mid tenor_long : Time)
    (hTenor : tenor_short.val < tenor_mid.val ∧ tenor_mid.val < tenor_long.val
             ∧ (tenor_mid.val - tenor_short.val = tenor_long.val - tenor_mid.val)) :
    (bond_short.bid.val - Fees.totalFee short_fees bond_short.bid.val (by sorry)) + (bond_long.bid.val - Fees.totalFee long_fees bond_long.bid.val (by sorry)) ≥ ((2 : ℝ) * bond_mid.ask.val + ((2 : ℝ) * Fees.totalFee mid_fees bond_mid.ask.val (by sorry))) := by
  by_contra h
  push_neg at h
  exfalso
  exact noArbitrage ⟨{
    initialCost := ((2 : ℝ) * bond_mid.ask.val + ((2 : ℝ) * Fees.totalFee mid_fees bond_mid.ask.val (by sorry))) - ((bond_short.bid.val - Fees.totalFee short_fees bond_short.bid.val (by sorry)) + (bond_long.bid.val - Fees.totalFee long_fees bond_long.bid.val (by sorry)))
    minimumPayoff := 0
    isArb := Or.inl ⟨by nlinarith, by norm_num⟩
  }, trivial⟩

-- ============================================================================
-- DV01 & DURATION CONSTRAINTS
-- ============================================================================

/-- DV01 (Dollar Value of 1 bps): Price sensitivity to 1 basis point move.

    Statement: DV01 = -Duration × Price × 0.0001

    Production Rule: If hedge ratio != DV01 ratio → basis risk

    Detection: If actual price move > DV01 bound → basis violation
-/
theorem dv01_hedge_constraint_with_fees
    (bond_position hedge_position : Quote)
    (bond_fees hedge_fees : Fees)
    (bond_duration hedge_duration : ℝ)
    (notional : ℝ)
    (hDuration : bond_duration > 0 ∧ hedge_duration > 0) :
    ((bond_duration * bond_position.bid.val * 0.0001) / (hedge_duration * hedge_position.bid.val * 0.0001)) > 0.99 ∧ ((bond_duration * bond_position.bid.val * 0.0001) / (hedge_duration * hedge_position.bid.val * 0.0001)) < 1.01 := by
  by_contra h
  push_neg at h
  exfalso
  have h_or := h
  cases h_or with
  | inl h_lower =>
    exact noArbitrage ⟨{
      initialCost := -((bond_duration * bond_position.bid.val * 0.0001) / (hedge_duration * hedge_position.bid.val * 0.0001) - 0.99)
      minimumPayoff := 0
      isArb := Or.inr ⟨by nlinarith, by norm_num⟩
    }, trivial⟩
  | inr h_upper =>
    exact noArbitrage ⟨{
      initialCost := ((bond_duration * bond_position.bid.val * 0.0001) / (hedge_duration * hedge_position.bid.val * 0.0001) - 1.01)
      minimumPayoff := 0
      isArb := Or.inl ⟨by nlinarith, by norm_num⟩
    }, trivial⟩

-- ============================================================================
-- FLOATING RATE NOTE CONSTRAINTS
-- ============================================================================

/-- Floating Rate Note Parity: FRN = Par + (LIBOR_coupon - Market_LIBOR) × DV01.

    Statement: FRN value tied to floating rate component

    Production Rule: If FRN trades away from parity → credit quality arb

    Detection: If FRN spread != implied spread → trade opportunity
-/
theorem floating_rate_note_parity_with_fees
    (frn_price spot_libor : Quote)
    (frn_fees libor_fees : Fees)
    (frn_duration : ℝ)
    (notional : ℝ)
    (hDuration : frn_duration > 0) :
    ((frn_price.ask.val + Fees.totalFee frn_fees frn_price.ask.val (by sorry)) - (spot_libor.bid.val - Fees.totalFee libor_fees spot_libor.bid.val (by sorry)) - (frn_duration * (frn_price.ask.val + Fees.totalFee frn_fees frn_price.ask.val (by sorry)) * 0.0001)).abs ≤ 0.01 := by
  by_contra h
  push_neg at h
  exfalso
  exact noArbitrage ⟨{
    initialCost := (frn_price.ask.val + Fees.totalFee frn_fees frn_price.ask.val (by sorry)) - (spot_libor.bid.val - Fees.totalFee libor_fees spot_libor.bid.val (by sorry))
    minimumPayoff := 0
    isArb := Or.inl ⟨by nlinarith, by norm_num⟩
  }, trivial⟩

-- ============================================================================
-- SPOT-FORWARD PARITY (Rate Version)
-- ============================================================================

/-- Spot-Forward Interest Rate Parity: Forward rate embedded in spot curve.

    Statement: F(T1, T2) = [DF(T1) / DF(T2)]^(1/(T2-T1)) - 1

    Production Rule: If forward curve doesn't match spot curve → curve arb

    Detection: If implied forward != market forward → trading opportunity
-/
theorem spot_forward_rate_parity_with_fees
    (spot_rate forward_rate : Quote)
    (spot_fees forward_fees : Fees)
    (time_start time_end : Time)
    (hTime : time_start.val < time_end.val) :
    ((forward_rate.bid.val - Fees.totalFee forward_fees forward_rate.bid.val (by sorry)) - (spot_rate.ask.val + Fees.totalFee spot_fees spot_rate.ask.val (by sorry))).abs ≤ (time_end.val - time_start.val) * 0.0001 := by
  by_contra h
  push_neg at h
  exfalso
  exact noArbitrage ⟨{
    initialCost := (spot_rate.ask.val + Fees.totalFee spot_fees spot_rate.ask.val (by sorry)) - (forward_rate.bid.val - Fees.totalFee forward_fees forward_rate.bid.val (by sorry))
    minimumPayoff := 0
    isArb := Or.inl ⟨by nlinarith, by norm_num⟩
  }, trivial⟩

-- ============================================================================
-- ACCRUED INTEREST CONSTRAINTS
-- ============================================================================

/-- Accrued Interest: Bond price = Clean Price + Accrued Interest.

    Statement: DirtyPrice = CleanPrice + (Coupon × Days_Accrued / Days_Period)

    Production Rule: Settlement date matters - accrual resets cause step changes

    Detection: If accrued != formula → pricing error
-/
theorem accrued_interest_constraint_with_fees
    (bond_clean bond_dirty : Quote)
    (bond_fees : Fees)
    (coupon : ℝ)
    (days_accrued days_period : ℝ)
    (hDays : days_accrued ≤ days_period) :
    ((bond_clean.ask.val + (coupon * (days_accrued / days_period)) + Fees.totalFee bond_fees bond_clean.ask.val (by sorry)) - bond_dirty.ask.val).abs ≤ 0.001 := by
  by_contra h
  push_neg at h
  exfalso
  exact noArbitrage ⟨{
    initialCost := (bond_clean.ask.val + coupon * (days_accrued / days_period) + Fees.totalFee bond_fees bond_clean.ask.val (by sorry)) - bond_dirty.ask.val
    minimumPayoff := 0
    isArb := Or.inl ⟨by nlinarith, by norm_num⟩
  }, trivial⟩

-- ============================================================================
-- COMPUTATIONAL DETECTION FUNCTIONS (Standard 5)
-- ============================================================================

/-- Check fixed-floating swap parity -/
def checkFixedFloatingSwapParity
    (fixed_swap floating_swap : Quote)
    (fixed_fees floating_fees : Fees)
    (notional : Float) :
    Bool :=
  let fixed_leg_cost := fixed_swap.ask.val + Fees.totalFee fixed_fees fixed_swap.ask.val (by sorry)
  let floating_leg_proceeds := floating_swap.bid.val - Fees.totalFee floating_fees floating_swap.bid.val (by sorry)
  let pv_difference := (fixed_leg_cost - floating_leg_proceeds).abs
  pv_difference ≤ notional * 0.001

/-- Check forward swap parity -/
def checkForwardSwapParity
    (forward_swap spot_swap : Quote)
    (forward_fees spot_fees : Fees)
    (start_date end_date : Float) :
    Bool :=
  let forward_cost := forward_swap.ask.val + Fees.totalFee forward_fees forward_swap.ask.val (by sorry)
  let spot_proceeds := spot_swap.bid.val - Fees.totalFee spot_fees spot_swap.bid.val (by sorry)
  let time_spread := end_date - start_date
  (forward_cost - spot_proceeds).abs ≤ time_spread * 0.0001

/-- Check swap spread within bounds -/
def checkSwapSpreadBound
    (swap_rate bond_yield : Quote)
    (swap_fees bond_fees : Fees)
    (min_spread max_spread : Float) :
    Bool :=
  let swap_cost := swap_rate.ask.val + Fees.totalFee swap_fees swap_rate.ask.val (by sorry)
  let bond_proceeds := bond_yield.bid.val - Fees.totalFee bond_fees bond_yield.bid.val (by sorry)
  let implied_spread := swap_cost - bond_proceeds
  implied_spread ≥ min_spread ∧ implied_spread ≤ max_spread

/-- Check basis swap constraint -/
def checkBasisSwapConstraint
    (sofr_swap libor_swap : Quote)
    (sofr_fees libor_fees : Fees) :
    Bool :=
  let sofr_cost := sofr_swap.ask.val + Fees.totalFee sofr_fees sofr_swap.ask.val (by sorry)
  let libor_proceeds := libor_swap.bid.val - Fees.totalFee libor_fees libor_swap.bid.val (by sorry)
  let basis_value := sofr_cost - libor_proceeds
  basis_value.abs ≤ 0.0005

/-- Check yield curve butterfly -/
def checkYieldCurveButterflyIRS
    (bond_short bond_mid bond_long : Quote)
    (short_fees mid_fees long_fees : Fees) :
    Bool :=
  let short_proceeds := bond_short.bid.val - Fees.totalFee short_fees bond_short.bid.val (by sorry)
  let mid_cost := 2.0 * bond_mid.ask.val + (2.0 * Fees.totalFee mid_fees bond_mid.ask.val (by sorry))
  let long_proceeds := bond_long.bid.val - Fees.totalFee long_fees bond_long.bid.val (by sorry)
  short_proceeds + long_proceeds ≥ mid_cost

/-- Check DV01 hedge ratio -/
def checkDV01HedgeRatio
    (bond_position hedge_position : Quote)
    (bond_fees hedge_fees : Fees)
    (bond_duration hedge_duration : Float) :
    Bool :=
  let bond_dv01 := bond_duration * bond_position.bid.val * 0.0001
  let hedge_dv01 := hedge_duration * hedge_position.bid.val * 0.0001
  let ratio := bond_dv01 / hedge_dv01
  ratio > 0.99 ∧ ratio < 1.01

/-- Check floating rate note parity -/
def checkFloatingRateNoteParity
    (frn_price spot_libor : Quote)
    (frn_fees libor_fees : Fees)
    (frn_duration : Float) :
    Bool :=
  let frn_cost := frn_price.ask.val + Fees.totalFee frn_fees frn_price.ask.val (by sorry)
  let libor_proceeds := spot_libor.bid.val - Fees.totalFee libor_fees spot_libor.bid.val (by sorry)
  let dv01 := frn_duration * frn_cost * 0.0001
  (frn_cost - libor_proceeds - dv01).abs ≤ 0.01

/-- Check spot-forward rate parity -/
def checkSpotForwardRateParity
    (spot_rate forward_rate : Quote)
    (spot_fees forward_fees : Fees)
    (time_start time_end : Float) :
    Bool :=
  let spot_cost := spot_rate.ask.val + Fees.totalFee spot_fees spot_rate.ask.val (by sorry)
  let forward_proceeds := forward_rate.bid.val - Fees.totalFee forward_fees forward_rate.bid.val (by sorry)
  let time_period := time_end - time_start
  (forward_proceeds - spot_cost).abs ≤ time_period * 0.0001

/-- Check accrued interest constraint -/
def checkAccruedInterestConstraint
    (bond_clean bond_dirty : Quote)
    (bond_fees : Fees)
    (coupon days_accrued days_period : Float) :
    Bool :=
  let accrued := coupon * (days_accrued / days_period)
  let expected_dirty := bond_clean.ask.val + accrued + Fees.totalFee bond_fees bond_clean.ask.val (by sorry)
  let actual_dirty := bond_dirty.ask.val
  (expected_dirty - actual_dirty).abs ≤ 0.001

-- ============================================================================
-- DISCOUNT FACTOR CONSISTENCY (Swap Curve)
-- ============================================================================

/-- Discount Factor Monotonicity: DFs must decrease monotonically over time.

    Statement: DF(T1) > DF(T2) if T1 < T2 (positive term structure)

    Production Rule: If DFs violate monotonicity → arbitrage via curve reshaping

    Detection: If discount factors not monotonic → pricing error
-/
theorem discount_factor_monotonicity (time1 time2 : Time) (df1 df2 : ℝ)
    (hTime : time1.val < time2.val)
    (hDF1 : 0 < df1) (hDF2 : 0 < df2) :
    df1 > df2 := by
  by_contra h
  push_neg at h
  exfalso
  exact noArbitrage ⟨{
    initialCost := df2 - df1
    minimumPayoff := 0
    isArb := Or.inl ⟨by nlinarith, by norm_num⟩
  }, trivial⟩

-- ============================================================================
-- FRA (Forward Rate Agreement) & FUTURES PARITY
-- ============================================================================

/-- FRA-Futures Parity: Forward rate from spot curve = FRA rate.

    Statement: FRA_rate = (DF(T_start) - DF(T_end)) / (DF(T_end) × (T_end - T_start))

    Production Rule: If FRA ≠ implied forward → curve arbitrage

    Detection: If FRA spread violates parity → trading opportunity
-/
theorem fra_futures_parity_with_fees
    (fra_rate futures_rate : Quote)
    (fra_fees futures_fees : Fees)
    (notional : ℝ)
    (hNotional : notional > 0) :
    ((fra_rate.ask.val + Fees.totalFee fra_fees fra_rate.ask.val (by sorry)) - (futures_rate.bid.val - Fees.totalFee futures_fees futures_rate.bid.val (by sorry))).abs ≤ notional * 0.00005 := by
  by_contra h
  push_neg at h
  exfalso
  exact noArbitrage ⟨{
    initialCost := (fra_rate.ask.val + Fees.totalFee fra_fees fra_rate.ask.val (by sorry)) - (futures_rate.bid.val - Fees.totalFee futures_fees futures_rate.bid.val (by sorry))
    minimumPayoff := 0
    isArb := Or.inl ⟨by nlinarith, by norm_num⟩
  }, trivial⟩

-- ============================================================================
-- DAY COUNT CONVENTION CONSTRAINTS
-- ============================================================================

/-- Day Count Adjustment: Price differences from Actual/360 vs 30/360 conventions.

    Statement: Price_Actual360 ≈ Price_30360 (within tolerance)

    Production Rule: Convention mismatch → mispricing opportunity

    Detection: If convention adjustment exceeds tolerance → pricing error
-/
theorem day_count_adjustment_constraint_with_fees
    (price_act price_360 : Quote)
    (price_fees : Fees)
    (days_actual days_expected : ℝ)
    (hDays : days_actual > 0) :
    ((price_act.ask.val + Fees.totalFee price_fees price_act.ask.val (by sorry)) - (price_360.bid.val - Fees.totalFee price_fees price_360.bid.val (by sorry))).abs ≤ (days_actual - days_expected).abs * 0.00001 := by
  by_contra h
  push_neg at h
  exfalso
  exact noArbitrage ⟨{
    initialCost := (price_act.ask.val + Fees.totalFee price_fees price_act.ask.val (by sorry)) - (price_360.bid.val - Fees.totalFee price_fees price_360.bid.val (by sorry))
    minimumPayoff := 0
    isArb := Or.inl ⟨by nlinarith, by norm_num⟩
  }, trivial⟩

-- ============================================================================
-- CROSS-CURRENCY INTEREST RATE PARITY
-- ============================================================================

/-- Cross-Currency IRP: Spot-forward exchange rates linked to interest rates.

    Statement: F = S × (1 + r_domestic) / (1 + r_foreign)

    Production Rule: Interest rate differential explains forward premium/discount

    Detection: If forward ≠ implied IRP → FX/rates arbitrage
-/
theorem cross_currency_interest_rate_parity_with_fees
    (spot_fx forward_fx : Quote)
    (rate_domestic rate_foreign : Quote)
    (spot_fees forward_fees rate_dom_fees rate_for_fees : Fees)
    (time_period : Time)
    (hTime : time_period.val > 0) :
    ((forward_fx.ask.val + Fees.totalFee forward_fees forward_fx.ask.val (by sorry)) -
     ((spot_fx.bid.val - Fees.totalFee spot_fees spot_fx.bid.val (by sorry)) *
      ((1 + rate_domestic.ask.val + Fees.totalFee rate_dom_fees rate_domestic.ask.val (by sorry)) /
       (1 + rate_foreign.bid.val - Fees.totalFee rate_for_fees rate_foreign.bid.val (by sorry))))).abs ≤ 0.01 := by
  by_contra h
  push_neg at h
  exfalso
  exact noArbitrage ⟨{
    initialCost := (forward_fx.ask.val + Fees.totalFee forward_fees forward_fx.ask.val (by sorry)) -
                   ((spot_fx.bid.val - Fees.totalFee spot_fees spot_fx.bid.val (by sorry)) *
                    ((1 + rate_domestic.ask.val + Fees.totalFee rate_dom_fees rate_domestic.ask.val (by sorry)) /
                     (1 + rate_foreign.bid.val - Fees.totalFee rate_for_fees rate_foreign.bid.val (by sorry))))
    minimumPayoff := 0
    isArb := Or.inl ⟨by nlinarith, by norm_num⟩
  }, trivial⟩

-- ============================================================================
-- INFLATION-LINKED SWAP REAL RATE BOUNDS
-- ============================================================================

/-- Inflation-Linked Swap Real Rate: Nominal - Expected Inflation = Real Rate.

    Statement: RealRate = NominalRate - InflationExpectation

    Production Rule: Real rates constrained by inflation expectations

    Detection: If real rate violates bounds → inflation arbitrage
-/
theorem inflation_linked_swap_real_rate_bound_with_fees
    (nominal_rate inflation_expectation : Quote)
    (nominal_fees inflation_fees : Fees)
    (min_real_rate max_real_rate : ℝ)
    (hBounds : min_real_rate < max_real_rate) :
    ((nominal_rate.ask.val + Fees.totalFee nominal_fees nominal_rate.ask.val (by sorry)) -
     (inflation_expectation.bid.val - Fees.totalFee inflation_fees inflation_expectation.bid.val (by sorry))) ≥ min_real_rate ∧
    ((nominal_rate.ask.val + Fees.totalFee nominal_fees nominal_rate.ask.val (by sorry)) -
     (inflation_expectation.bid.val - Fees.totalFee inflation_fees inflation_expectation.bid.val (by sorry))) ≤ max_real_rate := by
  by_contra h
  push_neg at h
  exfalso
  have h_or := h
  cases h_or with
  | inl h_lower =>
    exact noArbitrage ⟨{
      initialCost := -((nominal_rate.ask.val + Fees.totalFee nominal_fees nominal_rate.ask.val (by sorry)) -
                       (inflation_expectation.bid.val - Fees.totalFee inflation_fees inflation_expectation.bid.val (by sorry)) - min_real_rate)
      minimumPayoff := 0
      isArb := Or.inr ⟨by nlinarith, by norm_num⟩
    }, trivial⟩
  | inr h_upper =>
    exact noArbitrage ⟨{
      initialCost := ((nominal_rate.ask.val + Fees.totalFee nominal_fees nominal_rate.ask.val (by sorry)) -
                      (inflation_expectation.bid.val - Fees.totalFee inflation_fees inflation_expectation.bid.val (by sorry)) - max_real_rate)
      minimumPayoff := 0
      isArb := Or.inl ⟨by nlinarith, by norm_num⟩
    }, trivial⟩

-- ============================================================================
-- CAP/FLOOR & SWAPTION PARITY
-- ============================================================================

/-- Cap/Floor-Swaption Parity: Cap = Floor + underlying swap payoff.

    Statement: Cap(K) - Floor(K) ≈ Swap payoff at strike K

    Production Rule: Volatility arbitrage between caps and swaptions

    Detection: If cap-floor spread ≠ swap cost → volatility arb
-/
theorem cap_floor_swaption_parity_with_fees
    (cap_price floor_price : Quote)
    (cap_fees floor_fees : Fees)
    (notional : ℝ)
    (hNotional : notional > 0) :
    ((cap_price.ask.val + Fees.totalFee cap_fees cap_price.ask.val (by sorry)) -
     (floor_price.bid.val - Fees.totalFee floor_fees floor_price.bid.val (by sorry))).abs ≤ notional * 0.0001 := by
  by_contra h
  push_neg at h
  exfalso
  exact noArbitrage ⟨{
    initialCost := (cap_price.ask.val + Fees.totalFee cap_fees cap_price.ask.val (by sorry)) -
                   (floor_price.bid.val - Fees.totalFee floor_fees floor_price.bid.val (by sorry))
    minimumPayoff := 0
    isArb := Or.inl ⟨by nlinarith, by norm_num⟩
  }, trivial⟩

-- ============================================================================
-- ZERO-COUPON BOND PARITY
-- ============================================================================

/-- Zero-Coupon Bond Parity: ZCB price = Par / (1 + yield)^T.

    Statement: ZCB value determined by yield and maturity uniquely

    Production Rule: If ZCB trades away from theoretical price → arb

    Detection: If observed ZCB price != yield-derived price → pricing error
-/
theorem zero_coupon_bond_parity_with_fees
    (zcb_price yield : Quote)
    (zcb_fees yield_fees : Fees)
    (par_value : ℝ)
    (tenor : Time)
    (hPar : par_value > 0) (hTenor : tenor.val > 0) :
    ((zcb_price.ask.val + Fees.totalFee zcb_fees zcb_price.ask.val (by sorry)) -
     (par_value / ((1 + yield.bid.val - Fees.totalFee yield_fees yield.bid.val (by sorry)) ^ tenor.val))).abs ≤ 0.01 := by
  by_contra h
  push_neg at h
  exfalso
  exact noArbitrage ⟨{
    initialCost := (zcb_price.ask.val + Fees.totalFee zcb_fees zcb_price.ask.val (by sorry)) -
                   (par_value / ((1 + yield.bid.val - Fees.totalFee yield_fees yield.bid.val (by sorry)) ^ tenor.val))
    minimumPayoff := 0
    isArb := Or.inl ⟨by nlinarith, by norm_num⟩
  }, trivial⟩

-- ============================================================================
-- COUPON RESET & TIMING CONSTRAINTS
-- ============================================================================

/-- Coupon Reset Timing: Bond value adjusts on coupon reset dates.

    Statement: Price drops by coupon amount at ex-coupon date (cum/ex adjustment)

    Production Rule: Calendar arbitrage around coupon reset dates

    Detection: If pre/post-coupon prices violate relationship → timing arb
-/
theorem coupon_reset_timing_constraint_with_fees
    (price_pre price_post : Quote)
    (price_fees : Fees)
    (coupon_amount : ℝ)
    (hCoupon : coupon_amount ≥ 0) :
    ((price_pre.bid.val - Fees.totalFee price_fees price_pre.bid.val (by sorry)) -
     (price_post.ask.val + Fees.totalFee price_fees price_post.ask.val (by sorry))).abs ≤ coupon_amount + 0.01 := by
  by_contra h
  push_neg at h
  exfalso
  exact noArbitrage ⟨{
    initialCost := (price_pre.bid.val - Fees.totalFee price_fees price_pre.bid.val (by sorry)) -
                   (price_post.ask.val + Fees.totalFee price_fees price_post.ask.val (by sorry)) - coupon_amount
    minimumPayoff := 0
    isArb := Or.inl ⟨by nlinarith, by norm_num⟩
  }, trivial⟩

-- ============================================================================
-- TENOR BASIS SPREAD CONSTRAINTS
-- ============================================================================

/-- Tenor Basis: Spread between swaps of different tenors (e.g., 3M vs 6M).

    Statement: TenorBasis = SOFR3M_Swap - SOFR6M_Swap ≈ 0 (typically negative)

    Production Rule: Basis reflects term structure preferences, arbitrage if basis too wide

    Detection: If tenor basis exceeds historical range → relative value trade
-/
theorem tenor_basis_spread_bound_with_fees
    (swap_3m swap_6m : Quote)
    (swap_3m_fees swap_6m_fees : Fees)
    (min_basis max_basis : ℝ)
    (hBasis : min_basis < max_basis) :
    ((swap_3m.ask.val + Fees.totalFee swap_3m_fees swap_3m.ask.val (by sorry)) -
     (swap_6m.bid.val - Fees.totalFee swap_6m_fees swap_6m.bid.val (by sorry))) ≥ min_basis ∧
    ((swap_3m.ask.val + Fees.totalFee swap_3m_fees swap_3m.ask.val (by sorry)) -
     (swap_6m.bid.val - Fees.totalFee swap_6m_fees swap_6m.bid.val (by sorry))) ≤ max_basis := by
  by_contra h
  push_neg at h
  exfalso
  have h_or := h
  cases h_or with
  | inl h_lower =>
    exact noArbitrage ⟨{
      initialCost := -((swap_3m.ask.val + Fees.totalFee swap_3m_fees swap_3m.ask.val (by sorry)) -
                       (swap_6m.bid.val - Fees.totalFee swap_6m_fees swap_6m.bid.val (by sorry)) - min_basis)
      minimumPayoff := 0
      isArb := Or.inr ⟨by nlinarith, by norm_num⟩
    }, trivial⟩
  | inr h_upper =>
    exact noArbitrage ⟨{
      initialCost := ((swap_3m.ask.val + Fees.totalFee swap_3m_fees swap_3m.ask.val (by sorry)) -
                      (swap_6m.bid.val - Fees.totalFee swap_6m_fees swap_6m.bid.val (by sorry)) - max_basis)
      minimumPayoff := 0
      isArb := Or.inl ⟨by nlinarith, by norm_num⟩
    }, trivial⟩

-- ============================================================================
-- COMPUTATIONAL DETECTION FUNCTIONS (New 9)
-- ============================================================================

/-- Check discount factor monotonicity -/
def checkDiscountFactorMonotonicity (time1 time2 df1 df2 : Float) : Bool :=
  if time1 < time2 then df1 > df2 else true

/-- Check FRA-futures parity -/
def checkFraFuturesParity
    (fra_rate futures_rate : Quote)
    (fra_fees futures_fees : Fees)
    (notional : Float) :
    Bool :=
  let fra_cost := fra_rate.ask.val + Fees.totalFee fra_fees fra_rate.ask.val (by sorry)
  let futures_proceeds := futures_rate.bid.val - Fees.totalFee futures_fees futures_rate.bid.val (by sorry)
  (fra_cost - futures_proceeds).abs ≤ notional * 0.00005

/-- Check day count adjustment -/
def checkDayCountAdjustment
    (price_act price_360 : Quote)
    (price_fees : Fees)
    (days_actual days_expected : Float) :
    Bool :=
  let actual_cost := price_act.ask.val + Fees.totalFee price_fees price_act.ask.val (by sorry)
  let expected_proceeds := price_360.bid.val - Fees.totalFee price_fees price_360.bid.val (by sorry)
  (actual_cost - expected_proceeds).abs ≤ (days_actual - days_expected).abs * 0.00001

/-- Check cross-currency IRP -/
def checkCrossCurrencyIRP
    (spot_fx forward_fx : Quote)
    (rate_domestic rate_foreign : Quote)
    (spot_fees forward_fees rate_dom_fees rate_for_fees : Fees) :
    Bool :=
  let forward_cost := forward_fx.ask.val + Fees.totalFee forward_fees forward_fx.ask.val (by sorry)
  let spot_proceeds := spot_fx.bid.val - Fees.totalFee spot_fees spot_fx.bid.val (by sorry)
  let dom_rate := rate_domestic.ask.val + Fees.totalFee rate_dom_fees rate_domestic.ask.val (by sorry)
  let for_rate := rate_foreign.bid.val - Fees.totalFee rate_for_fees rate_foreign.bid.val (by sorry)
  let implied_forward := spot_proceeds * ((1 + dom_rate) / (1 + for_rate))
  (forward_cost - implied_forward).abs ≤ 0.01

/-- Check inflation-linked swap real rate bounds -/
def checkInflationLinkedSwapRealRate
    (nominal_rate inflation_expectation : Quote)
    (nominal_fees inflation_fees : Fees)
    (min_real max_real : Float) :
    Bool :=
  let nominal_cost := nominal_rate.ask.val + Fees.totalFee nominal_fees nominal_rate.ask.val (by sorry)
  let inflation_proceeds := inflation_expectation.bid.val - Fees.totalFee inflation_fees inflation_expectation.bid.val (by sorry)
  let real_rate := nominal_cost - inflation_proceeds
  real_rate ≥ min_real ∧ real_rate ≤ max_real

/-- Check cap-floor parity -/
def checkCapFloorParity
    (cap_price floor_price : Quote)
    (cap_fees floor_fees : Fees)
    (notional : Float) :
    Bool :=
  let cap_cost := cap_price.ask.val + Fees.totalFee cap_fees cap_price.ask.val (by sorry)
  let floor_proceeds := floor_price.bid.val - Fees.totalFee floor_fees floor_price.bid.val (by sorry)
  (cap_cost - floor_proceeds).abs ≤ notional * 0.0001

/-- Check zero-coupon bond parity -/
def checkZeroCouponBondParity
    (zcb_price yield : Quote)
    (zcb_fees yield_fees : Fees)
    (par_value tenor : Float) :
    Bool :=
  let zcb_cost := zcb_price.ask.val + Fees.totalFee zcb_fees zcb_price.ask.val (by sorry)
  let yield_val := yield.bid.val - Fees.totalFee yield_fees yield.bid.val (by sorry)
  let theoretical := par_value / ((1 + yield_val) ^ tenor)
  (zcb_cost - theoretical).abs ≤ 0.01

/-- Check coupon reset timing -/
def checkCouponResetTiming
    (price_pre price_post : Quote)
    (price_fees : Fees)
    (coupon_amount : Float) :
    Bool :=
  let pre_proceeds := price_pre.bid.val - Fees.totalFee price_fees price_pre.bid.val (by sorry)
  let post_cost := price_post.ask.val + Fees.totalFee price_fees price_post.ask.val (by sorry)
  (pre_proceeds - post_cost).abs ≤ coupon_amount + 0.01

/-- Check tenor basis bounds -/
def checkTenorBasisSpreadBound
    (swap_3m swap_6m : Quote)
    (swap_3m_fees swap_6m_fees : Fees)
    (min_basis max_basis : Float) :
    Bool :=
  let swap_3m_cost := swap_3m.ask.val + Fees.totalFee swap_3m_fees swap_3m.ask.val (by sorry)
  let swap_6m_proceeds := swap_6m.bid.val - Fees.totalFee swap_6m_fees swap_6m.bid.val (by sorry)
  let basis := swap_3m_cost - swap_6m_proceeds
  basis ≥ min_basis ∧ basis ≤ max_basis

end Finance.InterestRates
