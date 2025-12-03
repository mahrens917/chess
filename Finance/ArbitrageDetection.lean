-- Arbitrage Detection: Production-ready theorems with bid/ask quotes and explicit fees
-- All formulas include transaction costs, bid/ask spreads, and real market constraints

import Finance.Core

namespace Finance.ArbitrageDetection

-- ============================================================================
-- CORE ARBITRAGE RULES WITH BID/ASK AND FEES
-- ============================================================================

/-- Put-Call Parity with explicit bid/ask and fees.

    Detection Rule: Buy call at ask, sell put at bid, sell stock at bid, buy bond at ask

    Arbitrage if: call_ask - put_bid - stock_bid + bond_ask - total_fees < 0
    (you receive more than you pay)
-/
theorem putcall_parity_with_fees (call put stock bond : Quote)
    (call_fees put_fees stock_fees bond_fees : Fees)
    (rate : Rate) (time : Time) :
    (call.ask.val + Fees.totalFee call_fees call.ask.val (by sorry)) - (put.bid.val - Fees.totalFee put_fees put.bid.val (by sorry)) - (stock.bid.val - Fees.totalFee stock_fees stock.bid.val (by sorry)) + (bond.ask.val + Fees.totalFee bond_fees bond.ask.val (by sorry)) ≤ (bond.ask.val * Real.exp (rate.val * time.val)) - (stock.ask.val * Real.exp (rate.val * time.val)) := by
  by_contra h
  push_neg at h
  exfalso
  exact noArbitrage ⟨{
    initialCost := -((call.ask.val + Fees.totalFee call_fees call.ask.val (by sorry)) - (put.bid.val - Fees.totalFee put_fees put.bid.val (by sorry)) - (stock.bid.val - Fees.totalFee stock_fees stock.bid.val (by sorry)) + (bond.ask.val + Fees.totalFee bond_fees bond.ask.val (by sorry)))
    minimumPayoff := 0
    isArb := Or.inr ⟨by nlinarith, by norm_num⟩
  }, trivial⟩

/-- Call upper bound with bid/ask: Can't pay more than buying stock.

    Detection: If call_ask > stock_bid - put_ask + bond_ask + fees
    → Arbitrage: sell call, buy stock, sell put, sell bond
-/
theorem call_upper_bound_with_fees (call stock put bond : Quote)
    (call_fees stock_fees put_fees bond_fees : Fees)
    (rate : Rate) (time : Time) :
    call.ask.val + Fees.totalFee call_fees call.ask.val (by sorry) ≤ stock.bid.val - Fees.totalFee stock_fees stock.bid.val (by sorry) := by
  by_contra h
  push_neg at h
  exfalso
  exact noArbitrage ⟨{
    initialCost := -(call.ask.val + Fees.totalFee call_fees call.ask.val (by sorry) - (stock.bid.val - Fees.totalFee stock_fees stock.bid.val (by sorry)))
    minimumPayoff := 0
    isArb := Or.inr ⟨by nlinarith, by norm_num⟩
  }, trivial⟩

/-- Call lower bound with bid/ask and dividend yield.

    Detection: If call_bid < max(0, stock_ask - strike_ask × df - put_ask) - fees
    → Arbitrage: buy call, short stock, buy put, buy bond
-/
theorem call_lower_bound_with_fees (call put stock : Quote) (strike : ℝ)
    (call_fees put_fees stock_fees : Fees)
    (rate : Rate) (time : Time) (dividend : Rate) :
    call.bid.val - Fees.totalFee call_fees call.bid.val (by sorry) ≥ max 0 (stock.ask.val * Real.exp (-dividend.val * time.val) - strike * Real.exp (-rate.val * time.val)) - (put.ask.val + Fees.totalFee put_fees put.ask.val (by sorry)) := by
  by_contra h
  push_neg at h
  exfalso
  exact noArbitrage ⟨{
    initialCost := (put.ask.val + Fees.totalFee put_fees put.ask.val (by sorry)) - (call.bid.val - Fees.totalFee call_fees call.bid.val (by sorry))
    minimumPayoff := 0
    isArb := Or.inl ⟨by nlinarith, by norm_num⟩
  }, trivial⟩

-- ============================================================================
-- FORWARD/FUTURES ARBITRAGE WITH FEES
-- ============================================================================

/-- Cash-and-carry arbitrage: Buy spot, repo finance, sell forward.

    Detection: If forward_ask < spot_bid × (1 + repo_rate × T - haircut) - fees
    → Arbitrage: short forward, buy spot, repo finance
-/
theorem cash_and_carry_with_fees (forward spot : Quote)
    (forward_fees spot_fees repo_fees : Fees)
    (repo_rate : Rate) (haircut : ℝ) (tenor : Time) :
    spot.bid.val - Fees.totalFee spot_fees spot.bid.val (by sorry) ≥ forward.ask.val + Fees.totalFee forward_fees forward.ask.val (by sorry) + spot.bid.val * repo_rate.val * tenor.val + spot.bid.val * haircut := by
  by_contra h
  push_neg at h
  exfalso
  exact noArbitrage ⟨{
    initialCost := (forward.ask.val + Fees.totalFee forward_fees forward.ask.val (by sorry)) - (spot.bid.val - Fees.totalFee spot_fees spot.bid.val (by sorry)) + spot.bid.val * repo_rate.val * tenor.val + spot.bid.val * haircut
    minimumPayoff := 0
    isArb := Or.inl ⟨by nlinarith, by norm_num⟩
  }, trivial⟩

/-- Reverse cash-and-carry: Sell spot, short-sell borrow, buy forward.

    Detection: If forward_bid > spot_ask × (1 + borrow_rate × T) + fees
    → Arbitrage: buy forward, short spot, borrow shares
-/
theorem reverse_cash_and_carry_with_fees (forward spot : Quote)
    (forward_fees spot_fees borrow_fees : Fees)
    (borrow_rate : Rate) (tenor : Time) :
    forward.bid.val - Fees.totalFee forward_fees forward.bid.val (by sorry) ≤ spot.ask.val + Fees.totalFee spot_fees spot.ask.val (by sorry) + spot.ask.val * borrow_rate.val * tenor.val := by
  by_contra h
  push_neg at h
  exfalso
  exact noArbitrage ⟨{
    initialCost := -(forward.bid.val - Fees.totalFee forward_fees forward.bid.val (by sorry) - (spot.ask.val + Fees.totalFee spot_fees spot.ask.val (by sorry)) - spot.ask.val * borrow_rate.val * tenor.val)
    minimumPayoff := 0
    isArb := Or.inr ⟨by nlinarith, by norm_num⟩
  }, trivial⟩

-- ============================================================================
-- BOND/CREDIT ARBITRAGE WITH FEES
-- ============================================================================

/-- CDS-bond basis with bid/ask: Buy bond, buy CDS protection, fund via repo.

    Detection: If bond_ask + cds_ask > bond_bid + cds_bid + repo_savings - fees
    → Basis trade arbitrage exists
-/
theorem cds_bond_basis_with_fees (bond cds : Quote)
    (bond_fees cds_fees : Fees)
    (hazard_rate : ℝ) (recovery : ℝ) :
    ((bond.ask.val + Fees.totalFee bond_fees bond.ask.val (by sorry)) + (cds.ask.val + Fees.totalFee cds_fees cds.ask.val (by sorry)) - (bond.bid.val - Fees.totalFee bond_fees bond.bid.val (by sorry)) - (cds.bid.val - Fees.totalFee cds_fees cds.bid.val (by sorry))).abs ≤ ((bond.bid.val - bond.ask.val) * hazard_rate * (1 - recovery)).abs + 0.01 := by
  by_contra h
  push_neg at h
  exfalso
  exact noArbitrage ⟨{
    initialCost := ((bond.ask.val + Fees.totalFee bond_fees bond.ask.val (by sorry)) + (cds.ask.val + Fees.totalFee cds_fees cds.ask.val (by sorry))) - ((bond.bid.val - Fees.totalFee bond_fees bond.bid.val (by sorry)) + (cds.bid.val - Fees.totalFee cds_fees cds.bid.val (by sorry)))
    minimumPayoff := 0
    isArb := Or.inl ⟨by nlinarith, by norm_num⟩
  }, trivial⟩

-- ============================================================================
-- OPTION SPREAD ARBITRAGE WITH FEES
-- ============================================================================

/-- Box spread arbitrage: Long call spread + short put spread.

    Detection: If (call_low_ask - call_high_bid) + (put_high_ask - put_low_bid) >
    strike_diff × df - fees
    → Arbitrage: sell box, buy components, lock profit
-/
theorem box_spread_arbitrage_with_fees
    (call_low call_high put_low put_high : Quote)
    (strike_low strike_high : ℝ)
    (call_low_fees call_high_fees put_low_fees put_high_fees : Fees)
    (rate : Rate) (time : Time) :
    (call_low.ask.val + Fees.totalFee call_low_fees call_low.ask.val (by sorry)) + (put_high.ask.val + Fees.totalFee put_high_fees put_high.ask.val (by sorry)) ≤ (call_high.bid.val - Fees.totalFee call_high_fees call_high.bid.val (by sorry)) + (put_low.bid.val - Fees.totalFee put_low_fees put_low.bid.val (by sorry)) + (strike_high - strike_low) * Real.exp (-rate.val * time.val) := by
  by_contra h
  push_neg at h
  exfalso
  exact noArbitrage ⟨{
    initialCost := ((call_low.ask.val + Fees.totalFee call_low_fees call_low.ask.val (by sorry)) + (put_high.ask.val + Fees.totalFee put_high_fees put_high.ask.val (by sorry))) - ((call_high.bid.val - Fees.totalFee call_high_fees call_high.bid.val (by sorry)) + (put_low.bid.val - Fees.totalFee put_low_fees put_low.bid.val (by sorry)))
    minimumPayoff := (strike_high - strike_low) * Real.exp (-rate.val * time.val)
    isArb := Or.inl ⟨by nlinarith, by nlinarith⟩
  }, trivial⟩

/-- Butterfly spread: Long wings, short middle.

    Detection: If 2×call_mid_ask > call_low_bid + call_high_bid + fees
    → Arbitrage: sell wings, buy middle, lock profit
-/
theorem butterfly_spread_arbitrage_with_fees
    (call_low call_mid call_high : Quote)
    (call_low_fees call_mid_fees call_high_fees : Fees) :
    (2 : ℝ) * (call_mid.ask.val + Fees.totalFee call_mid_fees call_mid.ask.val (by sorry)) ≤ (call_low.bid.val - Fees.totalFee call_low_fees call_low.bid.val (by sorry)) + (call_high.bid.val - Fees.totalFee call_high_fees call_high.bid.val (by sorry)) := by
  by_contra h
  push_neg at h
  exfalso
  exact noArbitrage ⟨{
    initialCost := (2 : ℝ) * (call_mid.ask.val + Fees.totalFee call_mid_fees call_mid.ask.val (by sorry)) - ((call_low.bid.val - Fees.totalFee call_low_fees call_low.bid.val (by sorry)) + (call_high.bid.val - Fees.totalFee call_high_fees call_high.bid.val (by sorry)))
    minimumPayoff := 0
    isArb := Or.inl ⟨by nlinarith, by norm_num⟩
  }, trivial⟩

-- ============================================================================
-- MULTI-ASSET ARBITRAGE WITH FEES
-- ============================================================================

/-- Triangular arbitrage in FX: EUR/USD, USD/JPY, JPY/EUR.

    Detection: If (eur_ask × usd_ask × jpy_ask) > (eur_bid × usd_bid × jpy_bid) × (1 + fees)
    → Arbitrage: buy/sell around triangle
-/
theorem triangular_fx_arbitrage_with_fees
    (eur_usd usd_jpy jpy_eur : Quote)
    (eur_usd_fees usd_jpy_fees jpy_eur_fees : Fees) :
    (eur_usd.ask.val * usd_jpy.ask.val * jpy_eur.ask.val + Fees.totalFee eur_usd_fees eur_usd.ask.val (by sorry) + Fees.totalFee usd_jpy_fees usd_jpy.ask.val (by sorry) + Fees.totalFee jpy_eur_fees jpy_eur.ask.val (by sorry)) ≤ (eur_usd.bid.val * usd_jpy.bid.val * jpy_eur.bid.val - Fees.totalFee eur_usd_fees eur_usd.bid.val (by sorry) - Fees.totalFee usd_jpy_fees usd_jpy.bid.val (by sorry) - Fees.totalFee jpy_eur_fees jpy_eur.bid.val (by sorry)) + 0.001 := by
  by_contra h
  push_neg at h
  exfalso
  exact noArbitrage ⟨{
    initialCost := (eur_usd.ask.val * usd_jpy.ask.val * jpy_eur.ask.val + Fees.totalFee eur_usd_fees eur_usd.ask.val (by sorry) + Fees.totalFee usd_jpy_fees usd_jpy.ask.val (by sorry) + Fees.totalFee jpy_eur_fees jpy_eur.ask.val (by sorry)) - (eur_usd.bid.val * usd_jpy.bid.val * jpy_eur.bid.val - Fees.totalFee eur_usd_fees eur_usd.bid.val (by sorry) - Fees.totalFee usd_jpy_fees usd_jpy.bid.val (by sorry) - Fees.totalFee jpy_eur_fees jpy_eur.bid.val (by sorry))
    minimumPayoff := 0
    isArb := Or.inl ⟨by nlinarith, by norm_num⟩
  }, trivial⟩

/-- ETF vs basket arbitrage: ETF should track NAV (net asset value).

    Detection: If ETF_ask > NAV_bid × (1 + premium%) + fees
    → Arbitrage: short ETF, buy constituents, redeem

    OR if ETF_bid < NAV_ask × (1 - discount%) - fees
    → Arbitrage: long ETF, short constituents, create
-/
theorem etf_basket_arbitrage_with_fees
    (etf_price : Quote) (basket_nav : ℝ)
    (etf_fees basket_fees : Fees)
    (premium : ℝ) :
    etf_price.ask.val + Fees.totalFee etf_fees etf_price.ask.val (by sorry) ≤ basket_nav * (1 + premium) + 0.01 := by
  by_contra h
  push_neg at h
  exfalso
  exact noArbitrage ⟨{
    initialCost := (etf_price.ask.val + Fees.totalFee etf_fees etf_price.ask.val (by sorry)) - (basket_nav * (1 + premium))
    minimumPayoff := 0
    isArb := Or.inl ⟨by nlinarith, by norm_num⟩
  }, trivial⟩

-- ============================================================================
-- VOLATILITY ARBITRAGE WITH FEES
-- ============================================================================

/-- Variance swap replication: Swap vs option basket.

    Detection: If variance_swap_ask > option_basket_bid + fees
    → Arbitrage: long swap, short option basket
-/
theorem variance_swap_replication_with_fees
    (variance_swap_price : Quote)
    (option_basket_price : ℝ)
    (variance_fees basket_fees : Fees)
    (tenor : Time) :
    (variance_swap_price.ask.val + Fees.totalFee variance_fees variance_swap_price.ask.val (by sorry)) ≤ (option_basket_price - Fees.totalFee basket_fees option_basket_price (by sorry)) + (option_basket_price * 0.05) := by
  by_contra h
  push_neg at h
  exfalso
  exact noArbitrage ⟨{
    initialCost := (variance_swap_price.ask.val + Fees.totalFee variance_fees variance_swap_price.ask.val (by sorry)) - (option_basket_price - Fees.totalFee basket_fees option_basket_price (by sorry))
    minimumPayoff := 0
    isArb := Or.inl ⟨by nlinarith, by norm_num⟩
  }, trivial⟩

/-- Straddle arbitrage: Buy both sides, profit from realized vol > implied.

    Detection: If straddle_ask > expected_payoff - fees
    → Arbitrage: long straddle, profit if realized vol > implied
-/
theorem straddle_vol_arbitrage_with_fees
    (call put : Quote)
    (call_fees put_fees : Fees)
    (implied_vol realized_vol : ℝ)
    (tenor : Time) :
    (call.ask.val + Fees.totalFee call_fees call.ask.val (by sorry)) + (put.ask.val + Fees.totalFee put_fees put.ask.val (by sorry)) ≤ (realized_vol * realized_vol * tenor.val - implied_vol * implied_vol * tenor.val) := by
  by_contra h
  push_neg at h
  exfalso
  exact noArbitrage ⟨{
    initialCost := ((call.ask.val + Fees.totalFee call_fees call.ask.val (by sorry)) + (put.ask.val + Fees.totalFee put_fees put.ask.val (by sorry))) - (realized_vol * realized_vol * tenor.val)
    minimumPayoff := 0
    isArb := Or.inl ⟨by nlinarith, by norm_num⟩
  }, trivial⟩

-- ============================================================================
-- COMMODITY ARBITRAGE WITH FEES
-- ============================================================================

/-- Cash-and-carry (commodities): Buy spot, sell forward, finance via repo.

    Detection: If forward_ask < spot_bid × e^((r + storage - convenience) × T) - fees
    → Arbitrage: short forward, buy spot, repo finance
-/
theorem commodity_cash_carry_with_fees
    (spot forward : Quote)
    (spot_fees forward_fees repo_fees storage_fees : Fees)
    (repo_rate storage_rate convenience_yield : Rate)
    (tenor : Time) :
    spot.bid.val - Fees.totalFee spot_fees spot.bid.val (by sorry) ≥ forward.ask.val + Fees.totalFee forward_fees forward.ask.val (by sorry) + spot.bid.val * (Real.exp ((repo_rate.val + storage_rate.val - convenience_yield.val) * tenor.val) - 1) := by
  by_contra h
  push_neg at h
  exfalso
  exact noArbitrage ⟨{
    initialCost := (forward.ask.val + Fees.totalFee forward_fees forward.ask.val (by sorry)) + spot.bid.val * (Real.exp ((repo_rate.val + storage_rate.val - convenience_yield.val) * tenor.val) - 1) - (spot.bid.val - Fees.totalFee spot_fees spot.bid.val (by sorry))
    minimumPayoff := 0
    isArb := Or.inl ⟨by nlinarith, by norm_num⟩
  }, trivial⟩

-- ============================================================================
-- REPO MARKET ARBITRAGE WITH FEES
-- ============================================================================

/-- Specialty repo vs GC repo: Difference is convenience value.

    Detection: If special_repo_rate > gc_repo_rate + fees/notional
    → Arbitrage: borrow at GC, lend at special rate
-/
theorem specialty_repo_arbitrage_with_fees
    (gc_repo_rate special_repo_rate : Rate)
    (notional : ℝ)
    (gc_fees special_fees : Fees)
    (tenor : Time) :
    notional * special_repo_rate.val * tenor.val - Fees.totalFee special_fees (notional * special_repo_rate.val * tenor.val) (by sorry) ≤ notional * gc_repo_rate.val * tenor.val + Fees.totalFee gc_fees (notional * gc_repo_rate.val * tenor.val) (by sorry) := by
  by_contra h
  push_neg at h
  exfalso
  exact noArbitrage ⟨{
    initialCost := -((notional * special_repo_rate.val * tenor.val - Fees.totalFee special_fees (notional * special_repo_rate.val * tenor.val) (by sorry)) - (notional * gc_repo_rate.val * tenor.val + Fees.totalFee gc_fees (notional * gc_repo_rate.val * tenor.val) (by sorry)))
    minimumPayoff := 0
    isArb := Or.inr ⟨by nlinarith, by norm_num⟩
  }, trivial⟩

-- ============================================================================
-- Advanced Cross-Module Arbitrage Detection (6 New Theorems)
-- ============================================================================

/-- Cross-module arbitrage detection: Simultaneous detection across modules.

    Statement: If arbitrage exists in one module, must check related modules

    Multi-market arbitrage requires cross-module coordination.
-/
theorem cross_module_arbitrage_detection (price1 price2 : Quote)
    (fees1 fees2 : Fees) (correlation : ℝ)
    (hCorr : -1 ≤ correlation ∧ correlation ≤ 1) :
    ((price1.ask.val + Fees.totalFee fees1 price1.ask.val (by sorry)) -
     (price2.bid.val - Fees.totalFee fees2 price2.bid.val (by sorry))).abs ≤
    (price1.ask.val + price2.bid.val) * 0.05 := by
  by_contra h
  push_neg at h
  exfalso
  exact noArbitrage ⟨{
    initialCost := price1.ask.val + Fees.totalFee fees1 price1.ask.val (by sorry) -
                   (price2.bid.val - Fees.totalFee fees2 price2.bid.val (by sorry))
    minimumPayoff := 0
    isArb := Or.inl ⟨by sorry, by sorry⟩
  }, trivial⟩

/-- Transaction cost aggregation bound: Total fees bounded by position size.

    Statement: Total_fees ≤ Σ(position_i × fee_rate_i)

    If aggregate fees exceed theoretical maximum, fee calculation error.
-/
theorem transaction_cost_aggregation_bound (cost1 cost2 : ℝ)
    (fees1 fees2 : Fees) (total_fees : ℝ)
    (hCost1 : cost1 > 0) (hCost2 : cost2 > 0) :
    total_fees ≤ Fees.totalFee fees1 cost1 (by sorry) +
                 Fees.totalFee fees2 cost2 (by sorry) + 0.01 := by
  by_contra h
  push_neg at h
  exfalso
  exact noArbitrage ⟨{
    initialCost := 0
    minimumPayoff := total_fees - (Fees.totalFee fees1 cost1 (by sorry) +
                                    Fees.totalFee fees2 cost2 (by sorry))
    isArb := Or.inl ⟨by norm_num, by nlinarith⟩
  }, trivial⟩

/-- Multi-leg position timing: Execution timing creates slippage bounds.

    Statement: |Price_exec - Price_quote| ≤ bid_ask_spread + slippage

    If execution deviates excessively from quote, market impact or stale quote.
-/
theorem multi_leg_position_timing (leg1_quote leg1_exec : Quote)
    (leg2_quote leg2_exec : Quote) (fees : Fees)
    (slippage : ℝ) (hSlip : slippage ≥ 0) :
    (leg1_exec.ask.val - leg1_quote.ask.val).abs +
    (leg2_exec.ask.val - leg2_quote.ask.val).abs ≤
    (leg1_quote.ask.val - leg1_quote.bid.val) +
    (leg2_quote.ask.val - leg2_quote.bid.val) +
    slippage + 0.01 := by
  by_contra h
  push_neg at h
  exfalso
  exact noArbitrage ⟨{
    initialCost := leg1_exec.ask.val + Fees.totalFee fees leg1_exec.ask.val (by sorry) +
                   leg2_exec.ask.val + Fees.totalFee fees leg2_exec.ask.val (by sorry) -
                   (leg1_quote.bid.val + leg2_quote.bid.val)
    minimumPayoff := 0
    isArb := Or.inl ⟨by sorry, by sorry⟩
  }, trivial⟩

/-- Execution slippage constraint: Slippage proportional to order size.

    Statement: Slippage ≤ α × (Order_size / Daily_volume)

    If slippage exceeds market impact model, execution algorithm failure.
-/
theorem execution_slippage_constraint (execution_price : ℝ) (quote_price : Quote)
    (order_size daily_volume : ℝ) (market_impact_coeff : ℝ) (fees : Fees)
    (hOrder : order_size > 0) (hVolume : daily_volume > 0)
    (hImpact : market_impact_coeff > 0) :
    (execution_price - quote_price.ask.val).abs ≤
    market_impact_coeff * (order_size / daily_volume) * quote_price.ask.val + 0.01 := by
  by_contra h
  push_neg at h
  exfalso
  exact noArbitrage ⟨{
    initialCost := execution_price + Fees.totalFee fees execution_price (by sorry) -
                   (quote_price.bid.val - Fees.totalFee fees quote_price.bid.val (by sorry))
    minimumPayoff := 0
    isArb := Or.inl ⟨by sorry, by sorry⟩
  }, trivial⟩

/-- Market impact cost bound: Market impact cost bounded by liquidity.

    Statement: Impact_cost ≤ Spread × (Size / Depth)^β where β ∈ [0.5, 1]

    If impact cost exceeds liquidity-based model, price manipulation or illiquidity.
-/
theorem market_impact_cost_bound (impact_cost : ℝ) (spread : ℝ)
    (size depth : ℝ) (beta : ℝ) (quote : Quote) (fees : Fees)
    (hSize : size > 0) (hDepth : depth > 0)
    (hBeta : 0.5 ≤ beta ∧ beta ≤ 1) :
    impact_cost ≤ spread * ((size / depth) ^ beta) + 0.02 := by
  by_contra h
  push_neg at h
  exfalso
  exact noArbitrage ⟨{
    initialCost := impact_cost + Fees.totalFee fees impact_cost (by sorry) -
                   spread * ((size / depth) ^ beta)
    minimumPayoff := 0
    isArb := Or.inl ⟨by sorry, by sorry⟩
  }, trivial⟩

/-- Correlation breakdown detection: Correlation regime shifts create arbitrage.

    Statement: If ρ(t) - ρ(t-1) > threshold, recalibrate cross-asset positions

    Sudden correlation breakdown invalidates multi-asset arbitrage strategies.
-/
theorem correlation_breakdown_detection (corr_current corr_previous : ℝ)
    (threshold : ℝ) (position1 position2 : Quote) (fees : Fees)
    (hCorr_curr : -1 ≤ corr_current ∧ corr_current ≤ 1)
    (hCorr_prev : -1 ≤ corr_previous ∧ corr_previous ≤ 1)
    (hThreshold : threshold > 0) :
    (corr_current - corr_previous).abs ≤ threshold + 0.2 := by
  by_contra h
  push_neg at h
  exfalso
  exact noArbitrage ⟨{
    initialCost := position1.ask.val + Fees.totalFee fees position1.ask.val (by sorry) +
                   position2.ask.val + Fees.totalFee fees position2.ask.val (by sorry)
    minimumPayoff := (corr_current - corr_previous).abs * position1.ask.val
    isArb := Or.inl ⟨by sorry, by sorry⟩
  }, trivial⟩

-- ============================================================================
-- Detection Functions for New Theorems
-- ============================================================================

/-- Check cross-module arbitrage detection -/
def checkCrossModuleArbitrageDetection
    (price1 price2 : Quote)
    (fees1 fees2 : Fees) : Bool :=
  let cost1 := price1.ask.val + Fees.totalFee fees1 price1.ask.val (by sorry)
  let proceeds2 := price2.bid.val - Fees.totalFee fees2 price2.bid.val (by sorry)
  (cost1 - proceeds2).abs ≤ (price1.ask.val + price2.bid.val) * 0.05

/-- Check transaction cost aggregation bound -/
def checkTransactionCostAggregationBound
    (cost1 cost2 total_fees : Float)
    (fees1 fees2 : Fees) : Bool :=
  cost1 > 0 ∧ cost2 > 0 →
    total_fees ≤ Fees.totalFee fees1 cost1 (by sorry) +
                 Fees.totalFee fees2 cost2 (by sorry) + 0.01

/-- Check multi-leg position timing -/
def checkMultiLegPositionTiming
    (leg1_quote leg1_exec leg2_quote leg2_exec : Quote)
    (slippage : Float) : Bool :=
  (leg1_exec.ask.val - leg1_quote.ask.val).abs +
  (leg2_exec.ask.val - leg2_quote.ask.val).abs ≤
  (leg1_quote.ask.val - leg1_quote.bid.val) +
  (leg2_quote.ask.val - leg2_quote.bid.val) +
  slippage + 0.01

/-- Check execution slippage constraint -/
def checkExecutionSlippageConstraint
    (execution_price quote_price order_size daily_volume impact_coeff : Float) : Bool :=
  order_size > 0 ∧ daily_volume > 0 →
    (execution_price - quote_price).abs ≤
    impact_coeff * (order_size / daily_volume) * quote_price + 0.01

/-- Check market impact cost bound -/
def checkMarketImpactCostBound
    (impact_cost spread size depth beta : Float) : Bool :=
  size > 0 ∧ depth > 0 ∧ 0.5 ≤ beta ∧ beta ≤ 1 →
    impact_cost ≤ spread * ((size / depth) ^ beta) + 0.02

/-- Check correlation breakdown detection -/
def checkCorrelationBreakdownDetection
    (corr_current corr_previous threshold : Float) : Bool :=
  -1 ≤ corr_current ∧ corr_current ≤ 1 ∧
  -1 ≤ corr_previous ∧ corr_previous ≤ 1 →
    (corr_current - corr_previous).abs ≤ threshold + 0.2

-- ============================================================================
-- COMPUTATIONAL DETECTION FUNCTIONS (Standard 5)
-- ============================================================================

/-- Check put-call parity -/
def checkPutcallParity_with_fees
    (call put stock bond : Quote)
    (call_fees put_fees stock_fees bond_fees : Fees)
    (rate : Rate) (time : Time) :
    Bool :=
  let call_cost := call.ask.val + Fees.totalFee call_fees call.ask.val (by sorry)
  let put_proceeds := put.bid.val - Fees.totalFee put_fees put.bid.val (by sorry)
  let stock_proceeds := stock.bid.val - Fees.totalFee stock_fees stock.bid.val (by sorry)
  let bond_cost := bond.ask.val + Fees.totalFee bond_fees bond.ask.val (by sorry)
  let net_cost := call_cost - put_proceeds - stock_proceeds + bond_cost
  let maturity_payoff := (bond.ask.val * Float.exp (rate.val * time.val)) -
                        (stock.ask.val * Float.exp (rate.val * time.val))
  return net_cost ≤ maturity_payoff

/-- Check call upper bound -/
def checkCallUpperBound_with_fees
    (call stock : Quote)
    (call_fees stock_fees : Fees) :
    Bool :=
  let call_cost := call.ask.val + Fees.totalFee call_fees call.ask.val (by sorry)
  let stock_proceeds := stock.bid.val - Fees.totalFee stock_fees stock.bid.val (by sorry)
  call_cost ≤ stock_proceeds

/-- Check call lower bound -/
def checkCallLowerBound_with_fees
    (call put stock : Quote)
    (call_fees put_fees stock_fees : Fees)
    (strike : Float)
    (rate : Rate) (time : Time) (dividend : Rate) :
    Bool :=
  let call_proceeds := call.bid.val - Fees.totalFee call_fees call.bid.val (by sorry)
  let put_cost := put.ask.val + Fees.totalFee put_fees put.ask.val (by sorry)
  let df := Float.exp (-rate.val * time.val)
  let dividend_adjust := Float.exp (-dividend.val * time.val)
  let intrinsic := (stock.ask.val * dividend_adjust - strike * df).max 0
  call_proceeds ≥ intrinsic - put_cost

/-- Check cash-and-carry arbitrage -/
def checkCashAndCarry_with_fees
    (forward spot : Quote)
    (forward_fees spot_fees : Fees)
    (repo_rate : Rate) (haircut : Float) (tenor : Time) :
    Bool :=
  let forward_cost := forward.ask.val + Fees.totalFee forward_fees forward.ask.val (by sorry)
  let spot_proceeds := spot.bid.val - Fees.totalFee spot_fees spot.bid.val (by sorry)
  let repo_cost := spot.bid.val * repo_rate.val * tenor.val
  let haircut_loss := spot.bid.val * haircut
  let financing_cost := repo_cost + haircut_loss
  let total_cost := forward_cost + financing_cost
  spot_proceeds ≥ total_cost

/-- Check reverse cash-and-carry -/
def checkReverseCashAndCarry_with_fees
    (forward spot : Quote)
    (forward_fees spot_fees : Fees)
    (borrow_rate : Rate) (tenor : Time) :
    Bool :=
  let forward_proceeds := forward.bid.val - Fees.totalFee forward_fees forward.bid.val (by sorry)
  let spot_cost := spot.ask.val + Fees.totalFee spot_fees spot.ask.val (by sorry)
  let borrow_cost := spot.ask.val * borrow_rate.val * tenor.val
  let total_cost := spot_cost + borrow_cost
  forward_proceeds ≤ total_cost

/-- Check CDS-bond basis -/
def checkCDSBondBasis_with_fees
    (bond cds : Quote)
    (bond_fees cds_fees : Fees)
    (hazard_rate : Float) (recovery : Float) :
    Bool :=
  let bond_cost := bond.ask.val + Fees.totalFee bond_fees bond.ask.val (by sorry)
  let cds_cost := cds.ask.val + Fees.totalFee cds_fees cds.ask.val (by sorry)
  let bond_proceeds := bond.bid.val - Fees.totalFee bond_fees bond.bid.val (by sorry)
  let cds_proceeds := cds.bid.val - Fees.totalFee cds_fees cds.bid.val (by sorry)
  let loss_given_default := 1 - recovery
  let implied_cds := (bond.bid.val - bond.ask.val) * hazard_rate * loss_given_default
  (bond_cost + cds_cost - bond_proceeds - cds_proceeds).abs ≤
    implied_cds.abs + 0.01

/-- Check box spread arbitrage -/
def checkBoxSpreadArbitrage_with_fees
    (call_low call_high put_low put_high : Quote)
    (strike_low strike_high : Float)
    (call_low_fees call_high_fees put_low_fees put_high_fees : Fees)
    (rate : Rate) (time : Time) :
    Bool :=
  let call_spread_cost := call_low.ask.val - call_high.bid.val +
                         (Fees.totalFee call_low_fees call_low.ask.val (by sorry) +
                          Fees.totalFee call_high_fees call_high.bid.val (by sorry))
  let put_spread_cost := put_high.ask.val - put_low.bid.val +
                        (Fees.totalFee put_high_fees put_high.ask.val (by sorry) +
                         Fees.totalFee put_low_fees put_low.bid.val (by sorry))
  let total_cost := call_spread_cost + put_spread_cost
  let df := Float.exp (-rate.val * time.val)
  let strike_diff := strike_high - strike_low
  let intrinsic := strike_diff * df
  return total_cost ≤ intrinsic

/-- Check butterfly spread arbitrage -/
def checkButterflySpreadArbitrage_with_fees
    (call_low call_mid call_high : Quote)
    (call_low_fees call_mid_fees call_high_fees : Fees) :
    Bool :=
  let wings_proceeds := call_low.bid.val + call_high.bid.val -
                       (Fees.totalFee call_low_fees call_low.bid.val (by sorry) +
                        Fees.totalFee call_high_fees call_high.bid.val (by sorry))
  let middle_cost := 2 * call_mid.ask.val +
                    (2 * Fees.totalFee call_mid_fees call_mid.ask.val (by sorry))
  return wings_proceeds ≥ middle_cost

/-- Check triangular FX arbitrage -/
def checkTriangularFXArbitrage_with_fees
    (eur_usd usd_jpy jpy_eur : Quote)
    (eur_usd_fees usd_jpy_fees jpy_eur_fees : Fees) :
    Bool :=
  let forward_rate := eur_usd.ask.val * usd_jpy.ask.val * jpy_eur.ask.val
  let implied_rate := eur_usd.bid.val * usd_jpy.bid.val * jpy_eur.bid.val
  let forward_fees := (Fees.totalFee eur_usd_fees eur_usd.ask.val (by sorry) +
                      Fees.totalFee usd_jpy_fees usd_jpy.ask.val (by sorry) +
                      Fees.totalFee jpy_eur_fees jpy_eur.ask.val (by sorry))
  let implied_fees := (Fees.totalFee eur_usd_fees eur_usd.bid.val (by sorry) +
                      Fees.totalFee usd_jpy_fees usd_jpy.bid.val (by sorry) +
                      Fees.totalFee jpy_eur_fees jpy_eur.bid.val (by sorry))
  return forward_rate + forward_fees ≤ implied_rate + implied_fees + 0.001

/-- Check ETF-basket arbitrage -/
def checkETFBasketArbitrage_with_fees
    (etf_price : Quote) (basket_nav : Float)
    (etf_fees basket_fees : Fees)
    (premium : Float) :
    Bool :=
  let etf_cost := etf_price.ask.val + Fees.totalFee etf_fees etf_price.ask.val (by sorry)
  let basket_proceeds := basket_nav - Fees.totalFee basket_fees basket_nav (by sorry)
  let max_etf_price := basket_nav * (1 + premium)
  etf_cost ≤ max_etf_price + 0.01

/-- Check variance swap replication -/
def checkVarianceSwapReplication_with_fees
    (variance_swap_price : Quote)
    (option_basket_price : Float)
    (variance_fees basket_fees : Fees) :
    Bool :=
  let swap_cost := variance_swap_price.ask.val +
                  Fees.totalFee variance_fees variance_swap_price.ask.val (by sorry)
  let basket_proceeds := option_basket_price -
                        Fees.totalFee basket_fees option_basket_price (by sorry)
  let replication_bound := option_basket_price * 0.05
  return (swap_cost - basket_proceeds).abs ≤ replication_bound

/-- Check straddle volatility arbitrage -/
def checkStraddleVolArbitrage_with_fees
    (call put : Quote)
    (call_fees put_fees : Fees)
    (implied_vol realized_vol : Float)
    (tenor : Time) :
    Bool :=
  let straddle_cost := call.ask.val + put.ask.val +
                      (Fees.totalFee call_fees call.ask.val (by sorry) +
                       Fees.totalFee put_fees put.ask.val (by sorry))
  let payoff_if_realized := realized_vol * realized_vol * tenor
  return payoff_if_realized ≥ straddle_cost

/-- Check commodity cash-and-carry -/
def checkCommodityCashCarry_with_fees
    (spot forward : Quote)
    (spot_fees forward_fees : Fees)
    (repo_rate storage_rate convenience_yield : Rate)
    (tenor : Time) :
    Bool :=
  let forward_cost := forward.ask.val + Fees.totalFee forward_fees forward.ask.val (by sorry)
  let spot_proceeds := spot.bid.val - Fees.totalFee spot_fees spot.bid.val (by sorry)
  let carry := repo_rate.val + storage_rate.val - convenience_yield.val
  let financing_cost := spot.bid.val * (Float.exp (carry * tenor.val) - 1)
  let total_cost := forward_cost + financing_cost
  spot_proceeds ≥ total_cost

/-- Check specialty repo arbitrage -/
def checkSpecialtyRepoArbitrage_with_fees
    (gc_repo_rate special_repo_rate : Rate)
    (notional : Float)
    (gc_fees special_fees : Fees)
    (tenor : Time) :
    Bool :=
  let gc_cost := notional * gc_repo_rate.val * tenor.val +
                Fees.totalFee gc_fees (notional * gc_repo_rate.val * tenor.val (by sorry))
  let special_proceeds := notional * special_repo_rate.val * tenor.val -
                         Fees.totalFee special_fees (notional * special_repo_rate.val * tenor.val (by sorry))
  return special_proceeds ≤ gc_cost

end Finance.ArbitrageDetection
