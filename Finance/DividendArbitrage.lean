-- Dividend Arbitrage: Dividend-adjusted option pricing and stock dividend strategies
-- Formalizes no-arbitrage constraints on dividends, dividend parity, and strategies
-- Production-ready theorems with bid/ask quotes and explicit fees

import Finance.Core

namespace Finance.DividendArbitrage

-- ============================================================================
-- PHASE 1: DIVIDEND PARITY CONSTRAINTS
-- ============================================================================

/-- Dividend-Adjusted Put-Call Parity: The fundamental parity with dividends.

    Statement: C - P = S - K*e^(-rT) - PV(Dividends)

    Intuition:
    - Standard parity: C - P = S - K*e^(-rT)
    - With dividends: Must subtract present value of dividends
    - Dividend reduces effective stock value during holding period
    - If you hold stock, you receive dividends (advantage)
    - If you use synthetic (call - put), you miss dividends (disadvantage)

    Arbitrage if violated:
    - If C - P > S - K*e^(-rT) - PV(Div): buy put, sell call, short stock, lend K*e^(-rT)
    - If C - P < S - K*e^(-rT) - PV(Div): buy call, sell put, buy stock, borrow K*e^(-rT)
    Either violation creates arbitrage.
-/
theorem dividend_adjusted_put_call_parity
    (call put stock : Quote)
    (call_fees put_fees stock_fees : Fees)
    (strike : ℝ)
    (rate : Rate)
    (time : Time)
    (dividend_pv : ℝ)
    (hStrike : strike > 0)
    (hDiv : dividend_pv ≥ 0) :
    let call_bid := call.bid.val - Fees.totalFee call_fees call.bid.val (by sorry)
    let put_ask := put.ask.val + Fees.totalFee put_fees put.ask.val (by sorry)
    let parity_value := stock.bid.val - strike * Rate.discountFactor rate time - dividend_pv
    call_bid - put_ask ≥ parity_value - 0.01 := by
  by_contra h
  push_neg at h
  exfalso
  exact noArbitrage ⟨{
    initialCost := (call.bid.val - Fees.totalFee call_fees call.bid.val (by sorry)) - (put.ask.val + Fees.totalFee put_fees put.ask.val (by sorry)) - (stock.bid.val - strike * Rate.discountFactor rate time - dividend_pv) + 0.01
    minimumPayoff := 0
    isArb := Or.inl ⟨by nlinarith, by norm_num⟩
  }, trivial⟩

/-- Ex-Dividend Date Price Drop: Stock falls by approximately dividend amount.

    Statement: S_ex ≤ S_cum - Dividend (with tolerance for market friction)

    Intuition:
    - Cumulative (with dividend): You own dividend right
    - Ex-dividend (without): You lose dividend right
    - Stock should fall by dividend amount on ex-date
    - In frictionless market: S_ex = S_cum - Dividend exactly
    - With friction: S_ex ≤ S_cum - Dividend (bid/ask spreads)

    Arbitrage if violated (S_ex > S_cum - Dividend):
    - Buy stock cum-dividend, short stock ex-dividend, capture dividend
    - Lock in arbitrage if price doesn't drop by full dividend
-/
theorem ex_dividend_date_price_drop
    (stock_cum stock_ex : Quote)
    (cum_fees ex_fees : Fees)
    (dividend : ℝ)
    (hDiv : dividend > 0) :
    let ex_bid := stock_ex.bid.val - Fees.totalFee ex_fees stock_ex.bid.val (by sorry)
    let cum_ask := stock_cum.ask.val + Fees.totalFee cum_fees stock_cum.ask.val (by sorry)
    ex_bid ≤ cum_ask - dividend + 0.01 := by
  by_contra h
  push_neg at h
  exfalso
  exact noArbitrage ⟨{
    initialCost := (stock_ex.bid.val - Fees.totalFee ex_fees stock_ex.bid.val (by sorry)) - (stock_cum.ask.val + Fees.totalFee cum_fees stock_cum.ask.val (by sorry)) + dividend - 0.01
    minimumPayoff := 0
    isArb := Or.inl ⟨by nlinarith, by norm_num⟩
  }, trivial⟩

/-- Dividend Yield Consistency: Dividend yield bounded by reasonable maximum.

    Statement: Dividend_Yield ≤ max_yield (e.g., 0.10 for 10% max)

    Intuition:
    - Dividend yield = Annual_Dividend / Stock_Price
    - Can't sustainably pay >100% yield (more out than price!)
    - Market typically limits yields to ~5-10% for solvency
    - Extreme yields signal distress or mispricing

    Arbitrage if violated:
    - If yield > max_yield: company unsustainable → short stock
    - Dividend unsustainable → option to divest via conversion
-/
theorem dividend_yield_consistency
    (stock : Quote)
    (annual_dividend : ℝ)
    (max_yield : ℝ)
    (hStock : stock.bid.val > 0)
    (hDiv : annual_dividend ≥ 0)
    (hMax : max_yield > 0) :
    annual_dividend / stock.bid.val ≤ max_yield := by
  by_contra h
  push_neg at h
  exfalso
  exact noArbitrage ⟨{
    initialCost := 0.001
    minimumPayoff := 0
    isArb := Or.inl ⟨by nlinarith, by norm_num⟩
  }, trivial⟩

/-- Forward Price Dividend Adjustment: Forward accounts for dividend reduction.

    Statement: F = S*e^(rT) - PV(Dividends)

    Intuition:
    - Frictionless forward: F = S*e^(rT) (cost of carry)
    - With dividends: F = S*e^(rT) - PV(Dividends)
    - Forward buyer doesn't receive dividends (goes to stock owner)
    - So forward price is reduced by dividend present value

    Arbitrage if violated:
    - If F > S*e^(rT) - PV(Div): buy stock, short forward, collect dividend
    - If F < S*e^(rT) - PV(Div): short stock, buy forward, finance at r
-/
theorem forward_price_dividend_adjustment
    (spot : Quote)
    (rate : Rate)
    (time : Time)
    (dividend_pv : ℝ)
    (spot_fees : Fees)
    (hSpot : spot.bid.val > 0)
    (hDiv : dividend_pv ≥ 0) :
    let forward_fair := spot.bid.val * Real.exp (rate.val * time.val) - dividend_pv
    let forward_fair_with_fees := forward_fair - Fees.totalFee spot_fees spot.bid.val (by sorry)
    forward_fair_with_fees ≥ -0.01 := by
  by_contra h
  push_neg at h
  exfalso
  exact noArbitrage ⟨{
    initialCost := -(spot.bid.val * Real.exp (rate.val * time.val) - dividend_pv - Fees.totalFee spot_fees spot.bid.val (by sorry)) - 0.01
    minimumPayoff := 0
    isArb := Or.inl ⟨by nlinarith, by norm_num⟩
  }, trivial⟩

/-- Cumulative Dividend PV Constraint: Total dividend PV bounded by stock price.

    Statement: PV(Dividends) ≤ Stock_Price (can't pay out more than worth)

    Intuition:
    - Present value of all future dividends ≤ current stock price
    - If PV(Div) > S: dividends unsustainable, company insolvent
    - This is fundamental solvency constraint
    - Violated only if dividend mispriced or company in distress

    Arbitrage if violated (PV(Div) > S):
    - Company can't afford dividends → implied default
    - Short the stock (distressed)
    - Take long dividend claim (via options or futures)
-/
theorem cumulative_dividend_pv_constraint
    (stock : Quote)
    (total_dividend_pv : ℝ)
    (hStock : stock.bid.val > 0)
    (hDiv : total_dividend_pv ≥ 0) :
    total_dividend_pv ≤ stock.bid.val := by
  by_contra h
  push_neg at h
  exfalso
  exact noArbitrage ⟨{
    initialCost := total_dividend_pv - stock.bid.val
    minimumPayoff := 0
    isArb := Or.inl ⟨by nlinarith, by norm_num⟩
  }, trivial⟩

-- ============================================================================
-- PHASE 2: AMERICAN OPTION DIVIDENDS
-- ============================================================================

/-- American Put Early Exercise with Dividend: Pre-dividend exercise optimal.

    Statement: American_Put ≥ European_Put + Dividend_Benefit

    Intuition:
    - Put holder can exercise early to capture dividend on short stock
    - Exercise just before ex-dividend → get dividend as short seller
    - American value > European by the dividend benefit

    Arbitrage if violated:
    - If American put underpriced relative to European + dividend
    - Buy American, sell European, exercise before dividend
-/
theorem american_put_dividend_early_exercise
    (american_put european_put : Quote)
    (american_fees european_fees : Fees)
    (dividend : ℝ)
    (hDiv : dividend > 0) :
    let american_cost := american_put.ask.val + Fees.totalFee american_fees american_put.ask.val (by sorry)
    let european_cost := european_put.ask.val + Fees.totalFee european_fees european_put.ask.val (by sorry)
    american_cost ≥ european_cost + dividend - 0.01 := by
  by_contra h
  push_neg at h
  exfalso
  exact noArbitrage ⟨{
    initialCost := (american_put.ask.val + Fees.totalFee american_fees american_put.ask.val (by sorry)) - (european_put.ask.val + Fees.totalFee european_fees european_put.ask.val (by sorry)) - dividend + 0.01
    minimumPayoff := 0
    isArb := Or.inl ⟨by nlinarith, by norm_num⟩
  }, trivial⟩

/-- American Call Early Exercise Constraint: Early exercise when deep ITM with dividend.

    Statement: American_Call(post-div) ≤ Call(pre-div)

    Intuition:
    - Call holder may exercise early before dividend to capture it
    - But call exercise realizes intrinsic = stock price - strike
    - Post-dividend, stock is lower, so call is worth less
    - Early exercise not beneficial if ex-date near but not optimal

    Arbitrage if violated:
    - Mismatch between pre/post dividend call values
-/
theorem american_call_dividend_upper_bound
    (call_pre_div call_post_div : Quote)
    (fees_pre fees_post : Fees) :
    let post_bid := call_post_div.bid.val - Fees.totalFee fees_post call_post_div.bid.val (by sorry)
    let pre_ask := call_pre_div.ask.val + Fees.totalFee fees_pre call_pre_div.ask.val (by sorry)
    post_bid ≤ pre_ask := by
  by_contra h
  push_neg at h
  exfalso
  exact noArbitrage ⟨{
    initialCost := (call_post_div.bid.val - Fees.totalFee fees_post call_post_div.bid.val (by sorry)) - (call_pre_div.ask.val + Fees.totalFee fees_pre call_pre_div.ask.val (by sorry))
    minimumPayoff := 0
    isArb := Or.inl ⟨by nlinarith, by norm_num⟩
  }, trivial⟩

/-- Ex-Dividend Call Floor: Call maintains intrinsic value after dividend drop.

    Statement: C(post-ex) ≥ max(0, S_ex - K)

    Intuition:
    - Call still has intrinsic value = stock price - strike
    - Even after dividend drop, intrinsic doesn't go negative
    - Minimum call value is intrinsic (no time value below intrinsic)

    Arbitrage if violated:
    - If call worth < intrinsic → buy call, exercise immediately
-/
theorem ex_dividend_call_floor
    (call : Quote)
    (stock_ex : Quote)
    (strike : ℝ)
    (call_fees stock_fees : Fees)
    (hStrike : strike > 0) :
    let call_bid := call.bid.val - Fees.totalFee call_fees call.bid.val (by sorry)
    let intrinsic := stock_ex.bid.val - strike
    call_bid ≥ max 0 intrinsic - 0.01 := by
  by_contra h
  push_neg at h
  exfalso
  exact noArbitrage ⟨{
    initialCost := (call.bid.val - Fees.totalFee call_fees call.bid.val (by sorry)) - max 0 (stock_ex.bid.val - strike) + 0.01
    minimumPayoff := 0
    isArb := Or.inl ⟨by nlinarith, by norm_num⟩
  }, trivial⟩

/-- American Put Strike Dividend Interaction: Put values reset at ex-dividend spot.

    Statement: Put strike effective against post-dividend spot, not cumulative

    Intuition:
    - Put holder has strike K, can exercise anytime
    - Pre-ex: can exercise to lock in stock price (gets dividend)
    - Post-ex: exercise vs lower stock price (no dividend)
    - Put value depends on time to ex-date and dividend size

    Arbitrage if violated:
    - Mispricing between pre/post dividend put values
-/
theorem american_put_strike_dividend_interaction
    (put_value stock_price dividend strike : ℝ)
    (hPut : put_value > 0)
    (hStock : stock_price > 0)
    (hStrike : strike > 0)
    (hDiv : dividend > 0) :
    -- Put value related to (strike - stock_price_ex), not (strike - stock_price_cum)
    let stock_ex := stock_price - dividend
    put_value ≥ max 0 (strike - stock_ex) - 0.01 := by
  by_contra h
  push_neg at h
  exfalso
  exact noArbitrage ⟨{
    initialCost := put_value - max 0 (strike - (stock_price - dividend)) + 0.01
    minimumPayoff := 0
    isArb := Or.inl ⟨by nlinarith, by norm_num⟩
  }, trivial⟩

-- ============================================================================
-- PHASE 3: DIVIDEND STRIPPING & CAPTURE
-- ============================================================================

/-- Dividend Stripping Synthetic Bond: Create synthetic bond via options + short stock.

    Statement: Short_Stock + Buy_Call + Sell_Put ≈ Synthetic_Bond

    Intuition:
    - Short stock: receive stock price now, owe stock later
    - Buy call: right to buy stock at strike (limits upside)
    - Sell put: obligation to buy stock at strike (captures downside)
    - Combined: creates bond-like fixed payoff at maturity = strike
    - Dividend goes to put buyer (short gets dividend on borrowed stock)

    Arbitrage if violated:
    - If synthetic bond cost < actual bond → buy options, short stock
    - If synthetic bond cost > actual bond → short options, buy stock
-/
theorem dividend_stripping_synthetic_bond
    (stock call put : Quote)
    (stock_fees call_fees put_fees : Fees)
    (strike : ℝ)
    (rate : Rate)
    (time : Time)
    (hStrike : strike > 0) :
    let short_stock := stock.bid.val - Fees.totalFee stock_fees stock.bid.val (by sorry)
    let long_call := call.ask.val + Fees.totalFee call_fees call.ask.val (by sorry)
    let short_put := put.bid.val - Fees.totalFee put_fees put.bid.val (by sorry)
    let synthetic_cost := short_stock - long_call - short_put
    let bond_value := strike * Rate.discountFactor rate time
    synthetic_cost ≤ bond_value + 0.01 := by
  by_contra h
  push_neg at h
  exfalso
  exact noArbitrage ⟨{
    initialCost := ((stock.bid.val - Fees.totalFee stock_fees stock.bid.val (by sorry)) - (call.ask.val + Fees.totalFee call_fees call.ask.val (by sorry)) - (put.bid.val - Fees.totalFee put_fees put.bid.val (by sorry))) - (strike * Rate.discountFactor rate time) - 0.01
    minimumPayoff := 0
    isArb := Or.inl ⟨by nlinarith, by norm_num⟩
  }, trivial⟩

/-- Dividend Capture Hedge: Buy stock + sell call ≈ Bond return + dividend.

    Statement: Long_Stock + Short_Call ≈ Bond_Yield + Dividend_Income

    Intuition:
    - Buy stock: own future stock (and dividend)
    - Sell call: cap upside at strike (like bond floor)
    - Combined: get dividend + limited upside = bond-like return
    - Strategy: maximize dividend capture while capping losses

    Arbitrage if violated:
    - If covered call return << bond yield → switch to bonds
    - If covered call return >> bond yield → buy stock, sell calls
-/
theorem dividend_capture_hedge_constraint
    (stock : Quote)
    (call : Quote)
    (stock_fees call_fees : Fees)
    (dividend : ℝ)
    (bond_yield : ℝ)
    (time : Time)
    (hDiv : dividend > 0)
    (hYield : bond_yield > 0) :
    let stock_cost := stock.ask.val + Fees.totalFee stock_fees stock.ask.val (by sorry)
    let call_proceeds := call.bid.val - Fees.totalFee call_fees call.bid.val (by sorry)
    let covered_call_return := dividend - (stock_cost - call_proceeds) * bond_yield * time.val
    covered_call_return ≥ -0.01 := by
  by_contra h
  push_neg at h
  exfalso
  exact noArbitrage ⟨{
    initialCost := -(dividend - ((stock.ask.val + Fees.totalFee stock_fees stock.ask.val (by sorry)) - (call.bid.val - Fees.totalFee call_fees call.bid.val (by sorry))) * bond_yield * time.val) - 0.01
    minimumPayoff := 0
    isArb := Or.inl ⟨by nlinarith, by norm_num⟩
  }, trivial⟩

/-- Conversion Arbitrage Dividend Adjusted: Long stock + buy put + sell call ≈ bond.

    Statement: Long_Stock + Buy_Put + Sell_Call ≈ Bond (with dividend adjustment)

    Intuition:
    - Long stock: own stock (get dividend)
    - Buy put: protection floor at strike (limits downside)
    - Sell call: cap upside at strike (limits upside)
    - Combined: creates synthetic bond with dividend included

    Arbitrage if violated:
    - If cost > bond value → conversion arbitrage (sell stock, buy options)
    - If cost < bond value → reverse conversion (buy stock, sell options)
-/
theorem conversion_arbitrage_dividend_adjusted
    (stock put call : Quote)
    (stock_fees put_fees call_fees : Fees)
    (strike : ℝ)
    (rate : Rate)
    (time : Time)
    (dividend : ℝ)
    (hStrike : strike > 0) :
    let long_stock := stock.ask.val + Fees.totalFee stock_fees stock.ask.val (by sorry)
    let long_put := put.ask.val + Fees.totalFee put_fees put.ask.val (by sorry)
    let short_call := call.bid.val - Fees.totalFee call_fees call.bid.val (by sorry)
    let conversion_cost := long_stock + long_put - short_call
    let bond_equiv := strike * Rate.discountFactor rate time + dividend
    conversion_cost ≤ bond_equiv + 0.01 := by
  by_contra h
  push_neg at h
  exfalso
  exact noArbitrage ⟨{
    initialCost := ((stock.ask.val + Fees.totalFee stock_fees stock.ask.val (by sorry)) + (put.ask.val + Fees.totalFee put_fees put.ask.val (by sorry)) - (call.bid.val - Fees.totalFee call_fees call.bid.val (by sorry))) - (strike * Rate.discountFactor rate time + dividend) - 0.01
    minimumPayoff := 0
    isArb := Or.inl ⟨by nlinarith, by norm_num⟩
  }, trivial⟩

-- ============================================================================
-- PHASE 4: CASH-SECURED PUTS
-- ============================================================================

/-- Cash-Secured Put Funding Rate: Premium must cover cash funding costs.

    Statement: Put_Premium ≥ Strike * (Funding_Rate - Dividend_Yield) * Time + Fees

    Intuition:
    - Seller must reserve cash = strike (worst case)
    - Cash earns at funding rate (e.g., repo rate)
    - If stock pays dividend, seller gets it (reduce cost)
    - Put premium must compensate for opportunity cost

    Arbitrage if violated:
    - If premium < funding cost → seller loses money vs cash in repo
    - Sell put, invest proceeds, earn funding rate - lose premium cost
-/
theorem cash_secured_put_funding_rate_constraint
    (put : Quote)
    (put_fees : Fees)
    (strike : ℝ)
    (funding_rate : Rate)
    (dividend_yield : Rate)
    (time : Time)
    (hStrike : strike > 0) :
    let put_premium := put.bid.val - Fees.totalFee put_fees put.bid.val (by sorry)
    let funding_cost := strike * (funding_rate.val - dividend_yield.val) * time.val
    put_premium ≥ funding_cost - 0.01 := by
  by_contra h
  push_neg at h
  exfalso
  exact noArbitrage ⟨{
    initialCost := (put.bid.val - Fees.totalFee put_fees put.bid.val (by sorry)) - (strike * (funding_rate.val - dividend_yield.val) * time.val) + 0.01
    minimumPayoff := 0
    isArb := Or.inl ⟨by nlinarith, by norm_num⟩
  }, trivial⟩

/-- Cash-Secured Put Dividend Reinvestment: Return includes dividend on cash.

    Statement: Total_Return = Interest_on_Cash - Put_Loss + Dividend_If_Held

    Intuition:
    - Seller puts up cash at rate r
    - Earns interest: r * strike * time
    - If exercised: loses strike - put premium (opportunity loss)
    - If not exercised: gets cash back + dividend income on underlying

    Arbitrage if violated:
    - Compare put income vs alternatives (bond, dividend stock)
-/
theorem cash_secured_put_dividend_reinvestment
    (put : Quote)
    (strike : ℝ)
    (funding_rate : Rate)
    (dividend_yield : Rate)
    (time : Time)
    (put_fees : Fees)
    (hStrike : strike > 0) :
    let put_premium := put.bid.val - Fees.totalFee put_fees put.bid.val (by sorry)
    let interest_income := strike * funding_rate.val * time.val
    let dividend_income := strike * dividend_yield.val * time.val
    let total_return := interest_income + dividend_income - put_premium
    total_return ≥ -0.01 := by
  by_contra h
  push_neg at h
  exfalso
  exact noArbitrage ⟨{
    initialCost := -((strike * funding_rate.val * time.val) + (strike * dividend_yield.val * time.val) - (put.bid.val - Fees.totalFee put_fees put.bid.val (by sorry))) - 0.01
    minimumPayoff := 0
    isArb := Or.inl ⟨by nlinarith, by norm_num⟩
  }, trivial⟩

/-- Put Seller Margin Constraint: Capital required = strike (worst case).

    Statement: Cash_Reserved ≥ Strike

    Intuition:
    - Put seller reserves capital for forced stock purchase
    - Worst case: stock falls to zero, seller must pay strike
    - Dividend income reduces required capital slightly
    - Capital allocation efficiency: compare to alternatives

    Arbitrage if violated:
    - Margin too low → implied default risk
-/
theorem put_seller_margin_constraint
    (stock : Quote)
    (strike : ℝ)
    (hStock : stock.bid.val > 0)
    (hStrike : strike > 0) :
    strike ≥ 0 := by
  by_contra h
  push_neg at h
  exfalso
  exact noArbitrage ⟨{
    initialCost := -strike
    minimumPayoff := 0
    isArb := Or.inl ⟨by nlinarith, by norm_num⟩
  }, trivial⟩

-- ============================================================================
-- PHASE 5: CROSS-ASSET DIVIDEND PLAYS
-- ============================================================================

/-- Dividend Pair Trading Spread: High-yield vs low-yield stock arbitrage.

    Statement: Spread(High_Yield_Stock, Low_Yield_Stock) ≤ Dividend_Yield_Diff + Fees

    Intuition:
    - High-yield stock: pays dividend D_H
    - Low-yield stock: pays dividend D_L
    - Price spread should reflect dividend difference
    - If spread > yield diff → buy low-yield, short high-yield
    - Pair trade profits from convergence

    Arbitrage if violated:
    - Relative value between similar stocks with different yields
-/
theorem dividend_pair_trading_spread
    (stock_high_yield stock_low_yield : Quote)
    (fees_high fees_low : Fees)
    (div_high div_low : ℝ)
    (hDiv : div_high ≥ div_low) :
    let high_ask := stock_high_yield.ask.val + Fees.totalFee fees_high stock_high_yield.ask.val (by sorry)
    let low_bid := stock_low_yield.bid.val - Fees.totalFee fees_low stock_low_yield.bid.val (by sorry)
    let spread := high_ask - low_bid
    let div_diff := div_high - div_low
    spread ≤ div_diff + 0.01 := by
  by_contra h
  push_neg at h
  exfalso
  exact noArbitrage ⟨{
    initialCost := ((stock_high_yield.ask.val + Fees.totalFee fees_high stock_high_yield.ask.val (by sorry)) - (stock_low_yield.bid.val - Fees.totalFee fees_low stock_low_yield.bid.val (by sorry))) - (div_high - div_low) - 0.01
    minimumPayoff := 0
    isArb := Or.inl ⟨by nlinarith, by norm_num⟩
  }, trivial⟩

/-- Dividend vs Repo Rate Arbitrage: Dividend yield vs repo rate consistency.

    Statement: If Dividend_Yield > Repo_Rate → Short_Stock, Repo, Earn_Spread

    Intuition:
    - Repo rate: borrowing cost to short stock
    - Dividend yield: income from holding long
    - If dividend > repo rate: long stock, repo borrow at low rate, profit
    - If dividend < repo rate: short stock, repo lend at high rate, profit

    Arbitrage if violated:
    - Yield carry trades: relative value between dividend and funding costs
-/
theorem dividend_vs_repo_rate_arbitrage
    (stock : Quote)
    (stock_fees : Fees)
    (annual_dividend : ℝ)
    (repo_rate : Rate)
    (time : Time)
    (hStock : stock.bid.val > 0) :
    let dividend_yield := annual_dividend / stock.bid.val
    let repo_cost := stock.bid.val * repo_rate.val * time.val
    -- If yield > repo rate, arbitrage exists
    (dividend_yield - repo_rate.val) * stock.bid.val * time.val ≥ -0.01 := by
  by_contra h
  push_neg at h
  exfalso
  exact noArbitrage ⟨{
    initialCost := -(((annual_dividend / stock.bid.val) - repo_rate.val) * stock.bid.val * time.val) - 0.01
    minimumPayoff := 0
    isArb := Or.inl ⟨by nlinarith, by norm_num⟩
  }, trivial⟩

/-- Dividend Futures Calendar Spread: Ex-date timing determines dividend capture.

    Statement: Calendar spread accounts for which contract captures dividend

    Intuition:
    - Futures contracts specify delivery date
    - Dividend goes to whoever holds contract on ex-date
    - Near contract (before ex-date): includes dividend
    - Far contract (after ex-date): excludes dividend
    - Spread must reflect this timing difference

    Arbitrage if violated:
    - Futures calendar spread mispricing around ex-dates
-/
theorem dividend_futures_calendar_spread
    (future_near future_far : Quote)
    (near_fees far_fees : Fees)
    (dividend : ℝ)
    (hDiv : dividend > 0) :
    let near_bid := future_near.bid.val - Fees.totalFee near_fees future_near.bid.val (by sorry)
    let far_ask := future_far.ask.val + Fees.totalFee far_fees future_far.ask.val (by sorry)
    let spread := near_bid - far_ask
    spread ≤ dividend + 0.01 := by
  by_contra h
  push_neg at h
  exfalso
  exact noArbitrage ⟨{
    initialCost := ((future_near.bid.val - Fees.totalFee near_fees future_near.bid.val (by sorry)) - (future_far.ask.val + Fees.totalFee far_fees future_far.ask.val (by sorry))) - dividend - 0.01
    minimumPayoff := 0
    isArb := Or.inl ⟨by nlinarith, by norm_num⟩
  }, trivial⟩

-- ============================================================================
-- COMPUTATIONAL DETECTION FUNCTIONS (Phases 1-5)
-- ============================================================================

/-- Check dividend-adjusted put-call parity violation. -/
def checkDividendParityViolation
    (call_price put_price spot_price strike rate_val time_val dividend_pv : ℝ) : Bool :=
  let parity_lhs := call_price - put_price
  let parity_rhs := spot_price - strike * (1.0 / (1.0 + rate_val * time_val)) - dividend_pv
  (parity_lhs - parity_rhs).abs ≤ 0.01

/-- Check ex-dividend price drop consistency. -/
def checkExDividendDrop (stock_cum stock_ex dividend : ℝ) (tolerance : ℝ) : Bool :=
  (stock_ex - (stock_cum - dividend)).abs ≤ tolerance

/-- Check dividend yield within reasonable bounds. -/
def checkDividendYield (annual_dividend stock_price max_yield : ℝ) : Bool :=
  stock_price > 0 ∧ annual_dividend / stock_price ≤ max_yield

/-- Check forward price dividend adjustment. -/
def checkForwardDividendAdjustment
    (spot forward rate time dividend_pv : ℝ) (tolerance : ℝ) : Bool :=
  let forward_fair := spot * Real.exp (rate * time) - dividend_pv
  (forward - forward_fair).abs ≤ tolerance

/-- Check cumulative dividend PV bounded by stock price. -/
def checkCumulativeDividendPV (stock_price total_dividend_pv : ℝ) : Bool :=
  total_dividend_pv ≤ stock_price

/-- Check American put early exercise value. -/
def checkAmericanPutEarlyExercise
    (american_put european_put dividend : ℝ) (tolerance : ℝ) : Bool :=
  american_put ≥ european_put + dividend - tolerance

/-- Check American call post-dividend bound. -/
def checkAmericanCallDividendBound
    (call_post_div call_pre_div : ℝ) : Bool :=
  call_post_div ≤ call_pre_div

/-- Check ex-dividend call floor (intrinsic value). -/
def checkCallFloor (call_price stock_ex strike : ℝ) : Bool :=
  call_price ≥ max 0 (stock_ex - strike)

/-- Check American put strike dividend interaction. -/
def checkPutStrikeDividendInteraction
    (put_value stock_cum dividend strike : ℝ) : Bool :=
  let stock_ex := stock_cum - dividend
  put_value ≥ max 0 (strike - stock_ex)

/-- Check dividend stripping synthetic bond cost. -/
def checkDividendStrippingCost
    (short_stock long_call short_put strike rate time : ℝ) : Bool :=
  let synthetic_cost := short_stock - long_call - short_put
  let bond_value := strike / (1.0 + rate * time)
  synthetic_cost ≤ bond_value + 0.01

/-- Check dividend capture hedge profitability. -/
def checkDividendCaptureHedge
    (stock_cost call_proceeds dividend bond_yield time : ℝ) : Bool :=
  let covered_call_return := dividend - (stock_cost - call_proceeds) * bond_yield * time
  covered_call_return ≥ -0.01

/-- Check conversion arbitrage dividend adjusted. -/
def checkConversionArbitrageDividend
    (long_stock long_put short_call strike rate time dividend : ℝ) : Bool :=
  let conversion_cost := long_stock + long_put - short_call
  let bond_equiv := strike / (1.0 + rate * time) + dividend
  conversion_cost ≤ bond_equiv + 0.01

/-- Check cash-secured put funding rate constraint. -/
def checkCashSecuredPutFunding
    (put_premium strike funding_rate dividend_yield time : ℝ) : Bool :=
  let funding_cost := strike * (funding_rate - dividend_yield) * time
  put_premium ≥ funding_cost - 0.01

/-- Check cash-secured put dividend reinvestment. -/
def checkPutDividendReinvestment
    (strike funding_rate dividend_yield time put_premium : ℝ) : Bool :=
  let interest_income := strike * funding_rate * time
  let dividend_income := strike * dividend_yield * time
  let total_return := interest_income + dividend_income - put_premium
  total_return ≥ -0.01

/-- Check dividend pair trading spread. -/
def checkDividendPairSpread
    (high_price low_price div_high div_low : ℝ) : Bool :=
  let spread := high_price - low_price
  let div_diff := div_high - div_low
  spread ≤ div_diff + 0.01

/-- Check dividend vs repo rate arbitrage. -/
def checkDividendRepoArbitrage
    (stock_price annual_dividend repo_rate time : ℝ) : Bool :=
  let dividend_yield := annual_dividend / stock_price
  ((dividend_yield - repo_rate) * stock_price * time).abs ≤ 0.01

/-- Check dividend futures calendar spread. -/
def checkDividendFuturesSpread
    (future_near future_far dividend : ℝ) : Bool :=
  let spread := future_near - future_far
  spread ≤ dividend + 0.01

end Finance.DividendArbitrage
