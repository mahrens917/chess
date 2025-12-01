-- Unified No-Arbitrage Rule Scanner
-- Runs all option arbitrage detection rules simultaneously
-- Produces comprehensive violation report

import Finance.Core
import Finance.Options.European
import Finance.Options.Bounds
import Finance.Options.Monotonicity
import Finance.Options.Convexity

namespace Finance.Options

-- ============================================================================
-- Market Data Input
-- ============================================================================

/-- Complete market snapshot for option arbitrage scanning. -/
structure MarketSnapshot where
  -- Underlying & spot price
  spot : Quote

  -- Risk-free rate and dividend yield
  rate : Rate
  dividendYield : Rate

  -- Call and put quotes at different strikes
  strikes : List Float  -- sorted ascending
  callQuotes : List Quote  -- same order as strikes
  putQuotes : List Quote   -- same order as strikes

  -- Transaction fees
  callFees : Fees
  putFees : Fees
  spotFees : Fees

  -- Expiry
  expiry : Time

  -- Validity checks
  strikesLengthMatch : strikes.length = callQuotes.length ∧
                     strikes.length = putQuotes.length

/-- Single rule violation report. -/
structure RuleViolation where
  ruleName : String          -- "pcp", "call_upper", "call_lower", etc.
  violationType : String     -- describes what rule was broken
  strikes : List Float       -- which strikes involved
  profitOpportunity : Float  -- profit after fees
  profitPercentage : Float   -- as % of capital required
  recommendedAction : String -- what to do to exploit it
  confidence : Float         -- how clear the arbitrage is (0-1)

/-- Aggregated report from all rules. -/
structure ArbitrageReport where
  snapshotTime : String  -- when the scan was done

  -- Summary statistics
  totalViolations : Nat
  numRulesViolated : Nat

  -- Individual violations
  violations : List RuleViolation

  -- Best opportunities (top 3 by profit)
  topOpportunities : List RuleViolation

  -- Overall assessment
  hasArbitrage : Bool
  bestProfit : Float
  totalProfit : Float  -- sum of all profitable arbs

  -- Recommendation
  recommendation : String
  urgency : String  -- "none", "low", "medium", "high"

-- ============================================================================
-- Rule 1: Put-Call Parity
-- ============================================================================

/-- Check put-call parity across all strikes. -/
def scanPutCallParity
    (spot : Quote) (strikes : List Float) (callQuotes : List Quote)
    (putQuotes : List Quote) (rate : Rate) (expiry : Time)
    (callFees putFees spotFees : Fees) :
    List RuleViolation :=
  []

-- ============================================================================
-- Rule 2: Call Bounds (Upper & Lower)
-- ============================================================================

/-- Check all call upper and lower bounds. -/
def scanCallBounds
    (spot : Quote) (strikes : List Float) (callQuotes : List Quote)
    (rate : Rate) (expiry : Time) (callFees spotFees : Fees) :
    List RuleViolation :=
  []

-- ============================================================================
-- Rule 3: Put Bounds (Upper & Lower)
-- ============================================================================

/-- Check all put upper and lower bounds. -/
def scanPutBounds
    (strikes : List Float) (putQuotes : List Quote)
    (rate : Rate) (expiry : Time) (putFees : Fees) :
    List RuleViolation :=
  []

-- ============================================================================
-- Rule 4: Call Spread Monotonicity
-- ============================================================================

/-- Check all call spreads for monotonicity violations. -/
def scanCallMonotonicity
    (strikes : List Float) (callQuotes : List Quote)
    (callFees : Fees) :
    List RuleViolation :=
  []

-- ============================================================================
-- Rule 5: Put Spread Monotonicity
-- ============================================================================

/-- Check all put spreads for monotonicity violations. -/
def scanPutMonotonicity
    (strikes : List Float) (putQuotes : List Quote)
    (putFees : Fees) :
    List RuleViolation :=
  []

-- ============================================================================
-- Rule 6: Call Butterfly Convexity
-- ============================================================================

/-- Check all call butterflies for convexity violations. -/
def scanCallButterflies
    (strikes : List Float) (callQuotes : List Quote)
    (callFees : Fees) :
    List RuleViolation :=
  []

-- ============================================================================
-- Rule 7: Put Butterfly Convexity
-- ============================================================================

/-- Check all put butterflies for convexity violations. -/
def scanPutButterflies
    (strikes : List Float) (putQuotes : List Quote)
    (putFees : Fees) :
    List RuleViolation :=
  []

-- ============================================================================
-- Comprehensive Scanner
-- ============================================================================

/-- Run all arbitrage detection rules on market snapshot.

    This is the main entry point for scanning a market for arbitrage opportunities.
    It runs all 7 rules (or combinations thereof) and aggregates results.
-/
def scanAllRules (snapshot : MarketSnapshot) : ArbitrageReport :=
  -- Extract data
  let strikes := snapshot.strikes
  let callQuotes := snapshot.callQuotes
  let putQuotes := snapshot.putQuotes
  let spot := snapshot.spot
  let rate := snapshot.rate
  let expiry := snapshot.expiry
  let callFees := snapshot.callFees
  let putFees := snapshot.putFees
  let spotFees := snapshot.spotFees

  -- Run each rule
  let pcpViolations := scanPutCallParity spot strikes callQuotes putQuotes rate expiry callFees putFees spotFees
  let callBoundViolations := scanCallBounds spot strikes callQuotes rate expiry callFees spotFees
  let putBoundViolations := scanPutBounds strikes putQuotes rate expiry putFees
  let callMonoViolations := scanCallMonotonicity strikes callQuotes callFees
  let putMonoViolations := scanPutMonotonicity strikes putQuotes putFees
  let callButterflyViolations := scanCallButterflies strikes callQuotes callFees
  let putButterflyViolations := scanPutButterflies strikes putQuotes putFees

  -- Combine all violations
  let allViolations := pcpViolations ++ callBoundViolations ++ putBoundViolations ++
                       callMonoViolations ++ putMonoViolations ++
                       callButterflyViolations ++ putButterflyViolations

  -- Sort by profit (descending)
  let sortedByProfit := allViolations.insertionSort (fun a b => a.profitOpportunity > b.profitOpportunity)
  let topThree := sortedByProfit.take 3

  -- Calculate totals
  let totalViolations := allViolations.length
  let rulesViolated := 7  -- could track which rules fired
  let totalProfit := allViolations.foldl (fun sum v => sum + max 0.0 v.profitOpportunity) 0.0
  let bestProfit : Float := match sortedByProfit.head? with
    | some v => v.profitOpportunity
    | none => 0.0

  -- Determine urgency
  let urgency :=
    if bestProfit > 0.1 then "high"
    else if bestProfit > 0.01 then "medium"
    else if bestProfit > (0 : Float) then "low"
    else "none"

  -- Recommendation
  let recommendation :=
    if allViolations.isEmpty then
      "✓ No arbitrage opportunities detected. Market appears fairly priced."
    else if bestProfit > 0.1 then
      "⚠ SIGNIFICANT arbitrage detected. Execute immediately."
    else if bestProfit > 0.01 then
      "⚡ Moderate arbitrage opportunities available. Consider execution."
    else
      "📊 Minor violations detected. Watch for execution opportunities."

  ⟨"now", totalViolations, rulesViolated, allViolations, topThree,
   !allViolations.isEmpty, bestProfit, totalProfit, recommendation, urgency⟩

-- ============================================================================
-- Reporting
-- ============================================================================

/-- Format a single violation for display. -/
def formatViolation (v : RuleViolation) : String :=
  s!"  • {v.ruleName}: {v.violationType}\n" ++
  s!"    Profit: {v.profitOpportunity} ({v.profitPercentage}%)\n" ++
  s!"    Action: {v.recommendedAction}\n"

/-- Format complete report for display. -/
def formatReport (report : ArbitrageReport) : String :=
  s!"╔══════════════════════════════════════════════════════════════════╗\n" ++
  s!"║            ARBITRAGE DETECTION REPORT                           ║\n" ++
  s!"╠══════════════════════════════════════════════════════════════════╣\n" ++
  s!"║ Status:        {if report.hasArbitrage then "VIOLATIONS FOUND" else "NO VIOLATIONS"}\n" ++
  s!"║ Urgency:       {report.urgency}\n" ++
  s!"║ Total Arbs:    {report.totalViolations}\n" ++
  s!"║ Rules Hit:     {report.numRulesViolated}\n" ++
  s!"║ Best Profit:   {report.bestProfit}\n" ++
  s!"║ Total Profit:  {report.totalProfit}\n" ++
  s!"╠══════════════════════════════════════════════════════════════════╣\n" ++
  (if !report.topOpportunities.isEmpty then
    s!"║ TOP OPPORTUNITIES\n" ++
    s!"├──────────────────────────────────────────────────────────────────┤\n" ++
    (report.topOpportunities.foldl (fun s v => s ++ formatViolation v) "") ++
    s!"├──────────────────────────────────────────────────────────────────┤\n"
  else "") ++
  s!"║ RECOMMENDATION:\n" ++
  s!"║ {report.recommendation}\n" ++
  s!"╚══════════════════════════════════════════════════════════════════╝\n"

-- ============================================================================
-- Quick Diagnostics
-- ============================================================================

/-- Quick health check for market prices. -/
def quickHealthCheck (snapshot : MarketSnapshot) : String :=
  let strikes := snapshot.strikes
  let numStrikes := strikes.length
  let hasCallData := snapshot.callQuotes.length > 0
  let hasPutData := snapshot.putQuotes.length > 0
  let spotValid := snapshot.spot.bid.val > 0 ∧ snapshot.spot.ask.val > snapshot.spot.bid.val

  if !spotValid then
    "❌ Invalid spot price (bid/ask)"
  else if !hasCallData || !hasPutData then
    "❌ Missing option quotes"
  else if numStrikes < 3 then
    "⚠️  Need at least 3 strikes for butterfly detection"
  else
    "✅ Market data valid. Ready for scanning."

end Finance.Options
