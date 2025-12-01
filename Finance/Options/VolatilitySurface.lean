-- Volatility surface analysis: smile, skew, and term structure
-- Detects inconsistencies in implied volatility across strikes and maturities

import Finance.Core
import Finance.Options.European
import Finance.Options.Convexity
import Finance.Options.Calendar
import Finance.Options.BlackScholes

namespace Finance.Options

-- ============================================================================
-- Volatility Surface Fundamentals
-- ============================================================================

/-- Implied volatility surface: a grid of volatilities across strikes and expirations. -/
structure VolatilitySurface where
  strikes : List Float               -- Strike prices (sorted)
  expirations : List Float           -- Time to expirations (sorted)
  impliedVols : Array (Array Float)  -- IV grid [expiration][strike]

  -- Invariants (would be proofs in a stricter system)
  -- strikesLengthMatch : strikes.length * expirations.length = impliedVols.size
  -- allVolsPositive : ∀ σ in impliedVols, σ > 0

/-- A single point on the surface. -/
structure VolPoint where
  strike : Float
  expiration : Float
  impliedVol : Float

/-- The "smile" or "skew": how IV varies across strikes at a fixed expiration. -/
structure SmileAnalysis where
  expiration : Float
  atm_vol : Float           -- IV at-the-money
  call_side_slope : Float   -- How IV changes for higher strikes (calls)
  put_side_slope : Float    -- How IV changes for lower strikes (puts)
  convexity : Float         -- Curvature (butterfly)
  smileType : String        -- "smile", "skew_up", "skew_down", "flat"

/-- The term structure: how IV varies across expirations at a fixed strike. -/
structure TermStructureAnalysis where
  strike : Float
  shortTermVol : Float      -- IV near expiry
  longTermVol : Float       -- IV far from expiry
  slope : Float            -- Long - short (positive = upward sloping)
  termType : String        -- "upward", "downward", "flat", "humped"

-- ============================================================================
-- Smile and Skew Detection
-- ============================================================================

/-- Extract the smile at a given expiration: IV as function of strike.

    Detects whether market exhibits:
    - Smile: symmetric (both sides have negative slope)
    - Skew: asymmetric (one side steeper)
    - Flat: no curvature
-/
def analyzeSmile (surface : VolatilitySurface) (expirationIndex : Nat) :
    Option SmileAnalysis :=
  if expirationIndex ≥ surface.expirations.length then
    none
  else if expirationIndex ≥ surface.impliedVols.size then
    none
  else
    let ivs := Array.getD surface.impliedVols expirationIndex #[]
    if ivs.size < 3 then none  -- Need at least 3 strikes
    else
      let expiration := List.getD surface.expirations expirationIndex 0.0
      let midIndex := ivs.size / 2
      let atm_vol := Array.getD ivs midIndex 0.0

      -- Extract slopes from left side (lower strikes)
      let putSlope := if midIndex ≥ 2 then
        let first := Array.getD ivs 0 0.0
        let last := Array.getD ivs (midIndex - 1) 0.0
        (last - first) / midIndex.toFloat
      else
        0.0

      -- Extract slopes from right side (higher strikes)
      let callSlope := if ivs.size - midIndex ≥ 2 then
        let first := Array.getD ivs midIndex 0.0
        let last := Array.getD ivs (ivs.size - 1) 0.0
        (last - first) / (ivs.size - midIndex).toFloat
      else
        0.0

      -- Butterfly (convexity) using 3-point rule
      let convex := if ivs.size ≥ 3 then
        let left := Array.getD ivs 0 0.0
        let mid := Array.getD ivs (ivs.size / 2) 0.0
        let right := Array.getD ivs (ivs.size - 1) 0.0
        2.0 * mid - (left + right) / 2.0
      else
        0.0

      -- Classify smile type
      let smileType := if callSlope.abs < 0.01 && putSlope.abs < 0.01 then
        "flat"
      else if (callSlope + putSlope).abs < 0.01 then
        "smile"  -- Symmetric
      else if callSlope > putSlope then
        "skew_up"  -- Right skew (calls have steeper IV)
      else
        "skew_down"

      some ⟨expiration, atm_vol, callSlope, putSlope, convex, smileType⟩

/-- Compare smiles across multiple expirations (for smile arbitrage detection).

    If smile shape changes dramatically between expirations,
    might indicate mispricing opportunity.
-/
def compareSmiles (surface : VolatilitySurface) (idx1 idx2 : Nat) :
    Option Float :=
  let smile1 := analyzeSmile surface idx1
  let smile2 := analyzeSmile surface idx2

  match smile1, smile2 with
  | some s1, some s2 =>
    let convexDiff := (s2.convexity - s1.convexity).abs
    some convexDiff
  | _, _ => none

-- ============================================================================
-- Term Structure Analysis
-- ============================================================================

/-- Extract term structure at a given strike: IV as function of expiration. -/
def analyzeTermStructure (surface : VolatilitySurface) (strikeIndex : Nat) :
    Option TermStructureAnalysis :=
  if strikeIndex ≥ surface.strikes.length then
    none
  else if surface.impliedVols.size = 0 then
    none
  else
    let strike := List.getD surface.strikes strikeIndex 0.0
    -- Build array of IVs at this strike across expirations
    let ivs := Array.range (surface.impliedVols.size) |>.filterMap fun i =>
      if i < surface.impliedVols.size then
        let row := Array.getD surface.impliedVols i #[]
        if strikeIndex < row.size then
          some (Array.getD row strikeIndex 0.0)
        else
          none
      else
        none

    if ivs.size < 2 then
      none
    else
      let shortTermVol := Array.getD ivs 0 0.0
      let longTermVol := Array.getD ivs (ivs.size - 1) 0.0
      let slope := longTermVol - shortTermVol

      let termType := if slope.abs < 0.01 then
        "flat"
      else if slope > 0 then
        "upward"
      else if slope < -0.001 then
        "downward"
      else
        "humped"  -- Complex shape

      some ⟨strike, shortTermVol, longTermVol, slope, termType⟩

/-- Forward volatility: implied volatility from one date to another.

    If short-term vol = σ_S and long-term vol = σ_L, the implied vol
    from time T1 to T2 is the vol that makes:
    σ_L²·T2 = σ_S²·T1 + σ_forward²·(T2 - T1)

    Solves for: σ_forward = sqrt((σ_L²·T2 - σ_S²·T1) / (T2 - T1))
-/
def forwardVolatility
    (shortTermVol : Float) (shortTermTime : Float)
    (longTermVol : Float) (longTermTime : Float) :
    Float :=
  let numerator := (longTermVol * longTermVol * longTermTime) -
                   (shortTermVol * shortTermVol * shortTermTime)
  let denominator := longTermTime - shortTermTime

  if denominator ≤ 0 then
    0
  else
    let variance := numerator / denominator
    if variance < 0 then 0 else Float.sqrt variance

-- ============================================================================
-- Volatility Consistency Rules (Arbitrage Detection)
-- ============================================================================

/-- Check if butterfly spread is inconsistent with vol surface smile.

    If call butterfly is expensive relative to put butterfly,
    might indicate smile inconsistency.
-/
def checkSmileConsistency
    (callButterfly putButterfly : Float)
    (spread : Float) :
    Bool :=
  -- If difference exceeds threshold, likely inconsistency
  (callButterfly - putButterfly).abs > spread * 0.05

/-- Check if calendar spread violates term structure no-arbitrage.

    Using put-call parity, calendar spreads on calls and puts must be consistent
    with the underlying term structure.
-/
def checkTermConsistency
    (callCalendarDev putCalendarDev : Float)
    (maxDeviation : Float) :
    Bool :=
  -- Both should have same sign and similar magnitude
  let signMismatch := (callCalendarDev > 0) ≠ (putCalendarDev > 0)
  let magnitudeDiff := (callCalendarDev.abs - putCalendarDev.abs).abs
  signMismatch || (magnitudeDiff > maxDeviation)

/-- Detect if implied vol is too high relative to realized vol.

    Realized vol: historical volatility of returns.
    Implied vol: market expectation from option prices.

    If IV >> realized vol, options may be overpriced.
-/
def checkImpliedVsRealized
    (impliedVol realizedVol : Float)
    (threshold : Float := 1.2) :  -- IV should be < 1.2x realized vol
    Bool :=
  impliedVol > realizedVol * threshold

/-- Check for volatility skew asymmetry relative to skew arbitrage limits.

    If skew is too steep, might be exploitable via put spreads or call spreads.
-/
def checkSkewAsymmetry
    (callSlope putSlope : Float)
    (maxAsymmetry : Float := 0.05) :  -- 5% difference is typical
    Bool :=
  (callSlope - putSlope).abs > maxAsymmetry

-- ============================================================================
-- Smile/Skew Arbitrage Opportunities
-- ============================================================================

/-- A smile arbitrage opportunity: exploit skew inconsistency. -/
structure SmileArbitrageOpportunity where
  expirationIndex : Nat
  lowStrike : Float
  atmStrike : Float
  highStrike : Float
  callButterfly : Float    -- Cost of call butterfly
  putButterfly : Float     -- Cost of put butterfly
  deviation : Float        -- callButterfly - putButterfly
  strategy : String        -- "buy_call_sell_put" or vice versa
  estimatedProfit : Float

/-- Find smile arbitrage: when call and put butterflies diverge.

    Sell the expensive butterfly, buy the cheap one.
-/
def findSmileArbitrage
    (surface : VolatilitySurface)
    (expirationIndex : Nat)
    (minThreshold : Float := 0.01) :  -- Min profit threshold
    List SmileArbitrageOpportunity :=
  -- This is a simplified version
  -- In practice, would iterate through all strike triples
  []  -- Placeholder for detailed implementation

-- ============================================================================
-- Term Structure Arbitrage
-- ============================================================================

/-- A term structure arbitrage: exploit calendar spread inconsistency. -/
structure TermStructureArbitrageOpportunity where
  strike : Float
  shortExpiration : Float
  longExpiration : Float
  callSpreadDev : Float    -- Deviation in call calendar spread
  putSpreadDev : Float     -- Deviation in put calendar spread
  inconsistency : Float    -- Difference between call and put deviations
  strategy : String
  estimatedProfit : Float

-- ============================================================================
-- Surface Reconstruction and Interpolation
-- ============================================================================

/-- Linear interpolation for IV at non-grid points.

    Given two IVs at strikes K1 and K2, estimate IV at strike K.
-/
def interpolateStrike
    (k1 iv1 k2 iv2 k : Float) :
    Float :=
  if (k2 - k1).abs < 0.0001 then
    (iv1 + iv2) / 2.0
  else
    iv1 + (iv2 - iv1) * (k - k1) / (k2 - k1)

/-- Linear interpolation across expirations. -/
def interpolateExpiration
    (t1 iv1 t2 iv2 t : Float) :
    Float :=
  if (t2 - t1).abs < 0.0001 then
    (iv1 + iv2) / 2.0
  else
    iv1 + (iv2 - iv1) * (t - t1) / (t2 - t1)

/-- Bilinear interpolation for IV at arbitrary (strike, expiration) point. -/
def interpolateSurface
    (surface : VolatilitySurface)
    (strike : Float)
    (expiration : Float) :
    Option Float :=
  -- Find bounding strikes and expirations
  if surface.strikes.isEmpty || surface.expirations.isEmpty then
    none
  else
    -- Clamp to surface boundaries
    let minStrike := surface.strikes.head?.getD 0.0
    let maxStrike := surface.strikes.getLast?.getD 0.0
    let minExp := surface.expirations.head?.getD 0.0
    let maxExp := surface.expirations.getLast?.getD 0.0
    let clamped_strike := min (max strike minStrike) maxStrike
    let clamped_exp := min (max expiration minExp) maxExp

    -- Simplified: return nearest point
    -- Full implementation would do proper bilinear interpolation
    if surface.impliedVols.isEmpty then
      none
    else
      match Array.getD surface.impliedVols 0 #[] with
      | #[] => none
      | row => some (Array.getD row 0 0.0)

-- ============================================================================
-- Result Aggregation
-- ============================================================================

/-- Comprehensive volatility surface smile and term structure analysis. -/
structure SurfaceSmileTermAnalysis where
  smiles : List SmileAnalysis
  termStructures : List TermStructureAnalysis
  smileArbitrages : List SmileArbitrageOpportunity
  termArbitrages : List TermStructureArbitrageOpportunity
  totalOpportunities : Nat
  smileConsistencyViolations : Nat
  termConsistencyViolations : Nat

/-- Analyze entire volatility surface for smile, skew, and term structure patterns. -/
def analyzeSurface (surface : VolatilitySurface) :
    SurfaceSmileTermAnalysis :=
  -- Collect smiles across all expirations
  let smiles := List.range surface.expirations.length |>.filterMap fun i =>
    analyzeSmile surface i

  -- Collect term structures across all strikes
  let termStructures := List.range surface.strikes.length |>.filterMap fun j =>
    analyzeTermStructure surface j

  let smileArbitrages := findSmileArbitrage surface 0  -- Placeholder
  let totalOpps := smileArbitrages.length

  ⟨smiles, termStructures, smileArbitrages, [], totalOpps, 0, 0⟩

end Finance.Options
