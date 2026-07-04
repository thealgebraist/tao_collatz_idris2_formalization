module TaoCollatz.PaperInterfaces

import TaoCollatz.Core
import TaoCollatz.Dynamics
import TaoCollatz.Large

%default total

public export
record OddThresholdChoice where
  constructor MkOddThresholdChoice
  oddThreshold : (Pos -> Nat) -> OddPos -> Nat

public export
record OddThresholdGrowth where
  constructor MkOddThresholdGrowth
  growthChoice : OddThresholdChoice
  oddThresholdGrows :
    (f : Pos -> Nat) ->
    TendsToInfinityPos f ->
    TendsToInfinityOdd (growthChoice.oddThreshold f)

public export
record OddThresholdCompatibility where
  constructor MkOddThresholdCompatibility
  compatibleGrowth : OddThresholdGrowth
  thresholdCompatibility :
    (f : Pos -> Nat) ->
    (pos : Pos) ->
    Leq (compatibleGrowth.growthChoice.oddThreshold f (oddPart pos)) (f pos)

public export
record OddThresholdSystem where
  constructor MkOddThresholdSystem
  thresholdCompatibilityProof : OddThresholdCompatibility

-- The odd-part orbit simulation is just the generic `OrbitSimulation` for the
-- Collatz/Syracuse pair along the odd-part map -- no separate record needed.
public export
OddPartOrbitSimulation : Type
OddPartOrbitSimulation =
  OrbitSimulation
    Pos
    OddPos
    Col
    Syr
    TaoCollatz.Dynamics.posSize
    TaoCollatz.Dynamics.oddSize
    TaoCollatz.Dynamics.oddPart

public export
record FirstPassageTailEstimate where
  constructor MkFirstPassageTailEstimate
  tailEstimatePayload : Type
  tailEstimateEvidence : tailEstimatePayload

public export
record FirstPassageStabilityEstimate where
  constructor MkFirstPassageStabilityEstimate
  stabilityEstimatePayload : Type
  stabilityEstimateEvidence : stabilityEstimatePayload

public export
record ValuationDistribution where             -- Proposition 1.9 payload
  constructor MkValuationDistribution
  valuationTailEstimate : FirstPassageTailEstimate

public export
StabilityFromValuations : Type
StabilityFromValuations =
  ValuationDistribution -> FirstPassageStabilityEstimate

public export
record StabilityPrinciple where
  constructor MkStabilityPrinciple
  stabilityFromValuations : StabilityFromValuations

public export
FineScaleMixing : Type                        -- Proposition 1.14 payload
FineScaleMixing = StabilityPrinciple

public export
FourierDecay : Type                           -- Proposition 1.17 payload
FourierDecay = StabilityPrinciple

public export
KeyFourierEstimate : Type                     -- Proposition 7.1 payload
KeyFourierEstimate = StabilityPrinciple

public export
RenewalWhitePoints : Type                     -- Proposition 7.3 payload
RenewalWhitePoints = StabilityPrinciple

public export
RenewalMonotonicity : Type                    -- Proposition 7.8 payload
RenewalMonotonicity = StabilityPrinciple
