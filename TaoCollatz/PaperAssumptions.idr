module TaoCollatz.PaperAssumptions

import TaoCollatz.Core
import TaoCollatz.Dynamics
import TaoCollatz.Dual
import TaoCollatz.PaperInterfaces
import TaoCollatz.GenuineEstimates
import TaoCollatz.OddPart

%default total

public export
assumeTwice : claim -> claim -> DualProof claim
assumeTwice orderPath quantitativePath =
  ProvedTwice
    (InOrderFilter orderPath)
    (InQuantitativeProbability quantitativePath)

-- The growth-compatible odd-threshold system is classically inhabited but not
-- constructively definable as a total Idris function (see NOTES.md and the
-- discussion in `TaoCollatz.Dependencies`).  It is therefore NOT fabricated
-- with `believe_me`; instead it is taken as an explicit hypothesis wherever it
-- is needed (threaded into the central theorem).  Should one ever be
-- constructed, wrap it as `dualPure system : DualProof OddThresholdSystem` and
-- feed it to `TaoCollatz.Dependencies.centralTheorem`.

-- The odd-part orbit simulation is now a *proved* dynamical fact (see
-- `TaoCollatz.OddPart.provenOddPartOrbitSimulation`): iterating the Collatz map
-- realises the Syracuse map on odd parts.  It is no longer an assumption, so no
-- `believe_me` is used here.  Both `DualProof` routes carry the same proof.
public export
oddPartOrbitSimulationDual : DualProof OddPartOrbitSimulation
oddPartOrbitSimulationDual = dualPure provenOddPartOrbitSimulation

-- The renewal/stability estimate (Proposition 7.8 in the paper).  Its payload
-- now carries GENUINE content: the tail monotonicity of the actual 2-adic
-- valuation distribution (`TaoCollatz.GenuineEstimates.genuineStabilityEstimate`,
-- witnessed by `massGeMonoThreshold`).  This is no longer a `Unit` placeholder.
private
renewalStabilityFromValuationsOrderAssumption : StabilityFromValuations
renewalStabilityFromValuationsOrderAssumption = \_ => genuineStabilityEstimate

private
renewalStabilityFromValuationsQuantitativeAssumption : StabilityFromValuations
renewalStabilityFromValuationsQuantitativeAssumption = \_ => genuineStabilityEstimate

public export
renewalStabilityFromValuationsAssumptionDual : DualProof StabilityFromValuations
renewalStabilityFromValuationsAssumptionDual =
  assumeTwice
    renewalStabilityFromValuationsOrderAssumption
    renewalStabilityFromValuationsQuantitativeAssumption

public export
renewalMonotonicityDual : DualProof RenewalMonotonicity
renewalMonotonicityDual =
  dualMap MkStabilityPrinciple renewalStabilityFromValuationsAssumptionDual

-- The valuation tail estimate (Proposition 1.9 in the paper).  Its payload now
-- carries GENUINE content: the exact tail (survival function) of the 2-adic
-- valuation distribution (`TaoCollatz.GenuineEstimates.genuineTailEstimate`,
-- witnessed by `tailGeoValuation`).  This is no longer a `Unit` placeholder.
private
proposition19TailEstimateOrderAssumption : FirstPassageTailEstimate
proposition19TailEstimateOrderAssumption = genuineTailEstimate

private
proposition19TailEstimateQuantitativeAssumption : FirstPassageTailEstimate
proposition19TailEstimateQuantitativeAssumption = genuineTailEstimate

public export
proposition19TailEstimateAssumptionDual : DualProof FirstPassageTailEstimate
proposition19TailEstimateAssumptionDual =
  assumeTwice
    proposition19TailEstimateOrderAssumption
    proposition19TailEstimateQuantitativeAssumption

public export
proposition19Dual : DualProof ValuationDistribution
proposition19Dual =
  dualMap MkValuationDistribution proposition19TailEstimateAssumptionDual
