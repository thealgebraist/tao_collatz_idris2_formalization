module TaoCollatz.PaperStructure

import TaoCollatz.Dual
import TaoCollatz.Large
import TaoCollatz.Dependencies

%default total

--------------------------------------------------------------------------------
-- Off-critical-path paper structure.
--
-- These declarations record additional milestones of Tao's argument that are
-- NOT needed by the minimal unified proof in `TaoCollatz.Dependencies`
-- (`centralTheorem` / `centralTheoremUnified`).  They are the paper's internal
-- proposition chain 7.8 => 7.3 => 7.1 => 1.17 => 1.14 (all identity reductions
-- at the current placeholder resolution), together with the alternate valuation
-- tail estimate and the paper-domain form of Theorem 3.1 => Theorem 1.6.
--
-- Keeping them here documents the paper's full logical skeleton while leaving
-- the dependency surface of the main theorem minimal and orthogonal.
--------------------------------------------------------------------------------

public export
proposition19TailEstimateDual : DualProof FirstPassageTailEstimate
proposition19TailEstimateDual =
  proposition19TailEstimateAssumptionDual

public export
proposition19TailEstimate : FirstPassageTailEstimate
proposition19TailEstimate = orderClaim proposition19TailEstimateDual

public export
renewalToStabilityDual : DualProof (RenewalMonotonicity -> StabilityPrinciple)
renewalToStabilityDual = dualId

public export
renewalToStability : RenewalMonotonicity -> StabilityPrinciple
renewalToStability = orderClaim renewalToStabilityDual

public export
stabilityFromRenewalAndValuationsDual :
  DualProof (RenewalMonotonicity -> ValuationDistribution -> FirstPassageStabilityEstimate)
stabilityFromRenewalAndValuationsDual =
  dualPure
    (\renewal, valuation =>
      (renewalToStability renewal).stabilityFromValuations valuation)

public export
stabilityFromRenewalAndValuations :
  RenewalMonotonicity -> ValuationDistribution -> FirstPassageStabilityEstimate
stabilityFromRenewalAndValuations =
  orderClaim stabilityFromRenewalAndValuationsDual

public export
proposition78To73Dual : DualProof (RenewalMonotonicity -> RenewalWhitePoints)
proposition78To73Dual = renewalToStabilityDual

public export
proposition78To73 : RenewalMonotonicity -> RenewalWhitePoints
proposition78To73 = renewalToStability

public export
proposition73To71Dual : DualProof (RenewalWhitePoints -> KeyFourierEstimate)
proposition73To71Dual = dualId

public export
proposition73To71 : RenewalWhitePoints -> KeyFourierEstimate
proposition73To71 = orderClaim proposition73To71Dual

public export
proposition71To17Dual : DualProof (KeyFourierEstimate -> FourierDecay)
proposition71To17Dual = dualId

public export
proposition71To17 : KeyFourierEstimate -> FourierDecay
proposition71To17 = orderClaim proposition71To17Dual

public export
proposition17To14Dual : DualProof (FourierDecay -> FineScaleMixing)
proposition17To14Dual = dualId

public export
proposition17To14 : FourierDecay -> FineScaleMixing
proposition17To14 = orderClaim proposition17To14Dual

public export
propositions19And14To11Dual :
  DualProof (ValuationDistribution -> FineScaleMixing -> StabilisationOfFirstPassage)
propositions19And14To11Dual =
  dualPure
    (\valuation, mixing =>
      (valuation.valuationTailEstimate, mixing.stabilityFromValuations valuation))

public export
propositions19And14To11 :
  ValuationDistribution -> FineScaleMixing -> StabilisationOfFirstPassage
propositions19And14To11 = orderClaim propositions19And14To11Dual

public export
theorem31ToTheorem16PaperDomainDual :
  DualProof (QuantitativeSyracuseBound -> Theorem16PaperDomain)
theorem31ToTheorem16PaperDomainDual =
  dualCompose
    (dualPure theorem16PaperDomainFromTheorem16)
    theorem31ToTheorem16Dual

public export
theorem31ToTheorem16PaperDomain :
  QuantitativeSyracuseBound -> Theorem16PaperDomain
theorem31ToTheorem16PaperDomain =
  orderClaim theorem31ToTheorem16PaperDomainDual
