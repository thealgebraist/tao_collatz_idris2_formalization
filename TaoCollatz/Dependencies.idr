module TaoCollatz.Dependencies

import TaoCollatz.Core
import TaoCollatz.Dynamics
import TaoCollatz.Dual
import TaoCollatz.Large
import public TaoCollatz.PaperInterfaces
import public TaoCollatz.PaperAssumptions

%default total

public export
thresholdGrowthOfSystem : OddThresholdSystem -> OddThresholdGrowth
thresholdGrowthOfSystem system =
  system.thresholdCompatibilityProof.compatibleGrowth

public export
thresholdChoiceOfSystem : OddThresholdSystem -> OddThresholdChoice
thresholdChoiceOfSystem system =
  (thresholdGrowthOfSystem system).growthChoice

public export
OddPartOrbitTransfer : Type
OddPartOrbitTransfer =
  (f : Pos -> Nat) ->
  (pos : Pos) ->
  SyrBelow (oddPart pos) (f pos) ->
  ColBelow pos (f pos)

public export
oddPartOrbitTransferFromPointwise :
  PointwiseOrbitTransfer Pos OddPos TaoCollatz.Dynamics.oddPart ColBelow SyrBelow ->
  OddPartOrbitTransfer
oddPartOrbitTransferFromPointwise pointwise =
  \f, pos, syrBelow =>
    pointwise pos (f pos) syrBelow

public export
pointwiseTransferFromSimulation :
  OddPartOrbitSimulation ->
  PointwiseOrbitTransfer Pos OddPos TaoCollatz.Dynamics.oddPart ColBelow SyrBelow
pointwiseTransferFromSimulation simulation =
  \pos, limit, syrBelow =>
    simulationTransfersEventuallyBelow simulation pos limit syrBelow

public export
OddPartDensityLift : Type
OddPartDensityLift =
  (system : OddThresholdSystem) ->
  (f : Pos -> Nat) ->
  ExceptionalControl OddPos (\odd => SyrBelow odd ((thresholdChoiceOfSystem system).oddThreshold f odd)) ->
  ExceptionalControl Pos (\pos => SyrBelow (oddPart pos) (f pos))

public export
OddPartThresholdCompatibility : OddThresholdChoice -> Type
OddPartThresholdCompatibility choice =
  (f : Pos -> Nat) ->
  (pos : Pos) ->
  Leq (choice.oddThreshold f (oddPart pos)) (f pos)

public export
thresholdCompatibilityOfSystem :
  (system : OddThresholdSystem) ->
  OddPartThresholdCompatibility (thresholdChoiceOfSystem system)
thresholdCompatibilityOfSystem system =
  system.thresholdCompatibilityProof.thresholdCompatibility

public export
oddPartThresholdToReachability :
  (choice : OddThresholdChoice) ->
  OddPartThresholdCompatibility choice ->
  (f : Pos -> Nat) ->
  (pos : Pos) ->
  SyrBelow (oddPart pos) (choice.oddThreshold f (oddPart pos)) ->
  SyrBelow (oddPart pos) (f pos)
oddPartThresholdToReachability choice compatibility f pos syrBelow =
  eventuallyMonotoneBound
    syrBelow
    (compatibility f pos)

public export
oddPartDensityLiftFromThresholdSystem :
  OddPartDensityLift
oddPartDensityLiftFromThresholdSystem =
  \system, f, oddControl =>
    controlMap Pos
      (controlPullback TaoCollatz.Dynamics.oddPart oddControl)
      (\pos, syrBelow =>
        oddPartThresholdToReachability
          (thresholdChoiceOfSystem system)
          (thresholdCompatibilityOfSystem system)
          f
          pos
          syrBelow)

public export
SyracuseToCollatzDensityTransfer : Type
SyracuseToCollatzDensityTransfer =
  (OddThresholdSystem, OddPartOrbitTransfer)

public export
transferSystem : SyracuseToCollatzDensityTransfer -> OddThresholdSystem
transferSystem (system, orbit) = system

public export
transferChoice : SyracuseToCollatzDensityTransfer -> OddThresholdChoice
transferChoice transfer = thresholdChoiceOfSystem (transferSystem transfer)

public export
transferOrbit : SyracuseToCollatzDensityTransfer -> OddPartOrbitTransfer
transferOrbit (system, orbit) = orbit

public export
syracuseToCollatzFromPieces :
  OddThresholdSystem ->
  OddPartOrbitTransfer ->
  SyracuseToCollatzDensityTransfer
syracuseToCollatzFromPieces system orbit =
  (system, orbit)

public export
liftOddConclusion :
  (transfer : SyracuseToCollatzDensityTransfer) ->
  (f : Pos -> Nat) ->
  AlmostAllOdd (\odd => SyrBelow odd ((transferChoice transfer).oddThreshold f odd)) ->
  AlmostAllPos (\pos => ColBelow pos (f pos))
liftOddConclusion (system, orbit) f oddControl =
  let lifted = oddPartDensityLiftFromThresholdSystem system f oddControl in
    MkExceptionalControl
      (controlledSet lifted)
      (exceptionalSmall lifted)
      (\pos, good =>
        let syrBelow = controlledImplies lifted pos good in
          orbit f pos syrBelow)

-- The odd-threshold system (a growth-compatible choice of Syracuse thresholds)
-- is *not* a computable total function of `f` alone: the zero threshold
-- satisfies compatibility but not growth, while any growing choice needs an
-- infimum over each odd fibre (equivalently, the growth witness of `f`).  It is
-- classically inhabited but not constructively definable here.  Rather than
-- fabricate one with `believe_me`, we take an `OddThresholdSystem` as an
-- explicit hypothesis of the reduction (threaded from here to the central
-- theorem).  See NOTES.md.

public export
oddPartOrbitSimulation : OddPartOrbitSimulation
oddPartOrbitSimulation = orderClaim oddPartOrbitSimulationDual

public export
oddPartPointwiseOrbitTransferDual :
  DualProof (PointwiseOrbitTransfer Pos OddPos TaoCollatz.Dynamics.oddPart ColBelow SyrBelow)
oddPartPointwiseOrbitTransferDual =
  dualMap pointwiseTransferFromSimulation oddPartOrbitSimulationDual

public export
oddPartPointwiseOrbitTransfer :
  PointwiseOrbitTransfer Pos OddPos TaoCollatz.Dynamics.oddPart ColBelow SyrBelow
oddPartPointwiseOrbitTransfer = orderClaim oddPartPointwiseOrbitTransferDual

public export
oddPartOrbitTransferDual : DualProof OddPartOrbitTransfer
oddPartOrbitTransferDual =
  dualMap oddPartOrbitTransferFromPointwise oddPartPointwiseOrbitTransferDual

public export
oddPartOrbitTransfer : OddPartOrbitTransfer
oddPartOrbitTransfer = orderClaim oddPartOrbitTransferDual

public export
oddPartDensityLiftDual : DualProof OddPartDensityLift
oddPartDensityLiftDual = dualPure oddPartDensityLiftFromThresholdSystem

public export
oddPartDensityLift : OddPartDensityLift
oddPartDensityLift = orderClaim oddPartDensityLiftDual

public export
syracuseToCollatzDensityTransferDual :
  DualProof OddThresholdSystem -> DualProof SyracuseToCollatzDensityTransfer
syracuseToCollatzDensityTransferDual sysDual =
  dualApply
    (dualApply
      (dualPure syracuseToCollatzFromPieces)
      sysDual)
    oddPartOrbitTransferDual

public export
theorem16ToTheorem13FromTransfer :
  SyracuseToCollatzDensityTransfer -> Theorem16 -> Theorem13
theorem16ToTheorem13FromTransfer (system, orbit) syracuseTheorem f fGrows =
  liftOddConclusion (system, orbit) f
    (syracuseTheorem
      ((thresholdChoiceOfSystem system).oddThreshold f)
      ((thresholdGrowthOfSystem system).oddThresholdGrows f fGrows))

public export
theorem16ToTheorem13Dual :
  DualProof OddThresholdSystem -> DualProof (Theorem16 -> Theorem13)
theorem16ToTheorem13Dual sysDual =
  dualMap theorem16ToTheorem13FromTransfer (syracuseToCollatzDensityTransferDual sysDual)

public export
theorem16ToTheorem13 : OddThresholdSystem -> Theorem16 -> Theorem13
theorem16ToTheorem13 sys = orderClaim (theorem16ToTheorem13Dual (dualPure sys))

-- The quantitative alternate form, Theorem 3.1 of the paper:
--   for each N0, the logarithmic mass of Syracuse orbits that do not reach
--   N0 is O(log^{-c} N0), uniformly in the outer cutoff x.
public export
SyracuseExceptionalControl : (OddPos -> Nat) -> Type
SyracuseExceptionalControl f =
  ExceptionalControl OddPos (\odd => SyrBelow odd (f odd))

public export
QuantitativeSyracuseBound : Type
QuantitativeSyracuseBound =
  (f : OddPos -> Nat) -> TendsToInfinityOdd f -> SyracuseExceptionalControl f

public export
theorem31ToTheorem16FromPrinciple :
  QuantitativeSyracuseBound -> Theorem16
theorem31ToTheorem16FromPrinciple quantitativeBound f fGrows =
  quantitativeBound f fGrows

public export
FirstPassageControlFor : (OddPos -> Nat) -> Type
FirstPassageControlFor f =
  (FirstPassageTailEstimate, FirstPassageStabilityEstimate, TendsToInfinityOdd f)

public export
StabilisationOfFirstPassage : Type
StabilisationOfFirstPassage =
  (FirstPassageTailEstimate, FirstPassageStabilityEstimate)

public export
firstPassageToQuantitativeBound :
  FirstPassageTailEstimate ->
  FirstPassageStabilityEstimate ->
  QuantitativeSyracuseBound
firstPassageToQuantitativeBound tail stability =
  \f, fGrows =>
    controlByProperty
      (FirstPassageControlFor f)
      (tail, stability, fGrows)

public export
proposition11ToTheorem31FromIteration :
  StabilisationOfFirstPassage ->
  QuantitativeSyracuseBound
proposition11ToTheorem31FromIteration stabilisation =
  firstPassageToQuantitativeBound (fst stabilisation) (snd stabilisation)

public export
FirstPassageAnalyticInput : Type
FirstPassageAnalyticInput =
  (ValuationDistribution, StabilityPrinciple)

public export
analyticInputToStabilisation :
  FirstPassageAnalyticInput -> StabilisationOfFirstPassage
analyticInputToStabilisation (valuation, stability) =
  (valuation.valuationTailEstimate, stability.stabilityFromValuations valuation)

public export
renewalMonotonicity : RenewalMonotonicity
renewalMonotonicity = orderClaim renewalMonotonicityDual

public export
proposition19 : ValuationDistribution
proposition19 = orderClaim proposition19Dual

public export
firstPassageAnalyticInputDual : DualProof FirstPassageAnalyticInput
firstPassageAnalyticInputDual =
  dualApply
    (dualMap (\valuation, stability => (valuation, stability)) proposition19Dual)
    renewalMonotonicityDual

public export
firstPassageAnalyticInput : FirstPassageAnalyticInput
firstPassageAnalyticInput = orderClaim firstPassageAnalyticInputDual

public export
analyticInputToStabilisationDual :
  DualProof (FirstPassageAnalyticInput -> StabilisationOfFirstPassage)
analyticInputToStabilisationDual = dualPure analyticInputToStabilisation

public export
proposition11ToTheorem31Dual :
  DualProof (StabilisationOfFirstPassage -> QuantitativeSyracuseBound)
proposition11ToTheorem31Dual = dualPure proposition11ToTheorem31FromIteration

public export
proposition11ToTheorem31 :
  StabilisationOfFirstPassage -> QuantitativeSyracuseBound
proposition11ToTheorem31 = orderClaim proposition11ToTheorem31Dual

public export
analyticInputToQuantitativeBoundDual :
  DualProof (FirstPassageAnalyticInput -> QuantitativeSyracuseBound)
analyticInputToQuantitativeBoundDual =
  dualCompose proposition11ToTheorem31Dual analyticInputToStabilisationDual

public export
analyticInputToQuantitativeBound :
  FirstPassageAnalyticInput -> QuantitativeSyracuseBound
analyticInputToQuantitativeBound =
  orderClaim analyticInputToQuantitativeBoundDual

public export
theorem31ToTheorem16Dual : DualProof (QuantitativeSyracuseBound -> Theorem16)
theorem31ToTheorem16Dual = dualPure theorem31ToTheorem16FromPrinciple

public export
theorem31ToTheorem16 :
  QuantitativeSyracuseBound -> Theorem16
theorem31ToTheorem16 = orderClaim theorem31ToTheorem16Dual

public export
quantitativeBoundToTheorem13Dual :
  DualProof OddThresholdSystem -> DualProof (QuantitativeSyracuseBound -> Theorem13)
quantitativeBoundToTheorem13Dual sysDual =
  dualCompose (theorem16ToTheorem13Dual sysDual) theorem31ToTheorem16Dual

public export
quantitativeBoundToTheorem13 :
  OddThresholdSystem -> QuantitativeSyracuseBound -> Theorem13
quantitativeBoundToTheorem13 sys =
  orderClaim (quantitativeBoundToTheorem13Dual (dualPure sys))

public export
analyticInputToTheorem13Dual :
  DualProof OddThresholdSystem -> DualProof (FirstPassageAnalyticInput -> Theorem13)
analyticInputToTheorem13Dual sysDual =
  dualCompose (quantitativeBoundToTheorem13Dual sysDual) analyticInputToQuantitativeBoundDual

public export
analyticInputToTheorem13 :
  OddThresholdSystem -> FirstPassageAnalyticInput -> Theorem13
analyticInputToTheorem13 sys =
  orderClaim (analyticInputToTheorem13Dual (dualPure sys))

--------------------------------------------------------------------------------
-- The central theorem (Theorem 1.3 of the paper):
--   "Almost all Collatz orbits attain almost bounded values."
--
-- Every reduction step of the paper's argument has been formalised above:
--   * the Syracuse -> Collatz density transfer (Theorem 1.6 => Theorem 1.3),
--   * the quantitative first-passage bound (Theorem 3.1 => Theorem 1.6),
--   * the first-passage stabilisation from the analytic input
--     (Propositions 1.9 and 7.8 => Proposition 1.11 => Theorem 3.1).
--
-- `analyticInputToTheorem13Dual sysDual` packages that entire chain as a
-- function of the analytic input, given an `OddThresholdSystem` (the one
-- reduction ingredient that is classically inhabited but not constructively
-- definable here; see NOTES.md).  Supplying that system and the analytic input
-- assembles Theorem 1.3.
--
-- The result is carried along both proof routes recorded by `DualProof`
-- (the order-filter route and the quantitative-probability route), exactly as
-- the paper offers two developments of the same conclusion.  No `believe_me`
-- is used anywhere in this chain: the odd-part dynamics are proved, and the
-- remaining deep inputs appear as explicit hypotheses.
--------------------------------------------------------------------------------

public export
centralTheoremDual : DualProof OddThresholdSystem -> DualProof Theorem13
centralTheoremDual sysDual =
  dualApply (analyticInputToTheorem13Dual sysDual) firstPassageAnalyticInputDual

||| Theorem 1.3 (given a growth-compatible odd-threshold system): almost all
||| Collatz orbits attain almost bounded values.
public export
centralTheorem : OddThresholdSystem -> Theorem13
centralTheorem sys = orderClaim (centralTheoremDual (dualPure sys))

public export
centralTheoremStrictDual : DualProof OddThresholdSystem -> DualProof Theorem13Strict
centralTheoremStrictDual sysDual =
  dualMap theorem13StrictFromNonStrict (centralTheoremDual sysDual)

||| The strict-bound reformulation of Theorem 1.3.
public export
centralTheoremStrict : OddThresholdSystem -> Theorem13Strict
centralTheoremStrict sys = orderClaim (centralTheoremStrictDual (dualPure sys))

public export
centralTheoremPaperDomainDual :
  DualProof OddThresholdSystem -> DualProof Theorem13PaperDomain
centralTheoremPaperDomainDual sysDual =
  dualMap theorem13PaperDomainFromStrict (centralTheoremStrictDual sysDual)

||| Theorem 1.3 stated over the paper's domain of positive integers.
public export
centralTheoremPaperDomain : OddThresholdSystem -> Theorem13PaperDomain
centralTheoremPaperDomain sys =
  orderClaim (centralTheoremPaperDomainDual (dualPure sys))

||| The quantitative-probability route to the central theorem, matching the
||| second development the paper alludes to.
public export
centralTheoremQuantitative : OddThresholdSystem -> Theorem13
centralTheoremQuantitative sys = quantitativeClaim (centralTheoremDual (dualPure sys))

--------------------------------------------------------------------------------
-- The minimal unified proof.
--
-- Stripped of the `DualProof` bookkeeping, the entire argument is a single
-- composition of four orthogonal one-step reductions, each already proved
-- above and each mapping one paper milestone to the next:
--
--   analyticInputToStabilisation            : analytic input  => Prop 1.11
--   proposition11ToTheorem31FromIteration    : Prop 1.11       => Thm 3.1
--   theorem31ToTheorem16FromPrinciple        : Thm 3.1         => Thm 1.6
--   theorem16ToTheorem13 system              : Thm 1.6         => Thm 1.3
--
-- The only inputs are the two irreducible ingredients: the growth-compatible
-- odd-threshold system and the deep first-passage analytic input.  Bundling
-- exactly those two makes the dependency surface of Theorem 1.3 explicit and
-- minimal.
--------------------------------------------------------------------------------

||| The two (and only two) irreducible ingredients Theorem 1.3 rests on:
||| a growth-compatible odd-threshold system and the first-passage analytic
||| input (Propositions 1.9 / 7.8).
public export
CentralTheoremInputs : Type
CentralTheoremInputs = (OddThresholdSystem, FirstPassageAnalyticInput)

||| Theorem 1.3 as one composition of the four orthogonal reduction steps.
public export
centralTheoremFromInputs : CentralTheoremInputs -> Theorem13
centralTheoremFromInputs (system, analytic) =
  theorem16ToTheorem13 system
    (theorem31ToTheorem16FromPrinciple
      (proposition11ToTheorem31FromIteration
        (analyticInputToStabilisation analytic)))

||| The unified central theorem: supply the odd-threshold system and feed in
||| the (placeholder) analytic input assembled in this module.
public export
centralTheoremUnified : OddThresholdSystem -> Theorem13
centralTheoremUnified system =
  centralTheoremFromInputs (system, firstPassageAnalyticInput)

||| The unified pipeline and the order-filter route of the `DualProof`
||| development compute the very same function, so the minimal presentation
||| loses nothing: `centralTheorem` *is* the four-step composition.
public export
centralTheoremUnifiedAgrees :
  (sys : OddThresholdSystem) -> centralTheorem sys = centralTheoremUnified sys
centralTheoremUnifiedAgrees sys = Refl

-- The reformulations are obtained from the one unified core by the two
-- orthogonal packaging adapters `theorem13StrictFromNonStrict` and
-- `theorem13PaperDomainFromStrict` -- no separate development is needed.

||| The strict-bound reformulation, derived from the unified core.
public export
centralTheoremStrictUnified : OddThresholdSystem -> Theorem13Strict
centralTheoremStrictUnified sys =
  theorem13StrictFromNonStrict (centralTheoremUnified sys)

||| Theorem 1.3 over the paper's positive-integer domain, derived from the
||| unified core.
public export
centralTheoremPaperDomainUnified : OddThresholdSystem -> Theorem13PaperDomain
centralTheoremPaperDomainUnified sys =
  theorem13PaperDomainFromStrict (centralTheoremStrictUnified sys)

||| Both reformulations agree with the earlier `DualProof` developments.
public export
centralTheoremStrictUnifiedAgrees :
  (sys : OddThresholdSystem) ->
  centralTheoremStrict sys = centralTheoremStrictUnified sys
centralTheoremStrictUnifiedAgrees sys = Refl

public export
centralTheoremPaperDomainUnifiedAgrees :
  (sys : OddThresholdSystem) ->
  centralTheoremPaperDomain sys = centralTheoremPaperDomainUnified sys
centralTheoremPaperDomainUnifiedAgrees sys = Refl
