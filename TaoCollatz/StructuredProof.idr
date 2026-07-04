module TaoCollatz.StructuredProof

-- A single, self-contained *structured* presentation of the whole proof of the
-- central theorem (Theorem 1.3 of `taocollatz.pdf`).
--
-- Every reduction step of the paper's argument is already proved elsewhere in
-- the development; this module bundles the entire argument into one explicit
-- pipeline object (`CentralTheoremDerivation`) whose four fields are exactly the
-- four orthogonal reduction morphisms, and runs it end to end.  The odd-part
-- density transfer used here is the *unconditional* one
-- (`theorem16ToTheorem13Constructive`), so the derivation depends on exactly one
-- irreducible ingredient: the deep first-passage analytic input (Props. 1.9 /
-- 7.8).  That single dependency is made explicit as `theOnlyRemainingInput`.
--
-- No `believe_me`, no axioms, no holes; the pipeline is a total function and its
-- agreement with the previously assembled central theorems is proved by `Refl`.

import TaoCollatz.Core
import TaoCollatz.Dual
import TaoCollatz.Dynamics
import TaoCollatz.Large
import TaoCollatz.PaperInterfaces
import TaoCollatz.PaperAssumptions
import TaoCollatz.Dependencies
import TaoCollatz.OddThreshold

%default total

--------------------------------------------------------------------------------
-- The reduction pipeline as an explicit object.
--------------------------------------------------------------------------------

||| The four orthogonal reduction steps of the central theorem, each a proved
||| morphism between two paper milestones:
|||
|||   stepStabilisation : analytic input       => Prop. 1.11 (stabilisation)
|||   stepTheorem31     : Prop. 1.11            => Thm 3.1  (quantitative bound)
|||   stepTheorem16     : Thm 3.1               => Thm 1.6  (Syracuse density)
|||   stepTheorem13     : Thm 1.6               => Thm 1.3  (Collatz density)
public export
record CentralTheoremDerivation where
  constructor MkCentralTheoremDerivation
  stepStabilisation : FirstPassageAnalyticInput -> StabilisationOfFirstPassage
  stepTheorem31     : StabilisationOfFirstPassage -> QuantitativeSyracuseBound
  stepTheorem16     : QuantitativeSyracuseBound -> Theorem16
  stepTheorem13     : Theorem16 -> Theorem13

||| Run the pipeline from the analytic input to Theorem 1.3.
public export
runDerivation :
  CentralTheoremDerivation -> FirstPassageAnalyticInput -> Theorem13
runDerivation d analytic =
  d.stepTheorem13
    (d.stepTheorem16
      (d.stepTheorem31
        (d.stepStabilisation analytic)))

||| The standard derivation: the four proved reduction morphisms, using the
||| *unconditional* odd-part density transfer (the odd-threshold system is
||| constructed, not assumed).
public export
standardDerivation : CentralTheoremDerivation
standardDerivation =
  MkCentralTheoremDerivation
    analyticInputToStabilisation
    proposition11ToTheorem31FromIteration
    theorem31ToTheorem16FromPrinciple
    theorem16ToTheorem13Constructive

--------------------------------------------------------------------------------
-- The one remaining irreducible ingredient.
--------------------------------------------------------------------------------

||| The single deep input the whole proof still rests on: the first-passage
||| analytic estimate of the paper (Proposition 1.9's valuation tail estimate
||| together with Proposition 7.8's renewal/stability estimate).  Everything
||| else in the derivation is a proved, total reduction.
public export
theOnlyRemainingInput : Type
theOnlyRemainingInput = FirstPassageAnalyticInput

--------------------------------------------------------------------------------
-- The structured central theorem.
--------------------------------------------------------------------------------

||| Theorem 1.3, obtained by running the standard derivation on the analytic
||| input assembled in `TaoCollatz.Dependencies`.
public export
structuredCentralTheorem : Theorem13
structuredCentralTheorem =
  runDerivation standardDerivation firstPassageAnalyticInput

||| The structured pipeline computes the very same function as the previously
||| assembled unconditional central theorem: the structured presentation loses
||| nothing.
public export
structuredAgreesWithUnconditional :
  StructuredProof.structuredCentralTheorem = OddThreshold.centralTheoremUnconditional
structuredAgreesWithUnconditional = Refl

||| The strict-bound reformulation, from the structured core.
public export
structuredCentralTheoremStrict : Theorem13Strict
structuredCentralTheoremStrict =
  theorem13StrictFromNonStrict structuredCentralTheorem

||| Theorem 1.3 over the paper's positive-integer domain, from the structured
||| core.
public export
structuredCentralTheoremPaperDomain : Theorem13PaperDomain
structuredCentralTheoremPaperDomain =
  theorem13PaperDomainFromStrict structuredCentralTheoremStrict

||| A conditional presentation: for *any* derivation and *any* supplied analytic
||| input, Theorem 1.3 follows.  This isolates the exact logical shape of the
||| result — the whole content is the four reduction morphisms plus one input.
public export
centralTheoremFromDerivationAndInput :
  (d : CentralTheoremDerivation) ->
  FirstPassageAnalyticInput ->
  Theorem13
centralTheoremFromDerivationAndInput d analytic = runDerivation d analytic
