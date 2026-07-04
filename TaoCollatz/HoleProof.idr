module TaoCollatz.HoleProof

-- The "theorem-hole" presentation of the central theorem.
--
-- Earlier modules carry the central theorem as a *function of an explicit
-- hypothesis*: `theorem13GenuineFromSyracuse : SyracuseDensityControl ->
-- Theorem13Genuine`.  That keeps everything honest (the deep analytic content is
-- an named parameter, not fabricated), but the main theorem is never exhibited
-- as a *closed* term -- it is only ever "provable from a hypothesis".
--
-- This module adopts the requested strategy: state the genuine, closed main
-- theorem as a top-level definition and leave the single remaining analytic
-- content as an explicit Idris **hole** (`?...`).  A hole is the honest
-- machine-checked marker of "this exact, genuinely-typed goal is not yet
-- proved": the file type-checks and builds (`idris2 --build` exits 0), every
-- statement below has its *real* mathematical type (nothing is weakened to
-- `Unit` or `True`), and the precise surface area of what remains is exactly the
-- set of holes.  Filling the holes -- with no other change anywhere -- upgrades
-- these closed terms to a fully unconditional proof.
--
-- The gate is not left as one opaque hole: it is decomposed against the paper's
-- structure.  The genuine distributional ingredients that *are* already proved
-- elsewhere in this development are threaded in as real (hole-free) inputs:
--
--   * `SyracuseStepContraction` -- the mean-valuation drift `E[a] >= 8/5`
--     together with the growth comparison `3^5 <= 2^8` (`ContractionDrift`);
--   * `FirstPassageTailEstimate` -- the exact 2-adic valuation survival function
--     `mu({a >= j+1}) + 1 = 2^{n-j}` (`GenuineEstimates` / `ValuationTail`);
--   * `PositiveDensityDescentSet` -- the positive-density set of one-step
--     Syracuse descenders `n = 1 (mod 4)` (`DescentSetPositive`).
--
-- What is left is exactly the "assembly" step: turning these proved
-- distributional facts into the density-one first-passage control for an
-- arbitrary height `f` (the large-deviation / Fourier heart of the paper,
-- Theorem 1.6 in density form).  That is the single hole `assembleSyracuseGate`.

import TaoCollatz.Core
import TaoCollatz.Dynamics
import TaoCollatz.Large
import TaoCollatz.MinimalProof
import TaoCollatz.PaperInterfaces
import TaoCollatz.GenuineEstimates
import TaoCollatz.ContractionDrift
import TaoCollatz.DescentSetPositive

%default total

--------------------------------------------------------------------------------
-- The proved distributional ingredients, bundled.
--------------------------------------------------------------------------------

||| The genuine, already-proved distributional inputs to the Syracuse
||| first-passage analysis.  Every field is inhabited by real mathematics proved
||| elsewhere in this development -- there is no hole and no placeholder here.
public export
record AnalyticFirstPassageInputs where
  constructor MkAnalyticFirstPassageInputs
  ||| Mean-valuation drift `E[a] >= 8/5` and growth comparison `3^5 <= 2^8`
  ||| at scale 4 (`ContractionDrift.syracuseStepContractionFour`).
  stepContraction : SyracuseStepContraction 4
  ||| Exact 2-adic valuation survival function `mu({a>=j+1}) + 1 = 2^{n-j}`
  ||| (`GenuineEstimates.genuineTailEstimate`, witnessed by `tailGeoValuation`).
  valuationTail : FirstPassageTailEstimate
  ||| Positive-density set of one-step Syracuse descenders `n = 1 (mod 4)`
  ||| (`DescentSetPositive.goodStepDescentSet`).
  positiveDescent : PositiveDensityDescentSet

||| All three ingredients, genuinely constructed -- this term contains no hole.
public export
analyticInputs : AnalyticFirstPassageInputs
analyticInputs =
  MkAnalyticFirstPassageInputs
    syracuseStepContractionFour
    genuineTailEstimate
    goodStepDescentSet

--------------------------------------------------------------------------------
-- The single remaining analytic content, as an explicit hole.
--------------------------------------------------------------------------------

||| The one remaining deep step: assemble the proved distributional ingredients
||| into density-one Syracuse first-passage control for an arbitrary height `f`.
|||
||| This is exactly Tao's Theorem 1.6 in density form (the large-deviation /
||| Fourier heart of the paper): from the per-step contraction and the exact
||| valuation tail, deduce that for every `f -> infinity` almost every positive
||| integer's odd part first-passes below `f`.  Its type is the *genuine*,
||| non-vacuous gate `SyracuseDensityControl`; only its proof term is a hole.
export
assembleSyracuseGate : AnalyticFirstPassageInputs -> SyracuseDensityControl
assembleSyracuseGate inputs = ?assembleSyracuseGate_rhs

--------------------------------------------------------------------------------
-- The genuine gate and the closed main theorem.
--------------------------------------------------------------------------------

||| The single analytic gate, obtained by assembling the proved ingredients.
||| Genuinely typed as `SyracuseDensityControl`; its only unfilled dependency is
||| the hole `assembleSyracuseGate_rhs` above.
export
syracuseDensityControl : SyracuseDensityControl
syracuseDensityControl = assembleSyracuseGate analyticInputs

||| **Theorem 1.3 (genuine natural-density form), as a closed term.** For every
||| height `f -> infinity`, almost every positive integer has a Collatz orbit
||| that eventually drops below `f`.  Proved outright from the gate via the
||| already-proved odd-part orbit simulation; its only unfilled dependency is the
||| single hole above.
export
theorem13 : Theorem13Genuine
theorem13 = theorem13GenuineFromSyracuse syracuseDensityControl

||| Strict-bound form of the closed main theorem.
export
theorem13Strict : Theorem13GenuineStrict
theorem13Strict = theorem13GenuineStrictFromGenuine theorem13

||| Paper-domain (positive-integer) strict form of the closed main theorem.
export
theorem13PaperDomain : Theorem13GenuinePaperDomain
theorem13PaperDomain = theorem13GenuinePaperDomainFromStrict theorem13Strict

--------------------------------------------------------------------------------
-- Non-degeneracy: the closed conclusion has teeth.
--------------------------------------------------------------------------------

||| The density-one good set delivered by the closed main theorem is genuinely
||| non-empty: for every `f -> infinity` there is a concrete positive integer
||| whose Collatz orbit provably drops below `f`.  This certifies that
||| `theorem13` is not a vacuous statement.  (It depends on the same single hole
||| as `theorem13` itself.)
export
theorem13HasMember :
  (f : Pos -> Nat) -> TendsToInfinityPos f ->
  (n : Nat ** ColBelow (MkPos n) (f (MkPos n)))
theorem13HasMember f fGrows = theorem13GenuineHasMember theorem13 f fGrows
