module TaoCollatz.HoleProof

-- The "theorem-hole" presentation of the central theorem, with the single deep
-- analytic gate now **split into eight explicit steps**.
--
-- Earlier modules carry the central theorem as a *function of an explicit
-- hypothesis*: `theorem13GenuineFromSyracuse : SyracuseDensityControl ->
-- Theorem13Genuine`.  That keeps everything honest (the deep analytic content is
-- a named parameter, not fabricated), but the main theorem is never exhibited as
-- a *closed* term -- it is only ever "provable from a hypothesis".
--
-- This module adopts the requested strategy: state the genuine, closed main
-- theorem as a top-level definition and reduce the remaining analytic content to
-- a chain of eight named steps `step1 .. step8`, each with its *real*
-- mathematical type (nothing is weakened to `Unit`/`True`).  The gate
-- `assembleSyracuseGate` is now the composite `step8 . step7 . ... . step1`.
--
--   * `step1` is **proved outright** (no hole): it extracts, from the already
--     proved distributional ingredients, the strict per-step Syracuse
--     contraction `E[a] >= 8/5` together with the *strict* growth comparison
--     `3^5 < 2^8`.
--   * `step2`, `step3`, `step5`, `step8` are now **proved** as well.  `step4`,
--     `step6`, `step7` remain the analytic content, left as explicit Idris
--     **holes** (`?...`).  A hole is the honest machine-checked
--     marker of "this exact, genuinely-typed goal is not yet proved": the file
--     type-checks and builds, every step below has its *real* mathematical
--     type, and each intermediate statement is a genuine, non-vacuous, *true*
--     proposition (the milestones of Tao's density-one first-passage argument).
--
-- The eight steps mirror the structure of Tao's proof of the density form of
-- Theorem 1.6 (`SyracuseDensityControl`):
--
--   1. `StrictContraction`        -- per-step drift `E[a] >= 8/5` and `3^5 < 2^8`.
--   2. `IteratedGrowth`           -- the deterministic growth side `3^{5k} <= 2^{8k}`.
--   3. `ExactAffineDynamics`      -- the exact affine backbone
--                                    `2^{S_n(x)} * Syr^n(x) = 3^n * x + c`.
--   4. `ValuationLowerBoundDensity`-- large-deviation drift: for a.e. odd `y`,
--                                    arbitrarily late `n` with `S_n(y) >= (8/5)n`.
--   5. `ContractionDominatesDensity`-- combine 2 & 4: for a.e. `y`, eventually
--                                    `3^n * f(y) <= 2^{S_n(y)}`.
--   6. `TypicalDescentDensity`    -- combine 3 & 5: a density-one set of odd
--                                    starts whose Syracuse orbit drops below the
--                                    starting value.
--   7. `OddDensityControl`        -- iterate 6 to first-passage below an arbitrary
--                                    height `f -> infinity` on the odd domain.
--   8. `SyracuseDensityControl`   -- transfer 7 along the odd-part map to the
--                                    positive-integer domain (the gate itself).
--
-- The genuine distributional ingredients that *are* already proved elsewhere in
-- this development are threaded in as real (hole-free) inputs:
--
--   * `SyracuseStepContraction` -- the mean-valuation drift `E[a] >= 8/5`
--     together with the growth comparison `3^5 <= 2^8` (`ContractionDrift`);
--   * `FirstPassageTailEstimate` -- the exact 2-adic valuation survival function
--     `mu({a >= j+1}) + 1 = 2^{n-j}` (`GenuineEstimates` / `ValuationTail`);
--   * `PositiveDensityDescentSet` -- the positive-density set of one-step
--     Syracuse descenders `n = 1 (mod 4)` (`DescentSetPositive`).

import TaoCollatz.Core
import TaoCollatz.Dynamics
import TaoCollatz.Large
import TaoCollatz.Density
import TaoCollatz.CarrierDensity
import TaoCollatz.TwoAdic
import TaoCollatz.SyracuseStructure
import TaoCollatz.MinimalProof
import TaoCollatz.PaperInterfaces
import TaoCollatz.GenuineEstimates
import TaoCollatz.ContractionDrift
import TaoCollatz.DescentSetPositive
import TaoCollatz.StepArith
import TaoCollatz.StepArith2
import TaoCollatz.OddToPosTransfer
import TaoCollatz.Pieces64
import TaoCollatz.Large
import Data.Nat

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
-- Auxiliary quantities used to state the eight steps.
--------------------------------------------------------------------------------

||| `natPow b k = b^k` is provided by `TaoCollatz.StepArith`.
|||
||| `syrValSum n x` is the sum of the first `n` Syracuse 2-adic valuations along
||| the orbit of `x`: `a_1(x) + a_2(x) + ... + a_n(x)`, where `a_{i+1}` is the
||| valuation read off `3 * Syr^i(x) + 1`.  This is the exponent that appears in
||| the exact affine relation `2^{S_n(x)} * Syr^n(x) = 3^n * x + c`.  It is now
||| defined in `TaoCollatz.Pieces64` (`syrValSum`) and imported here.

--------------------------------------------------------------------------------
-- Step 1 target: the strict per-step Syracuse contraction.
--------------------------------------------------------------------------------

||| The genuine per-step contraction, in *strict* form: the mean 2-adic
||| valuation drift `E[a] >= 8/5` (packaged as `SyracuseStepContraction 4`),
||| together with the **strict** growth comparison `3^5 < 2^8` (i.e.
||| `244 <= 256`).  Since `E[a] >= 8/5` gives `2^{5 E[a]} >= 2^8 > 3^5`, the
||| five-step Syracuse growth `3^5` is *strictly* dominated by the five-step
||| contraction, so the per-step multiplicative factor `3 / 2^{E[a]}` is
||| genuinely `< 1`.  This is the quantitative seed of the whole descent.
public export
record StrictContraction where
  constructor MkStrictContraction
  ||| `E[a] >= 8/5` (cross-multiplied) and `3^5 <= 2^8`, at scale 4.
  baseContraction : SyracuseStepContraction 4
  ||| The strict comparison `3^5 < 2^8`, i.e. `244 <= 256`.
  strictGrowth : Leq (S (mult 3 (mult 3 (mult 3 (mult 3 3))))) (pow2 8)

--------------------------------------------------------------------------------
-- The eight intermediate milestone statements.
--------------------------------------------------------------------------------

||| Step 2 -- the deterministic *growth side*: for every number of five-step
||| blocks `k`, the growth `3^{5k}` is dominated by the contraction budget
||| `2^{8k}`.  (True, and provable from `StrictContraction` by monotonicity of
||| powers; it isolates the purely arithmetic half of the descent.)
public export
IteratedGrowth : Type
IteratedGrowth = (k : Nat) -> Leq (natPow 3 (mult 5 k)) (pow2 (mult 8 k))

||| Steps 3-7 refer to the milestone statement types `ExactAffineDynamics`,
||| `ValuationLowerBoundDensity`, `ContractionDominatesDensity`,
||| `TypicalDescentDensity` and `OddDensityControl`.  These are now defined in
||| `TaoCollatz.Pieces64` (together with the 64-piece decomposition of the
||| remaining analytic content) and imported here.

--------------------------------------------------------------------------------
-- Step 1, proved outright.
--------------------------------------------------------------------------------

||| **Step 1 (proved).**  From the bundled analytic inputs, extract the strict
||| per-step Syracuse contraction: the mean-valuation drift `E[a] >= 8/5`
||| (reused verbatim from the input) together with the strict growth comparison
||| `3^5 < 2^8` (a genuine, machine-checked numeric fact, `244 <= 256`).
export
step1 : AnalyticFirstPassageInputs -> StrictContraction
step1 inputs =
  MkStrictContraction
    (stepContraction inputs)
    (leqPlusExtraLeft 12 (S (mult 3 (mult 3 (mult 3 (mult 3 3))))))

--------------------------------------------------------------------------------
-- Steps 2..8, the remaining analytic content, as explicit holes.
--------------------------------------------------------------------------------

||| **Step 2.**  Deterministic growth side `3^{5k} <= 2^{8k}` from the strict
||| per-step contraction.
export
step2 : StrictContraction -> IteratedGrowth
step2 sc =
  iteratedGrowthProof
    (leqTrans (leqSuccRightLocal (natPow 3 5)) (strictGrowth sc))

||| The exact affine backbone, proved directly by induction on the number of
||| Syracuse steps.  The base case is `2^0 * x = 3^0 * x + 0`; the inductive
||| step feeds the one-step factorisation `3 * (oddSize x) + 1 =
||| oddSize(Syr x) * 2^{a}` (`syrFactorization`) through the induction
||| hypothesis for `Syr x`, accumulating the affine correction `c`.
export
affineBackbone : ExactAffineDynamics
affineBackbone x Z =
  (Z ** sym (plusZeroRightNeutral (mult (natPow 3 Z) (oddSize x))))
affineBackbone (MkOddPos m) (S k) =
  let v : Nat
      v = syrValuation m
      ih : (c : Nat **
              mult (pow2 (syrValSum k (Syr (MkOddPos m))))
                   (oddSize (iter k Syr (Syr (MkOddPos m))))
              = plus (mult (natPow 3 k) (oddSize (Syr (MkOddPos m)))) c)
      ih = affineBackbone (Syr (MkOddPos m)) k
      c' : Nat
      c' = fst ih
      eqIH : mult (pow2 (syrValSum k (Syr (MkOddPos m))))
                  (oddSize (iter k Syr (Syr (MkOddPos m))))
             = plus (mult (natPow 3 k) (oddSize (Syr (MkOddPos m)))) c'
      eqIH = snd ih
      s : Nat
      s = oddValue (Syr (MkOddPos m))
      pk : Nat
      pk = natPow 3 k
      pv : Nat
      pv = pow2 v
      sk : Nat
      sk = syrValSum k (Syr (MkOddPos m))
      w : Nat
      w = oddSize (iter k Syr (Syr (MkOddPos m)))
      e5 : mult pv (mult pk s) = mult pk (mult pv s)
      e5 = mulSwapMid pv pk s
      e6 : mult pv s = plus (mult 3 m) 1
      e6 = trans (multCommutative pv s) (sym (syrFactorization m))
      e9 : mult pk (mult 3 m) = mult (natPow 3 (S k)) m
      e9 = trans (multAssociative pk 3 m)
                 (cong (\z => mult z m) (multCommutative pk 3))
      eqA : mult pv (mult pk s) = plus (mult (natPow 3 (S k)) m) pk
      eqA =
        trans e5
          (trans (cong (\z => mult pk z) e6)
            (trans (multDistributesOverPlusRight pk (mult 3 m) 1)
              (cong2 plus e9 (multOneRightNeutral pk))))
      c : Nat
      c = plus pk (mult pv c')
  in (c **
        trans (cong (\z => mult z w) (pow2AddLocal v sk))
          (trans (sym (multAssociative pv (pow2 sk) w))
            (trans (cong (\z => mult pv z) eqIH)
              (trans (multDistributesOverPlusRight pv (mult pk s) c')
                (trans (cong (\z => plus z (mult pv c')) eqA)
                  (sym (plusAssociative (mult (natPow 3 (S k)) m) pk
                          (mult pv c'))))))))

||| **Step 3.**  The exact affine backbone `2^{S_n(x)} * Syr^n(x) = 3^n x + c`.
export
step3 : IteratedGrowth -> ExactAffineDynamics
step3 _ = affineBackbone

||| **Step 4.**  The large-deviation drift in density form: a.e. odd `y` reaches
||| the `8/5` drift rate arbitrarily late.
export
step4 : ExactAffineDynamics -> ValuationLowerBoundDensity
step4 = piece62_step4

||| **Step 5 (proved).**  Contraction dominates growth on a density-one set.
||| Apply the drift input `vlbd` at the inflated height `g y = 243 * (f y)^5`
||| (still tending to infinity, since `f y <= g y`); on its density-one good set,
||| the returned time `n >= g y` together with the drift `8 n <= 5 * S_n(y)`
||| feeds `contractionArith` to yield `3^n * f(y) <= 2^{S_n(y)}`.
export
step5 : ValuationLowerBoundDensity -> ContractionDominatesDensity
step5 vlbd f fGrows =
  let g : OddPos -> Nat
      g = \y => mult 243 (natPow (f y) 5)
      gGrows : TendsToInfinityOdd g
      gGrows = growthMonotone (\y => fLeqG (f y)) fGrows
  in case vlbd g gGrows of
       (good ** (aa, imp)) =>
         (good **
           (aa,
            \y, gy =>
              case imp y gy of
                (n ** (hge, hdrift)) =>
                  (n ** contractionArith n (f y) (syrValSum n y) hge hdrift)))

||| **Step 6.**  Typical descent below the starting value, density form.
export
step6 : ContractionDominatesDensity -> TypicalDescentDensity
step6 = piece63_step6

||| **Step 7.**  Density-one Syracuse first passage below an arbitrary height on
||| the odd domain.
export
step7 : TypicalDescentDensity -> OddDensityControl
step7 = piece64_step7

||| **Step 8.**  Transfer the odd-domain first passage along the odd-part map to
||| the positive-integer gate `SyracuseDensityControl`.
export
step8 : OddDensityControl -> SyracuseDensityControl
step8 odc = oddToPosTransfer odc

--------------------------------------------------------------------------------
-- The gate as the composite of the eight steps.
--------------------------------------------------------------------------------

||| The remaining deep analytic step, now assembled from the eight steps above.
||| `step1`,`step2`,`step3`,`step5`,`step8` are proved; only `step4`, `step6`,
||| `step7` remain as explicit holes.  Its type is the *genuine*, non-vacuous
||| gate `SyracuseDensityControl`; filling the three remaining holes -- with no
||| other change -- upgrades the closed theorems below to a fully unconditional
||| proof.
export
assembleSyracuseGate : AnalyticFirstPassageInputs -> SyracuseDensityControl
assembleSyracuseGate inputs =
  step8 (step7 (step6 (step5 (step4 (step3 (step2 (step1 inputs)))))))

--------------------------------------------------------------------------------
-- The genuine gate and the closed main theorem.
--------------------------------------------------------------------------------

||| The single analytic gate, obtained by assembling the proved ingredients.
||| Genuinely typed as `SyracuseDensityControl`; its only unfilled dependencies
||| are the holes `step2_rhs .. step8_rhs` above.
export
syracuseDensityControl : SyracuseDensityControl
syracuseDensityControl = assembleSyracuseGate analyticInputs

||| **Theorem 1.3 (genuine natural-density form), as a closed term.** For every
||| height `f -> infinity`, almost every positive integer has a Collatz orbit
||| that eventually drops below `f`.  Proved outright from the gate via the
||| already-proved odd-part orbit simulation; its only unfilled dependencies are
||| the seven step holes above.
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
||| `theorem13` is not a vacuous statement.  (It depends on the same seven step
||| holes as `theorem13` itself.)
export
theorem13HasMember :
  (f : Pos -> Nat) -> TendsToInfinityPos f ->
  (n : Nat ** ColBelow (MkPos n) (f (MkPos n)))
theorem13HasMember f fGrows = theorem13GenuineHasMember theorem13 f fGrows
