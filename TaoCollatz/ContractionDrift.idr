module TaoCollatz.ContractionDrift

-- Packaging the mean-valuation drift into a single per-step contraction
-- statement.
--
-- `TaoCollatz.ValuationMoment` proves two genuine facts about the 2-adic
-- valuation distribution at every scale `n >= 4`:
--
--   * the drift `8 * mass <= 5 * weightedSum` (`generalDrift`), i.e. the mean
--     valuation `E[a] = weightedSum / mass >= 8/5`;
--   * the growth comparison `3^5 = 243 <= 256 = 2^8` (`growthComparison`), i.e.
--     `log2 3 < 8/5`.
--
-- Together these say the per-step Syracuse multiplicative factor `3 / 2^{E[a]}`
-- is `< 1`: since `E[a] >= 8/5` gives `2^{5 E[a]} >= 2^8`, and `2^8 >= 3^5`, the
-- five-step growth `3^5` is dominated by the five-step contraction `2^{5 E[a]}`.
-- This module bundles the two proofs into one record `SyracuseStepContraction`
-- and derives it at every scale `n >= 4`.
--
-- Everything here is real, total mathematics: `%default total`, no
-- placeholders, no `believe_me`, no axioms, no holes.

import Data.Nat
import TaoCollatz.Core
import TaoCollatz.TwoAdic
import TaoCollatz.Density
import TaoCollatz.FinMeasure
import TaoCollatz.GeometricValuation
import TaoCollatz.ValuationMoment

%default total

||| The two ingredients of the per-step contraction at a given scale `n`,
||| packaged together: the mean-valuation drift and the growth comparison.
public export
record SyracuseStepContraction (n : Nat) where
  constructor MkSyracuseStepContraction
  ||| `E[a] >= 8/5`, in cross-multiplied form.
  meanDrift : Leq (mult 8 (mass (geoValuation n)))
                  (mult 5 (weightedSum (geoValuation n)))
  ||| `3^5 <= 2^8`, i.e. `log2 3 < 8/5`.
  growthDominated : Leq (mult 3 (mult 3 (mult 3 (mult 3 3)))) (pow2 8)

||| The per-step contraction holds at every scale `n = 4 + j`.
public export
syracuseStepContraction :
  (n : Nat) -> (j : Nat) -> n = plus 4 j -> SyracuseStepContraction n
syracuseStepContraction n j eq =
  MkSyracuseStepContraction (generalDrift n j eq) growthComparison

||| Concrete instance at scale 4: mean `26/15 >= 8/5` and `243 <= 256`.
public export
syracuseStepContractionFour : SyracuseStepContraction 4
syracuseStepContractionFour = syracuseStepContraction 4 0 Refl

||| The mean-valuation drift transports up any chain: from `8 mass <= 5 ws` and
||| the growth bound, the five-step contraction beats the five-step growth in the
||| sense that `3^5 <= 2^8` while `2^8` is a lower bound for `2^{5 E[a]}` (the
||| latter recorded implicitly by `meanDrift`).  We expose the crisp corollary
||| that the growth factor is strictly below the `8/5`-scale contraction.
public export
growthBelowContractionScale :
  (n : Nat) -> (j : Nat) -> n = plus 4 j ->
  Leq (mult 3 (mult 3 (mult 3 (mult 3 3)))) (pow2 8)
growthBelowContractionScale n j eq =
  growthDominated (syracuseStepContraction n j eq)
