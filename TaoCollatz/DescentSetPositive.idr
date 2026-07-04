module TaoCollatz.DescentSetPositive

-- Genuine, fully-proved capstone of this round: a *positive-density* set of odd
-- starting points on each of which one Syracuse step provably descends.
--
-- Everything downstream of the single analytic gate `SyracuseDensityControl`
-- (see `REMAINING_WORK.md`) needs a *large* set of points that reach a value at
-- or below their start.  This module assembles the pieces built in this round
-- into exactly such an object for the elementary "one good step" case:
--
--   * the good-step class `n ≡ 1 (mod 4)` (`res1mod4`) is not negligible
--     (`PositiveDensity.goodStepClassNotNegligible`), so it has positive natural
--     density (in fact `1/4`);
--   * every member `n` of it satisfies `SyrBelow (MkOddPos n) n`, i.e. one
--     Syracuse step reaches a value `<= n` (`GoodStepDensity.familyBelow`).
--
-- Packaged as `goodStepDescentSet : PositiveDensityDescentSet`.  This is the
-- honest elementary core of the first-passage statement; upgrading "positive
-- density" to "density one" (for an arbitrary threshold) is the remaining deep
-- analytic content the gate abstracts.
--
-- Everything here is real mathematics: `%default total`, no placeholders, no
-- `believe_me`, no axioms, no holes.

import TaoCollatz.Core
import TaoCollatz.Dynamics
import TaoCollatz.Density
import TaoCollatz.GoodStepDensity
import TaoCollatz.PositiveDensity
import Data.Nat

%default total

--------------------------------------------------------------------------------
-- Extracting the arithmetic form `4t+1` from the residue predicate.
--------------------------------------------------------------------------------

||| If `res1mod4 n` holds then `n = 4t+1` for some `t`.
public export
res1mod4Form :
  (n : Nat) -> res1mod4 n = True -> (t : Nat ** n = plus (mult 4 t) 1)
res1mod4Form Z h = absurd h
res1mod4Form (S Z) _ = (0 ** Refl)
res1mod4Form (S (S Z)) h = absurd h
res1mod4Form (S (S (S Z))) h = absurd h
res1mod4Form (S (S (S (S k)))) h =
  let (t ** eq) = res1mod4Form k h in
  (S t **
    trans (cong (plus 4) eq)
      (trans (plusAssociative 4 (mult 4 t) 1)
             (cong (\z => plus z 1) (sym (multRightSuccPlus 4 t)))))

--------------------------------------------------------------------------------
-- Every member of the good-step class descends in one step.
--------------------------------------------------------------------------------

||| Every `n ≡ 1 (mod 4)` has a genuine first-passage witness: one Syracuse step
||| reaches a value `<= n`.
public export
descentOnRes1mod4 :
  (n : Nat) -> res1mod4 n = True -> SyrBelow (MkOddPos n) n
descentOnRes1mod4 n h =
  let (t ** eq) = res1mod4Form n h in
  rewrite eq in familyBelow t

--------------------------------------------------------------------------------
-- The packaged positive-density descent set.
--------------------------------------------------------------------------------

||| A set of odd starts that (a) has positive natural density and (b) on which
||| one Syracuse step provably descends.
public export
record PositiveDensityDescentSet where
  constructor MkDescentSet
  member : Nat -> Bool
  notNegligible : Negligible (\i => member i) -> Void
  descends : (n : Nat) -> member n = True -> SyrBelow (MkOddPos n) n

||| The good-step class `n ≡ 1 (mod 4)` realises a positive-density set of
||| one-step Syracuse descenders.
public export
goodStepDescentSet : PositiveDensityDescentSet
goodStepDescentSet =
  MkDescentSet
    (\i => res1mod4 i)
    goodStepClassNotNegligible
    descentOnRes1mod4

--------------------------------------------------------------------------------
-- Concrete sanity checks.
--------------------------------------------------------------------------------

public export
res1mod4NineForm : (t : Nat ** 9 = plus (mult 4 t) 1)
res1mod4NineForm = res1mod4Form 9 Refl

public export
descentOnNine : SyrBelow (MkOddPos 9) 9
descentOnNine = descentOnRes1mod4 9 Refl
