module TaoCollatz.ValuationDistribution

-- Genuine, fully-proved link between a residue *predicate* and the *exact*
-- Syracuse valuation on it -- the first real slice of the geometric valuation
-- distribution.
--
-- `ResidueClasses.res1mod8` is a period-8 Boolean predicate of density `1/8`.
-- `ValuationTwoClass.valuationTwoOnClass1mod8` pins the valuation to `2` on the
-- arithmetic form `8t+1`.  Here we bridge the two: from `res1mod8 n = True`
-- extract the witness `n = 8t+1` (`res1mod8Form`), hence
--
--     res1mod8 n = True   ==>   syrValuation n = 2 .
--
-- So there is a density-`1/8` set of starting points whose Syracuse step
-- removes *exactly two* factors of two.  This is a genuine, checked instance of
-- the Syracuse valuation random variable taking a prescribed value on a set of
-- prescribed density (items C1/C2 of `REMAINING_WORK.md`).
--
-- Everything here is real mathematics: `%default total`, no placeholders, no
-- `believe_me`, no axioms, no holes.

import TaoCollatz.Core
import TaoCollatz.Dynamics
import TaoCollatz.SyracuseStructure
import TaoCollatz.ValuationTwoClass
import TaoCollatz.ResidueClasses
import TaoCollatz.Density
import Data.Nat

%default total

--------------------------------------------------------------------------------
-- Extracting the arithmetic form from the residue predicate.
--------------------------------------------------------------------------------

||| If `res1mod8 n` holds then `n = 8t+1` for some `t`.
public export
res1mod8Form :
  (n : Nat) -> res1mod8 n = True -> (t : Nat ** n = plus (mult 8 t) 1)
res1mod8Form Z h = absurd h
res1mod8Form (S Z) _ = (0 ** Refl)
res1mod8Form (S (S Z)) h = absurd h
res1mod8Form (S (S (S Z))) h = absurd h
res1mod8Form (S (S (S (S Z)))) h = absurd h
res1mod8Form (S (S (S (S (S Z))))) h = absurd h
res1mod8Form (S (S (S (S (S (S Z)))))) h = absurd h
res1mod8Form (S (S (S (S (S (S (S Z))))))) h = absurd h
res1mod8Form (S (S (S (S (S (S (S (S k)))))))) h =
  let (t ** eq) = res1mod8Form k h in
  (S t **
    trans (cong (plus 8) eq)
      (trans (plusAssociative 8 (mult 8 t) 1)
             (cong (\z => plus z 1) (sym (multRightSuccPlus 8 t)))))

--------------------------------------------------------------------------------
-- Exact valuation on the density-1/8 residue predicate.
--------------------------------------------------------------------------------

||| The Syracuse valuation is exactly two on every point of the density-`1/8`
||| residue class `n ≡ 1 (mod 8)`.
public export
valuationTwoWhenRes1mod8 :
  (n : Nat) -> res1mod8 n = True -> syrValuation n = 2
valuationTwoWhenRes1mod8 n h =
  let (t ** eq) = res1mod8Form n h in
  rewrite eq in valuationTwoOnClass1mod8 t

--------------------------------------------------------------------------------
-- Density of the exact-valuation-2 set.
--------------------------------------------------------------------------------

||| The set on which the Syracuse valuation is exactly two contains the
||| density-`1/8` class `res1mod8`: over `q` periods it has (at least) `q`
||| members, i.e. density `>= 1/8`.
public export
exactValuationTwoDensity :
  (q : Nat) -> count (\i => res1mod8 i) (mult q 8) = q
exactValuationTwoDensity q = countRes1mod8 q

--------------------------------------------------------------------------------
-- Concrete sanity checks.
--------------------------------------------------------------------------------

public export
res1mod8NineForm : (t : Nat ** 9 = plus (mult 8 t) 1)
res1mod8NineForm = res1mod8Form 9 Refl

public export
valuationTwoNineFromResidue : syrValuation 9 = 2
valuationTwoNineFromResidue = valuationTwoWhenRes1mod8 9 Refl
