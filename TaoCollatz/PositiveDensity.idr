module TaoCollatz.PositiveDensity

-- Genuine, fully-proved lower bound on density: a *periodic* predicate that is
-- true at least once per period is **not** negligible (it has positive natural
-- density).
--
-- `Density` proves the smallness side (unions of density-zero sets stay
-- density-zero).  For the descent analysis we also need the *largeness* side:
-- the good-step residue class is genuinely non-negligible, so its density
-- cannot be zero.  The engine is elementary: if `p` has period `m` and at least
-- one hit per period (`count p m >= 1`), then over `q` periods it has at least
-- `q` hits (`PeriodicCount.periodicCount`), whereas negligibility at precision
-- `1/(m+1)` would force `q*(m+1) <= q*m`, a contradiction.
--
-- Instantiated at the period-4 good-step class `n ≡ 1 (mod 4)` this shows the
-- set on which one Syracuse step provably descends is *not* density zero.
--
-- Everything here is real mathematics: `%default total`, no placeholders, no
-- `believe_me`, no axioms, no holes.

import TaoCollatz.Core
import TaoCollatz.Dynamics
import TaoCollatz.TwoAdic
import TaoCollatz.Density
import TaoCollatz.PeriodicCount
import TaoCollatz.GoodStepDensity
import Data.Nat

%default total

--------------------------------------------------------------------------------
-- Elementary `Leq` helpers.
--------------------------------------------------------------------------------

||| No successor is `<=` its predecessor.
public export
notLeqSucc : (a : Nat) -> Leq (S a) a -> Void
notLeqSucc Z p = notLeqSZ p
notLeqSucc (S a) (LeqS p) = notLeqSucc a p

||| A positive `Nat` is a successor.
public export
oneLeqToSucc : (x : Nat) -> Leq (S Z) x -> (c : Nat ** x = S c)
oneLeqToSucc Z p = void (notLeqSZ p)
oneLeqToSucc (S c) _ = (c ** Refl)

||| If a predicate has a hit below `m` then `m >= 1`.
public export
countPosImpliesArgPos :
  (p : Nat -> Bool) -> (m : Nat) -> Leq (S Z) (count p m) -> Leq (S Z) m
countPosImpliesArgPos p Z h = void (notLeqSZ h)
countPosImpliesArgPos p (S k) _ = LeqS LeqZ

--------------------------------------------------------------------------------
-- The main lower-bound theorem.
--------------------------------------------------------------------------------

||| A periodic predicate with at least one hit per period is not negligible:
||| its natural density is positive.
public export
periodicPositiveNotNegligible :
  (p : Nat -> Bool) -> (m : Nat) ->
  ((n : Nat) -> p (plus n m) = p n) ->
  Leq (S Z) (count p m) ->
  Negligible p -> Void
periodicPositiveNotNegligible p m period hCount neg =
  let (n0 ** pf) = neg m
      q : Nat
      q = S n0
      x : Nat
      x = mult q m
      mPos : Leq (S Z) m
      mPos = countPosImpliesArgPos p m hCount
      big : Leq n0 x
      big =
        let (m' ** meq) = oneLeqToSucc m mPos in
        leqTrans (leqSuccRight n0)
          (leqCastR (leqSelfMult (S n0) m') (cong (mult (S n0)) (sym meq)))
      cntEq : count p x = mult q (count p m)
      cntEq = periodicCount p m period q
      qLeqCount : Leq q (mult q (count p m))
      qLeqCount =
        let (c ** eq) = oneLeqToSucc (count p m) hCount in
        leqCastR (leqSelfMult q c) (cong (mult q) (sym eq))
      aStep : Leq (mult q (S m)) (mult (mult q (count p m)) (S m))
      aStep = leqMultRight qLeqCount (S m)
      bStep : Leq (mult (mult q (count p m)) (S m)) x
      bStep = leqCastL (cong (\z => mult z (S m)) (sym cntEq)) (pf x big)
      step : Leq (mult q (S m)) x
      step = leqTrans aStep bStep
      h0 : Leq (plus q x) x
      h0 = leqCastL (sym (multRightSuccPlus q m)) step
      contra : Leq (S (plus n0 x)) (plus n0 x)
      contra = leqTrans h0 (leqPlusExtraLeft n0 x)
  in notLeqSucc (plus n0 x) contra

--------------------------------------------------------------------------------
-- The good-step residue class has positive density.
--------------------------------------------------------------------------------

||| The good-step class `n ≡ 1 (mod 4)` (`res1mod4`) is not negligible: the set
||| of odd starts on which one Syracuse step provably descends has positive
||| natural density (in fact density `1/4`, cf. `GoodStepDensity`).
public export
goodStepClassNotNegligible : Negligible (\i => res1mod4 i) -> Void
goodStepClassNotNegligible neg =
  periodicPositiveNotNegligible (\i => res1mod4 i) 4
    (\n => res1mod4Periodic n)
    (rewrite countRes1PerPeriod in leqRefl 1)
    neg
