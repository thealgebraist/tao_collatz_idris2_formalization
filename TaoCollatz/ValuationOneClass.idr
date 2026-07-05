module TaoCollatz.ValuationOneClass

-- Genuine, fully-proved *exact* Syracuse valuation on the residue class
-- `n ≡ 3 (mod 4)`.
--
-- This is the base atom of the geometric Syracuse-valuation distribution: the
-- event `a = 1`.  On the arithmetic form `n = 4t+3`,
--
--     3(4t+3)+1 = 12t+10 = 2 * (6t+5),   6t+5 odd,
--
-- so `syrValuation (4t+3) = 1` (an instance of the general exact-valuation
-- reader `ValuationExact.syrValuationFromFactor`, exactly as
-- `ValuationTwoClass.valuationTwoOnClass1mod8` handles `a = 2`).
--
-- We also define the period-4 predicate `res3mod4`, prove its periodicity and
-- one-hit-per-period certificate, and hence its exact natural density `1/4`
-- (`countRes3mod4`).  Among the odd numbers this is density `1/2`, i.e.
-- `P(a = 1) = 1/2`, the leading term of the geometric law
-- `P(a = k) = 2^{-k}` (items C1/C2 of `REMAINING_WORK.md`).  Together with
-- `res1mod4` (`a >= 2`, density `1/4`) this gives the exact first-step split of
-- the odd numbers into `{a = 1}` and `{a >= 2}`, each of density `1/4`.
--
-- Everything here is real mathematics: `%default total`, no placeholders, no
-- `believe_me`, no axioms, no holes.

import TaoCollatz.Core
import TaoCollatz.Dynamics
import TaoCollatz.TwoAdic
import TaoCollatz.SyracuseStructure
import TaoCollatz.ValuationExact
import TaoCollatz.ValuationBounds
import TaoCollatz.ValuationTwoClass
import TaoCollatz.Density
import TaoCollatz.PeriodicCount
import TaoCollatz.DisjointDensity
import TaoCollatz.GoodStepDensity
import Data.Nat

%default total

--------------------------------------------------------------------------------
-- Odd cofactor `6t+5` in the factorisation `3(4t+3)+1 = 2 * (6t+5)`.
--------------------------------------------------------------------------------

||| `6t+5` is odd -- the odd cofactor `q` in `3(4t+3)+1 = 2^1 * (6t+5)`.
||| (Reuses `ValuationTwoClass.evenMult6`.)
public export
oddSixTPlus5 : (t : Nat) -> isEven (plus (mult 6 t) 5) = False
oddSixTPlus5 t =
  trans (cong isEven (plusCommutative (mult 6 t) 5))
        (isEvenPlusEven 5 (mult 6 t) (evenMult6 t))

--------------------------------------------------------------------------------
-- The 2-adic factorisation `3(4t+3)+1 = 2^1 * (6t+5)`.
--------------------------------------------------------------------------------

||| `3(4t+3)+1 = 12t + 10`.
public export
class3mod4Lhs :
  (t : Nat) -> plus (mult 3 (plus (mult 4 t) 3)) 1 = plus (mult 12 t) 10
class3mod4Lhs t =
  rewrite multDistributesOverPlusRight 3 (mult 4 t) 3 in
  rewrite multAssociative 3 4 t in
  sym (plusAssociative (mult 12 t) 9 1)

||| `2 * (6t+5) = 12t + 10`.
public export
class3mod4Rhs :
  (t : Nat) -> mult (pow2 1) (plus (mult 6 t) 5) = plus (mult 12 t) 10
class3mod4Rhs t =
  rewrite multDistributesOverPlusRight 2 (mult 6 t) 5 in
  rewrite multAssociative 2 6 t in
  Refl

||| The clean factorisation feeding the general lemma:
||| `3(4t+3)+1 = 2^1 * (6t+5)`.
public export
class3mod4Factor :
  (t : Nat) ->
  plus (mult 3 (plus (mult 4 t) 3)) 1 = mult (pow2 1) (plus (mult 6 t) 5)
class3mod4Factor t = trans (class3mod4Lhs t) (sym (class3mod4Rhs t))

--------------------------------------------------------------------------------
-- The exact valuation on the class `n = 4t+3`.
--------------------------------------------------------------------------------

||| The Syracuse valuation is **exactly one** on the residue class
||| `n ≡ 3 (mod 4)`: `syrValuation (4t+3) = 1`.  Immediate from the general
||| `syrValuationFromFactor` and the factorisation above.
public export
valuationOneOnClass3mod4 :
  (t : Nat) -> syrValuation (plus (mult 4 t) 3) = 1
valuationOneOnClass3mod4 t =
  syrValuationFromFactor (plus (mult 4 t) 3) 1 (plus (mult 6 t) 5)
    (oddSixTPlus5 t) (class3mod4Factor t)

--------------------------------------------------------------------------------
-- The period-4 residue predicate `n ≡ 3 (mod 4)` and its density.
--------------------------------------------------------------------------------

||| `n ≡ 3 (mod 4)`.
public export
res3mod4 : Nat -> Bool
res3mod4 Z = False
res3mod4 (S Z) = False
res3mod4 (S (S Z)) = False
res3mod4 (S (S (S Z))) = True
res3mod4 (S (S (S (S k)))) = res3mod4 k

public export
res3mod4Periodic : (n : Nat) -> res3mod4 (plus n 4) = res3mod4 n
res3mod4Periodic Z = Refl
res3mod4Periodic (S Z) = Refl
res3mod4Periodic (S (S Z)) = Refl
res3mod4Periodic (S (S (S Z))) = Refl
res3mod4Periodic (S (S (S (S k)))) = res3mod4Periodic k

public export
countRes3mod4PerPeriod : count (\i => res3mod4 i) 4 = 1
countRes3mod4PerPeriod = Refl

||| `n ≡ 3 (mod 4)` has natural density exactly `1/4`: `q` members over `q`
||| periods.  Among the odd numbers this is density `1/2`, i.e. `P(a = 1) = 1/2`.
public export
countRes3mod4 : (q : Nat) -> count (\i => res3mod4 i) (mult q 4) = q
countRes3mod4 q =
  singleHitDensity (\i => res3mod4 i) 4 (\n => res3mod4Periodic n)
    countRes3mod4PerPeriod q

--------------------------------------------------------------------------------
-- Exact valuation-one on the residue predicate.
--------------------------------------------------------------------------------

||| If `res3mod4 n` holds then `n = 4t+3` for some `t`.
public export
res3mod4Form :
  (n : Nat) -> res3mod4 n = True -> (t : Nat ** n = plus (mult 4 t) 3)
res3mod4Form Z h = absurd h
res3mod4Form (S Z) h = absurd h
res3mod4Form (S (S Z)) h = absurd h
res3mod4Form (S (S (S Z))) _ = (0 ** Refl)
res3mod4Form (S (S (S (S k)))) h =
  let (t ** eq) = res3mod4Form k h in
  (S t **
    trans (cong (plus 4) eq)
      (trans (plusAssociative 4 (mult 4 t) 3)
             (cong (\z => plus z 3) (sym (multRightSuccPlus 4 t)))))

||| The Syracuse valuation is exactly one on every point of the density-`1/4`
||| residue class `n ≡ 3 (mod 4)`.
public export
valuationOneWhenRes3mod4 :
  (n : Nat) -> res3mod4 n = True -> syrValuation n = 1
valuationOneWhenRes3mod4 n h =
  let (t ** eq) = res3mod4Form n h in
  rewrite eq in valuationOneOnClass3mod4 t

--------------------------------------------------------------------------------
-- Concrete sanity checks.
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- The exact first-step valuation partition of the odd numbers.
--
-- The odd numbers split disjointly into `{a = 1}` (`res3mod4`) and `{a >= 2}`
-- (`res1mod4`), each of natural density `1/4`.  This is the exact base level of
-- the geometric Syracuse-valuation distribution: `P(a = 1) = P(a >= 2) = 1/2`
-- among the odd numbers.
--------------------------------------------------------------------------------

||| `res3mod4` (`a = 1`) and `res1mod4` (`a >= 2`) are disjoint.
public export
res3res1Disjoint : (n : Nat) -> res3mod4 n = True -> res1mod4 n = False
res3res1Disjoint Z h = absurd h
res3res1Disjoint (S Z) h = absurd h
res3res1Disjoint (S (S Z)) h = absurd h
res3res1Disjoint (S (S (S Z))) _ = Refl
res3res1Disjoint (S (S (S (S k)))) h = res3res1Disjoint k h

||| Pointwise: `n ≡ 3 (mod 4)` or `n ≡ 1 (mod 4)` iff `n` is odd.
public export
res34UnionIsOdd :
  (n : Nat) -> (res3mod4 n || res1mod4 n) = isOddIndex n
res34UnionIsOdd Z = Refl
res34UnionIsOdd (S Z) = Refl
res34UnionIsOdd (S (S Z)) = Refl
res34UnionIsOdd (S (S (S Z))) = Refl
res34UnionIsOdd (S (S (S (S k)))) = res34UnionIsOdd k

||| Over `q` periods of length 4, the odd numbers split exactly into the two
||| valuation classes `{a = 1}` and `{a >= 2}`.
public export
oddValuationSplitDecomp :
  (q : Nat) ->
  count (\i => isOddIndex i) (mult q 4)
    = plus (count (\i => res3mod4 i) (mult q 4))
           (count (\i => res1mod4 i) (mult q 4))
oddValuationSplitDecomp q =
  trans
    (sym (countExt (\i => res3mod4 i || res1mod4 i) (\i => isOddIndex i)
            (\i => res34UnionIsOdd i) (mult q 4)))
    (countDisjoint (\i => res3mod4 i) (\i => res1mod4 i)
       res3res1Disjoint (mult q 4))

||| The exact count: over `q` periods there are `q + q = 2q` odd numbers, split
||| as `q` with `a = 1` and `q` with `a >= 2` (density `1/2 = 1/4 + 1/4`).
public export
oddValuationSplitCount :
  (q : Nat) -> count (\i => isOddIndex i) (mult q 4) = plus q q
oddValuationSplitCount q =
  trans (oddValuationSplitDecomp q)
        (rewrite countRes3mod4 q in rewrite countGoodResidues q in Refl)

--------------------------------------------------------------------------------
-- Concrete sanity checks.
--------------------------------------------------------------------------------

||| `t = 0`: `n = 3`, `3*3+1 = 10 = 2*5`, valuation one.
public export
valuationOneThree : syrValuation 3 = 1
valuationOneThree = valuationOneOnClass3mod4 0

||| `t = 1`: `n = 7`, `3*7+1 = 22 = 2*11`, valuation one.
public export
valuationOneSeven : syrValuation 7 = 1
valuationOneSeven = valuationOneOnClass3mod4 1

public export
valuationOneSevenFromResidue : syrValuation 7 = 1
valuationOneSevenFromResidue = valuationOneWhenRes3mod4 7 Refl
