module TaoCollatz.OrbitValuationTwoStep

-- Genuine, fully-proved *two-step* slice of the Syracuse orbit valuation
-- distribution.
--
-- `TaoCollatz.ValuationDistribution` / `TaoCollatz.ValuationTwoClass` pin down
-- the *first* Syracuse valuation `a_1(y)` on a residue class (density `1/8`:
-- `y = 8t+1 ==> a_1(y) = 2`).  Extending this to the orbit valuation *sum*
-- `S_n(y) = a_1(y) + ... + a_n(y)` requires knowing how the Syracuse map moves
-- residues -- the very content the deep analytic core (Tao's equidistribution)
-- supplies in general.  Here we carry out the first genuine instance of that
-- extension by *two* explicit steps.
--
-- Concretely, on the density-`1/32` residue class `y = 32s+1`:
--
--   * `3(32s+1)+1 = 96s+4 = 2^2 * (24s+1)`, so `a_1(y) = 2` and the odd part is
--     `Syr(y) = 24s+1`;
--   * `24s+1 = 8*(3s)+1`, so `a_2(y) = a_1(Syr(y)) = 2` as well.
--
-- Hence the two-step orbit valuation sum is *exactly* `S_2(y) = 4` on this
-- density-`1/32` set (`twoStepValSum`).  As both valuations are `>= 2`, both
-- Syracuse steps descend, giving a genuine positive-time (time `2`) descent
-- below the start on this class (`twoStepDescent`).
--
-- This is a concrete, checked instance of the Syracuse valuation random
-- variables `a_1, a_2` taking prescribed values along the *orbit* on a set of
-- prescribed density (item C2 of `REMAINING_WORK.md`), the first genuine
-- multi-step slice of the orbit valuation distribution.
--
-- Everything here is real mathematics: `%default total`, no placeholders, no
-- `believe_me`, no `postulate`, no `assert_*`, no `%foreign`, no `idris_crash`,
-- no axioms, no holes.

import Data.Nat
import TaoCollatz.Core
import TaoCollatz.Dynamics
import TaoCollatz.TwoAdic
import TaoCollatz.OddPart
import TaoCollatz.Density
import TaoCollatz.DensityTransfer
import TaoCollatz.SyracuseStructure
import TaoCollatz.ValuationExact
import TaoCollatz.ValuationBounds
import TaoCollatz.ValuationTwoClass
import TaoCollatz.Pieces64

%default total

--------------------------------------------------------------------------------
-- The odd-part of a power-of-two multiple of an odd number.
--------------------------------------------------------------------------------

||| `mult (pow2 0) m = m` (up to the stuck `plus m 0`).
public export
multPow2ZeroEq : (m : Nat) -> mult (pow2 Z) m = m
multPow2ZeroEq m = plusZeroRightNeutral m

||| `mult (pow2 (S k)) m = (mult (pow2 k) m) + (mult (pow2 k) m)`.
public export
multPow2SuccEq :
  (k : Nat) -> (m : Nat) ->
  mult (pow2 (S k)) m = plus (mult (pow2 k) m) (mult (pow2 k) m)
multPow2SuccEq k m = multDistributesOverPlusLeft (pow2 k) (pow2 k) m

||| **The odd-part reader.**  For every `k` and every ODD `m`,
||| `oddFactor (2^k * m) = m`: stripping `2^k` off a power-of-two multiple of an
||| odd number recovers exactly that odd number.  (Companion, at the level of the
||| odd *part*, to `ValuationExact.dropTimePowOdd`, which reads the valuation.)
public export
oddFactorPow2Mult :
  (k : Nat) -> (m : Nat) -> isEven m = False ->
  oddFactor (mult (pow2 k) m) = m
oddFactorPow2Mult Z m hodd =
  trans (cong oddFactor (multPow2ZeroEq m)) (oddFactorFixed m hodd)
oddFactorPow2Mult (S k) m hodd =
  trans (cong oddFactor (multPow2SuccEq k m))
        (trans (oddFactorDoubleEq (mult (pow2 k) m))
               (oddFactorPow2Mult k m hodd))

--------------------------------------------------------------------------------
-- Parity of the linear cofactors `24s+1` and `18s+1`.
--------------------------------------------------------------------------------

||| `24s` is even.
public export
evenMult24 : (s : Nat) -> isEven (mult 24 s) = True
evenMult24 s =
  rewrite multDistributesOverPlusLeft 12 12 s in
  isEvenDoubleTrue (mult 12 s)

||| `24s+1` is odd -- the odd cofactor in `3(32s+1)+1 = 2^2 * (24s+1)`.
public export
oddTwentyFourSPlus1 : (s : Nat) -> isEven (plus (mult 24 s) 1) = False
oddTwentyFourSPlus1 s =
  trans (cong isEven (plusCommutative (mult 24 s) 1))
        (isEvenPlusEven 1 (mult 24 s) (evenMult24 s))

--------------------------------------------------------------------------------
-- The exact 2-adic factorisation `3(32s+1)+1 = 2^2 * (24s+1)`.
--------------------------------------------------------------------------------

||| `3(32s+1)+1 = 96s+4`.
public export
lhs96 :
  (s : Nat) ->
  plus (mult 3 (plus (mult 32 s) 1)) 1 = plus (mult 96 s) 4
lhs96 s =
  rewrite multDistributesOverPlusRight 3 (mult 32 s) 1 in
  rewrite multAssociative 3 32 s in
  sym (plusAssociative (mult 96 s) 3 1)

||| `2^2 * (24s+1) = 96s+4`.
public export
rhs96 :
  (s : Nat) ->
  mult (pow2 2) (plus (mult 24 s) 1) = plus (mult 96 s) 4
rhs96 s =
  trans (multDistributesOverPlusRight 4 (mult 24 s) 1)
        (rewrite multAssociative 4 24 s in Refl)

||| `3(32s+1)+1 = 2^2 * (24s+1)`, `24s+1` odd.
public export
factor32SPlus1 :
  (s : Nat) ->
  plus (mult 3 (plus (mult 32 s) 1)) 1 = mult (pow2 2) (plus (mult 24 s) 1)
factor32SPlus1 s = trans (lhs96 s) (sym (rhs96 s))

--------------------------------------------------------------------------------
-- Step 1: the first valuation and the odd part of `Syr(32s+1)`.
--------------------------------------------------------------------------------

||| `a_1(32s+1) = 2`.  (Instance `t = 4s` of `valuationTwoOnClass1mod8`, since
||| `32s+1 = 8*(4s)+1`.)
public export
valuationOne32SPlus1 :
  (s : Nat) -> syrValuation (plus (mult 32 s) 1) = 2
valuationOne32SPlus1 s =
  rewrite sym (multAssociative 8 4 s) in valuationTwoOnClass1mod8 (mult 4 s)

||| `Syr(32s+1) = 24s+1` (odd-part form).
public export
syrStep32SPlus1 :
  (s : Nat) ->
  oddValue (Syr (MkOddPos (plus (mult 32 s) 1))) = plus (mult 24 s) 1
syrStep32SPlus1 s =
  rewrite factor32SPlus1 s in
  oddFactorPow2Mult 2 (plus (mult 24 s) 1) (oddTwentyFourSPlus1 s)

--------------------------------------------------------------------------------
-- Step 2: the second valuation.
--------------------------------------------------------------------------------

||| `a_1(24s+1) = 2`.  (Instance `t = 3s` of `valuationTwoOnClass1mod8`, since
||| `24s+1 = 8*(3s)+1`.)
public export
valuationTwo24SPlus1 :
  (s : Nat) -> syrValuation (plus (mult 24 s) 1) = 2
valuationTwo24SPlus1 s =
  rewrite sym (multAssociative 8 3 s) in valuationTwoOnClass1mod8 (mult 3 s)

--------------------------------------------------------------------------------
-- The two-step orbit valuation sum.
--------------------------------------------------------------------------------

||| `S_2(24s+1)` reading: the tail sum `S_1(Syr(32s+1)) = a_2(32s+1) = 2`.
public export
tailValSum :
  (s : Nat) ->
  syrValSum 1 (Syr (MkOddPos (plus (mult 32 s) 1))) = 2
tailValSum s =
  trans (cong (\z => plus (syrValuation z) 0)
              (syrStep32SPlus1 s))
        (cong (\z => plus z 0) (valuationTwo24SPlus1 s))

||| **Main result.**  On the density-`1/32` residue class `y = 32s+1`, the
||| two-step Syracuse orbit valuation sum is *exactly* `S_2(y) = 4`:
||| both `a_1(y) = 2` and `a_2(y) = 2`.
public export
twoStepValSum :
  (s : Nat) -> syrValSum 2 (MkOddPos (plus (mult 32 s) 1)) = 4
twoStepValSum s =
  cong2 plus (valuationOne32SPlus1 s) (tailValSum s)

--------------------------------------------------------------------------------
-- Corollary: a genuine positive-time (time 2) descent on this class.
--------------------------------------------------------------------------------

||| `Syr(32s+1) = 24s+1` (as an `OddPos`).
public export
syrStep32SPlus1Odd :
  (s : Nat) ->
  Syr (MkOddPos (plus (mult 32 s) 1)) = MkOddPos (plus (mult 24 s) 1)
syrStep32SPlus1Odd s = cong MkOddPos (syrStep32SPlus1 s)

||| Step-1 descent: `Syr(32s+1) <= 32s+1`.
public export
descentStep1 :
  (s : Nat) ->
  Leq (oddValue (Syr (MkOddPos (plus (mult 32 s) 1)))) (plus (mult 32 s) 1)
descentStep1 s =
  descendsFromValuationGeTwo (plus (mult 32 s) 1)
    (leqPlusExtraLeft (mult 32 s) 1)
    (leqCastR (leqRefl 2) (sym (valuationOne32SPlus1 s)))

||| Step-2 descent: `Syr(24s+1) <= 24s+1`.
public export
descentStep2 :
  (s : Nat) ->
  Leq (oddValue (Syr (MkOddPos (plus (mult 24 s) 1)))) (plus (mult 24 s) 1)
descentStep2 s =
  descendsFromValuationGeTwo (plus (mult 24 s) 1)
    (leqPlusExtraLeft (mult 24 s) 1)
    (leqCastR (leqRefl 2) (sym (valuationTwo24SPlus1 s)))

||| **Positive-time descent.**  On the density-`1/32` class `y = 32s+1` the
||| orbit descends below the start at the positive time `n = 2`:
||| `oddSize (Syr (Syr y)) <= oddSize y`.
public export
twoStepDescent :
  (s : Nat) ->
  Leq (oddSize (iter 2 Syr (MkOddPos (plus (mult 32 s) 1))))
      (oddSize (MkOddPos (plus (mult 32 s) 1)))
twoStepDescent s =
  let stepVal : Nat
      stepVal = oddValue (Syr (MkOddPos (plus (mult 32 s) 1)))
      -- `stepVal = 24s+1`, so it is positive and has second valuation `2`
      stepPos : Leq 1 stepVal
      stepPos =
        leqCastR (leqPlusExtraLeft (mult 24 s) 1) (sym (syrStep32SPlus1 s))
      stepVal2 : Leq 2 (syrValuation stepVal)
      stepVal2 =
        leqCastR (leqRefl 2)
          (sym (trans (cong syrValuation (syrStep32SPlus1 s))
                      (valuationTwo24SPlus1 s)))
      -- second Syracuse step descends below the first
      d2 : Leq (oddValue (Syr (Syr (MkOddPos (plus (mult 32 s) 1))))) stepVal
      d2 = descendsFromValuationGeTwo stepVal stepPos stepVal2
  in leqTrans d2 (descentStep1 s)
