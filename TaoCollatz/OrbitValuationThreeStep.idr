module TaoCollatz.OrbitValuationThreeStep

-- Genuine, fully-proved *three-step* slice of the Syracuse orbit valuation
-- distribution, extending `TaoCollatz.OrbitValuationTwoStep` by one more step.
--
-- The two-step module pins the first two orbit valuations `a_1, a_2` on the
-- density-`1/32` class `y = 32s+1`.  To pin a *third* valuation `a_3` at a fixed
-- value we must restrict to a finer residue class so that the second Syracuse
-- iterate again lands in `1 (mod 8)`.  Concretely, on the density-`1/128`
-- residue class `y = 128r+1`:
--
--   * `3(128r+1)+1 = 384r+4 = 2^2 * (96r+1)`, so `a_1(y) = 2` and
--     `Syr(y) = 96r+1`;
--   * `96r+1 = 32*(3r)+1`, so this iterate lies in the two-step class, and the
--     already-proved two-step results apply to it verbatim (with `s = 3r`).
--
-- Hence the three-step orbit valuation sum is *exactly* `S_3(y) = 6` on this
-- density-`1/128` set (`threeStepValSum`), i.e. `a_1 = a_2 = a_3 = 2`.  As every
-- valuation along the orbit is `>= 2`, all three Syracuse steps descend, giving a
-- genuine positive-time (time `3`) descent below the start on this class
-- (`threeStepDescent`).
--
-- This is the next concrete, checked instance of the Syracuse valuation random
-- variables taking prescribed values along the *orbit* on a set of prescribed
-- density, continuing the multi-step slices of the orbit valuation distribution.
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
import TaoCollatz.SyracuseStructure
import TaoCollatz.ValuationExact
import TaoCollatz.ValuationBounds
import TaoCollatz.ValuationTwoClass
import TaoCollatz.Pieces64
import TaoCollatz.OrbitValuationTwoStep

%default total

--------------------------------------------------------------------------------
-- Parity of the odd cofactor `96r+1`.
--------------------------------------------------------------------------------

||| `96r` is even.
public export
evenMult96 : (r : Nat) -> isEven (mult 96 r) = True
evenMult96 r =
  rewrite multDistributesOverPlusLeft 48 48 r in
  isEvenDoubleTrue (mult 48 r)

||| `96r+1` is odd -- the odd cofactor in `3(128r+1)+1 = 2^2 * (96r+1)`.
public export
oddNinetySixRPlus1 : (r : Nat) -> isEven (plus (mult 96 r) 1) = False
oddNinetySixRPlus1 r =
  trans (cong isEven (plusCommutative (mult 96 r) 1))
        (isEvenPlusEven 1 (mult 96 r) (evenMult96 r))

--------------------------------------------------------------------------------
-- The exact 2-adic factorisation `3(128r+1)+1 = 2^2 * (96r+1)`.
--------------------------------------------------------------------------------

||| `3(128r+1)+1 = 384r+4`.
public export
lhs384 :
  (r : Nat) ->
  plus (mult 3 (plus (mult 128 r) 1)) 1 = plus (mult 384 r) 4
lhs384 r =
  rewrite multDistributesOverPlusRight 3 (mult 128 r) 1 in
  rewrite multAssociative 3 128 r in
  sym (plusAssociative (mult 384 r) 3 1)

||| `2^2 * (96r+1) = 384r+4`.
public export
rhs384 :
  (r : Nat) ->
  mult (pow2 2) (plus (mult 96 r) 1) = plus (mult 384 r) 4
rhs384 r =
  trans (multDistributesOverPlusRight 4 (mult 96 r) 1)
        (rewrite multAssociative 4 96 r in Refl)

||| `3(128r+1)+1 = 2^2 * (96r+1)`, `96r+1` odd.
public export
factor128RPlus1 :
  (r : Nat) ->
  plus (mult 3 (plus (mult 128 r) 1)) 1 = mult (pow2 2) (plus (mult 96 r) 1)
factor128RPlus1 r = trans (lhs384 r) (sym (rhs384 r))

--------------------------------------------------------------------------------
-- Step 1: the first valuation and the odd part of `Syr(128r+1)`.
--------------------------------------------------------------------------------

||| `a_1(128r+1) = 2`.  (Instance `t = 16r` of `valuationTwoOnClass1mod8`, since
||| `128r+1 = 8*(16r)+1`.)
public export
valuationOne128RPlus1 :
  (r : Nat) -> syrValuation (plus (mult 128 r) 1) = 2
valuationOne128RPlus1 r =
  rewrite sym (multAssociative 8 16 r) in valuationTwoOnClass1mod8 (mult 16 r)

||| `Syr(128r+1) = 96r+1` (odd-part form).
public export
syrStep128RPlus1 :
  (r : Nat) ->
  oddValue (Syr (MkOddPos (plus (mult 128 r) 1))) = plus (mult 96 r) 1
syrStep128RPlus1 r =
  rewrite factor128RPlus1 r in
  oddFactorPow2Mult 2 (plus (mult 96 r) 1) (oddNinetySixRPlus1 r)

||| `Syr(128r+1) = 96r+1` (as an `OddPos`).
public export
syrStep128RPlus1Odd :
  (r : Nat) ->
  Syr (MkOddPos (plus (mult 128 r) 1)) = MkOddPos (plus (mult 96 r) 1)
syrStep128RPlus1Odd r = cong MkOddPos (syrStep128RPlus1 r)

--------------------------------------------------------------------------------
-- The three-step orbit valuation sum, via the two-step results applied to the
-- iterate `Syr(128r+1) = 96r+1 = 32*(3r)+1`.
--------------------------------------------------------------------------------

||| The two-step orbit valuation sum on the iterate class `96r+1 = 32*(3r)+1`,
||| directly from the two-step result `twoStepValSum (3r)`.
public export
twoStepValSum96 :
  (r : Nat) ->
  syrValSum 2 (MkOddPos (plus (mult 96 r) 1)) = 4
twoStepValSum96 r =
  rewrite sym (multAssociative 32 3 r) in twoStepValSum (mult 3 r)

||| The two-step tail sum along `Syr(128r+1) = 96r+1 = 32*(3r)+1`:
||| `S_2(Syr(128r+1)) = 4` (i.e. `a_2 = a_3 = 2`).
public export
tailTwoStepValSum :
  (r : Nat) ->
  syrValSum 2 (Syr (MkOddPos (plus (mult 128 r) 1))) = 4
tailTwoStepValSum r =
  trans (cong (syrValSum 2) (syrStep128RPlus1Odd r)) (twoStepValSum96 r)

||| **Main result.**  On the density-`1/128` residue class `y = 128r+1`, the
||| three-step Syracuse orbit valuation sum is *exactly* `S_3(y) = 6`:
||| `a_1(y) = a_2(y) = a_3(y) = 2`.
public export
threeStepValSum :
  (r : Nat) -> syrValSum 3 (MkOddPos (plus (mult 128 r) 1)) = 6
threeStepValSum r =
  cong2 plus (valuationOne128RPlus1 r) (tailTwoStepValSum r)

--------------------------------------------------------------------------------
-- Corollary: a genuine positive-time (time 3) descent on this class.
--------------------------------------------------------------------------------

||| Step-1 descent: `Syr(128r+1) <= 128r+1` (the first Syracuse step descends,
||| since `a_1 = 2 >= 2`).
public export
descentStep128 :
  (r : Nat) ->
  Leq (oddValue (Syr (MkOddPos (plus (mult 128 r) 1)))) (plus (mult 128 r) 1)
descentStep128 r =
  descendsFromValuationGeTwo (plus (mult 128 r) 1)
    (leqPlusExtraLeft (mult 128 r) 1)
    (leqCastR (leqRefl 2) (sym (valuationOne128RPlus1 r)))

||| **Positive-time descent.**  On the density-`1/128` class `y = 128r+1` the
||| orbit descends below the start at the positive time `n = 3`:
||| `oddSize (iter 3 Syr y) <= oddSize y`.
|||
||| The two later steps are handled by `twoStepDescent (3r)` applied to the
||| iterate `Syr(y) = 96r+1 = 32*(3r)+1`, and the first step by `descentStep128`.
public export
twoStepDescent96 :
  (r : Nat) ->
  Leq (oddSize (iter 2 Syr (MkOddPos (plus (mult 96 r) 1))))
      (oddSize (MkOddPos (plus (mult 96 r) 1)))
twoStepDescent96 r =
  rewrite sym (multAssociative 32 3 r) in twoStepDescent (mult 3 r)

||| `iter 3 Syr y = iter 2 Syr (Syr y) = iter 2 Syr (MkOddPos (96r+1))`.
public export
iterThreeShift :
  (r : Nat) ->
  iter 3 Syr (MkOddPos (plus (mult 128 r) 1))
    = iter 2 Syr (MkOddPos (plus (mult 96 r) 1))
iterThreeShift r = cong (iter 2 Syr) (syrStep128RPlus1Odd r)

||| First step descends: `oddSize (MkOddPos (96r+1)) = Syr y <= y`.
public export
headDescent128 :
  (r : Nat) ->
  Leq (oddSize (MkOddPos (plus (mult 96 r) 1))) (plus (mult 128 r) 1)
headDescent128 r = leqCastL (sym (syrStep128RPlus1 r)) (descentStep128 r)

public export
threeStepDescent :
  (r : Nat) ->
  Leq (oddSize (iter 3 Syr (MkOddPos (plus (mult 128 r) 1))))
      (oddSize (MkOddPos (plus (mult 128 r) 1)))
threeStepDescent r =
  leqCastL (cong oddSize (iterThreeShift r))
           (leqTrans (twoStepDescent96 r) (headDescent128 r))
