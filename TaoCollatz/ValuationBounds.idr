module TaoCollatz.ValuationBounds

-- Genuine, fully-proved parity facts and the lower bound on the Syracuse
-- valuation random variable.
--
-- For an odd `n`, `3n+1` is even, so the Syracuse step always removes at least
-- one factor of two: the valuation `syrValuation n >= 1`.  This is the basic
-- support fact for the "geometric valuation" distribution of the paper (item
-- C2 of `REMAINING_WORK.md`).  Establishing it needs a little parity algebra
-- (`isEven` of sums and of `3n`), which is developed here from scratch.
--
-- Everything here is real mathematics: `%default total`, no placeholders, no
-- `believe_me`, no axioms, no holes.

import TaoCollatz.Core
import TaoCollatz.Dynamics
import TaoCollatz.TwoAdic
import TaoCollatz.SyracuseStructure
import TaoCollatz.Density
import Data.Nat

%default total

--------------------------------------------------------------------------------
-- Parity algebra.
--------------------------------------------------------------------------------

||| `isEven (S a) = not (isEven a)`.
public export
isEvenSuccNot : (a : Nat) -> isEven (S a) = not (isEven a)
isEvenSuccNot Z = Refl
isEvenSuccNot (S k) =
  rewrite isEvenSuccNot k in
  rewrite boolNotInvolutiveLocal (isEven k) in Refl
  where
    boolNotInvolutiveLocal : (b : Bool) -> not (not b) = b
    boolNotInvolutiveLocal True = Refl
    boolNotInvolutiveLocal False = Refl

||| `plus a 1 = S a`.
public export
plusOneS : (a : Nat) -> plus a 1 = S a
plusOneS a = trans (sym (plusSuccRightSucc a Z)) (cong S (plusZeroRightNeutral a))

||| A doubled number is even.
public export
isEvenDoubleTrue : (n : Nat) -> isEven (plus n n) = True
isEvenDoubleTrue Z = Refl
isEvenDoubleTrue (S k) =
  rewrite twoSk k in isEvenDoubleTrue k

||| Adding an even number leaves the parity unchanged.
public export
isEvenPlusEven :
  (a : Nat) -> (b : Nat) -> isEven b = True -> isEven (plus a b) = isEven a
isEvenPlusEven Z b hb = hb
isEvenPlusEven (S k) b hb =
  trans (isEvenSuccNot (plus k b))
        (trans (cong not (isEvenPlusEven k b hb))
               (sym (isEvenSuccNot k)))

||| `3n` has the same parity as `n`.
public export
isEvenMult3 : (n : Nat) -> isEven (mult 3 n) = isEven n
isEvenMult3 n =
  isEvenPlusEven n (mult 2 n)
    (rewrite plusZeroRightNeutral n in isEvenDoubleTrue n)

||| For odd `n`, `3n` is odd.
public export
oddTimesThreeOdd : (n : Nat) -> isEven n = False -> isEven (mult 3 n) = False
oddTimesThreeOdd n h = trans (isEvenMult3 n) h

||| For odd `n`, `3n+1` is even.
public export
threeNPlus1Even : (n : Nat) -> isEven n = False -> isEven (plus (mult 3 n) 1) = True
threeNPlus1Even n h =
  rewrite plusOneS (mult 3 n) in
  trans (isEvenSuccNot (mult 3 n)) (cong not (oddTimesThreeOdd n h))

--------------------------------------------------------------------------------
-- The valuation lower bound.
--------------------------------------------------------------------------------

||| An even positive number has 2-adic drop time at least one.
public export
dropTimeGeOneOfEven :
  (m : Nat) -> Leq (S Z) m -> isEven m = True -> Leq (S Z) (oddPartDropTime m)
dropTimeGeOneOfEven Z le _ = void (notLeqSZ le)
dropTimeGeOneOfEven (S k) _ hev =
  rewrite hev in LeqS LeqZ

||| The Syracuse valuation is always at least one: for odd `n`, one Syracuse
||| step removes at least one factor of two from `3n+1`.
public export
syrValuationPositive :
  (n : Nat) -> isEven n = False -> Leq (S Z) (syrValuation n)
syrValuationPositive n h =
  dropTimeGeOneOfEven (plus (mult 3 n) 1)
    (threeNPlusOnePos n)
    (threeNPlus1Even n h)

--------------------------------------------------------------------------------
-- Concrete sanity checks.
--------------------------------------------------------------------------------

public export
sevenOddValuationPos : Leq (S Z) (syrValuation 7)
sevenOddValuationPos = syrValuationPositive 7 Refl

public export
threeNPlus1EvenSeven : isEven (plus (mult 3 7) 1) = True
threeNPlus1EvenSeven = Refl
