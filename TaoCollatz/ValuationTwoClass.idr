module TaoCollatz.ValuationTwoClass

-- Genuine, fully-proved *exact* Syracuse valuation on the residue class
-- `n ≡ 1 (mod 8)`.
--
-- This module is now a short *instance* of the general exact-valuation lemma
-- `ValuationExact.syrValuationFromFactor`: to read off the valuation one only
-- has to exhibit the 2-adic factorisation of `3n+1`.  For the class `n = 8t+1`,
--
--     3(8t+1)+1 = 24t+4 = 4 * (6t+1) = 2^2 * (6t+1),   6t+1 odd,
--
-- so `syrValuation (8t+1) = 2` follows immediately (the earlier bespoke
-- half/half chase and the `dropTimeExactlyTwo` case analysis are no longer
-- needed -- they are subsumed by the general lemma).
--
-- Everything here is real mathematics: `%default total`, no placeholders, no
-- `believe_me`, no axioms, no holes.

import TaoCollatz.Core
import TaoCollatz.Dynamics
import TaoCollatz.TwoAdic
import TaoCollatz.SyracuseStructure
import TaoCollatz.SyracuseDescent
import TaoCollatz.ValuationBounds
import TaoCollatz.ValuationExact
import TaoCollatz.Density
import Data.Nat

%default total

--------------------------------------------------------------------------------
-- Parity of the linear forms appearing in the factorisation.
--------------------------------------------------------------------------------

||| `6t` is even.
public export
evenMult6 : (t : Nat) -> isEven (mult 6 t) = True
evenMult6 t =
  rewrite multDistributesOverPlusLeft 3 3 t in
  isEvenDoubleTrue (mult 3 t)

||| `6t+1` is odd -- this is the odd cofactor `q` in `3n+1 = 2^2 * q`.
public export
oddSixTPlus1 : (t : Nat) -> isEven (plus (mult 6 t) 1) = False
oddSixTPlus1 t =
  trans (cong isEven (plusCommutative (mult 6 t) 1))
        (isEvenPlusEven 1 (mult 6 t) (evenMult6 t))

--------------------------------------------------------------------------------
-- The 2-adic factorisation `3(8t+1)+1 = 2^2 * (6t+1)`.
--------------------------------------------------------------------------------

||| `3 * (8t) = (12t) + (12t)`.
public export
threeEightEqTwelveTwelve :
  (t : Nat) -> mult 3 (mult 8 t) = plus (mult 12 t) (mult 12 t)
threeEightEqTwelveTwelve t =
  trans (multAssociative 3 8 t) (multDistributesOverPlusLeft 12 12 t)

||| `12t = (6t) + (6t)`.
public export
twelveEqSixSix : (t : Nat) -> mult 12 t = plus (mult 6 t) (mult 6 t)
twelveEqSixSix t = multDistributesOverPlusLeft 6 6 t

||| `3(8t+1)+1 = (12t+2) + (12t+2)`.
public export
class1mod8Double :
  (t : Nat) ->
  plus (mult 3 (plus (mult 8 t) 1)) 1 = plus (plus (mult 12 t) 2) (plus (mult 12 t) 2)
class1mod8Double t =
  rewrite multDistributesOverPlusRight 3 (mult 8 t) 1 in
  rewrite threeEightEqTwelveTwelve t in
  rewrite plusRearrange (mult 12 t) 2 (mult 12 t) 2 in
  sym (plusAssociative (plus (mult 12 t) (mult 12 t)) 3 1)

||| `12t+2 = (6t+1) + (6t+1)`.
public export
twelveTPlus2Double :
  (t : Nat) -> plus (mult 12 t) 2 = plus (plus (mult 6 t) 1) (plus (mult 6 t) 1)
twelveTPlus2Double t =
  rewrite twelveEqSixSix t in
  rewrite plusRearrange (mult 6 t) 1 (mult 6 t) 1 in
  Refl

||| The clean factorisation feeding the general lemma:
||| `3(8t+1)+1 = 2^2 * (6t+1)`.
public export
class1mod8Factor :
  (t : Nat) ->
  plus (mult 3 (plus (mult 8 t) 1)) 1 = mult (pow2 2) (plus (mult 6 t) 1)
class1mod8Factor t =
  rewrite class1mod8Double t in
  rewrite twelveTPlus2Double t in
  sym (quadIsDoubleDouble (plus (mult 6 t) 1))

--------------------------------------------------------------------------------
-- The exact valuation on the class `n = 8t+1` -- a one-line instance now.
--------------------------------------------------------------------------------

||| The Syracuse valuation is **exactly two** on the residue class
||| `n ≡ 1 (mod 8)`: `syrValuation (8t+1) = 2`.  Immediate from the general
||| `syrValuationFromFactor` and the factorisation above.
public export
valuationTwoOnClass1mod8 :
  (t : Nat) -> syrValuation (plus (mult 8 t) 1) = 2
valuationTwoOnClass1mod8 t =
  syrValuationFromFactor (plus (mult 8 t) 1) 2 (plus (mult 6 t) 1)
    (oddSixTPlus1 t) (class1mod8Factor t)

--------------------------------------------------------------------------------
-- Concrete sanity checks.
--------------------------------------------------------------------------------

||| `t = 0`: `n = 1`, `3*1+1 = 4 = 4*1`, valuation two.
public export
valuationTwoOne : syrValuation 1 = 2
valuationTwoOne = valuationTwoOnClass1mod8 0

||| `t = 1`: `n = 9`, `3*9+1 = 28 = 4*7`, valuation two.
public export
valuationTwoNine : syrValuation 9 = 2
valuationTwoNine = valuationTwoOnClass1mod8 1
