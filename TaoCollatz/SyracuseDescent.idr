module TaoCollatz.SyracuseDescent

-- Genuine, fully-proved descent lemma for the Syracuse map.
--
-- One Syracuse step replaces the odd number `n` by `(3n+1) / 2^v`, where `v`
-- is the number of factors of two in `3n+1`.  The single most important
-- quantitative fact about this step is:
--
--     if v >= 2  (equivalently 2^v >= 4)  then  Syr(n) <= n .
--
-- (Two or more factors of two beat the multiplication by three.)  This is the
-- elementary "good step" that drives the first-passage analysis of the paper.
-- Here it is proved unconditionally, from the exact factorisation
-- `3n+1 = Syr(n) * 2^v` (`SyracuseStructure.syrFactorization`).
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
-- Cancelling a factor of four.
--------------------------------------------------------------------------------

||| `4 * a = (a + a) + (a + a)`, the "double the double" shape.
public export
quadIsDoubleDouble : (a : Nat) -> mult 4 a = plus (plus a a) (plus a a)
quadIsDoubleDouble a =
  rewrite plusZeroRightNeutral a in
  plusAssociative a a (plus a a)

||| Left cancellation of a factor of four in `Leq`.
public export
leqQuadCancel : {a : Nat} -> {b : Nat} -> Leq (mult 4 a) (mult 4 b) -> Leq a b
leqQuadCancel {a} {b} h =
  leqHalf (leqHalf (leqCastR (leqCastL (sym (quadIsDoubleDouble a)) h)
                             (quadIsDoubleDouble b)))

--------------------------------------------------------------------------------
-- Elementary bound `3n+1 <= 4n` for `n >= 1`.
--------------------------------------------------------------------------------

public export
threeNPlus1LeqFourN : (n : Nat) -> Leq (S Z) n -> Leq (plus (mult 3 n) 1) (mult 4 n)
threeNPlus1LeqFourN n h =
  leqCastR (addLeftMono (mult 3 n) h) (plusCommutative (mult 3 n) n)

--------------------------------------------------------------------------------
-- The descent lemma.
--------------------------------------------------------------------------------

||| If `2^v >= 4` (the valuation of `3n+1` is at least two), then one Syracuse
||| step brings the value down to at most a quarter of `3n+1`:
||| `4 * Syr(n) <= 3n+1`.
public export
syrQuarterBound :
  (n : Nat) ->
  Leq 4 (pow2 (syrValuation n)) ->
  Leq (mult 4 (oddValue (Syr (MkOddPos n)))) (plus (mult 3 n) 1)
syrQuarterBound n hval =
  leqCastR
    (leqMultRight hval (oddValue (Syr (MkOddPos n))))
    (trans (multCommutative (pow2 (syrValuation n)) (oddValue (Syr (MkOddPos n))))
           (sym (syrFactorization n)))

||| The Syracuse descent lemma: if the valuation of `3n+1` is at least two, then
||| one Syracuse step does not increase the value: `Syr(n) <= n` (for `n >= 1`).
public export
syrDescends :
  (n : Nat) ->
  Leq (S Z) n ->
  Leq 4 (pow2 (syrValuation n)) ->
  Leq (oddValue (Syr (MkOddPos n))) n
syrDescends n h1 hval =
  leqQuadCancel (leqTrans (syrQuarterBound n hval) (threeNPlus1LeqFourN n h1))

--------------------------------------------------------------------------------
-- Concrete sanity check: n = 3, 3*3+1 = 10 = 5 * 2, valuation 1 (no descent);
-- n = 5, 3*5+1 = 16 = 1 * 2^4, valuation 4 >= 2, so Syr(5) = 1 <= 5.
--------------------------------------------------------------------------------

public export
syrFiveValuationFour : pow2 (syrValuation 5) = 16
syrFiveValuationFour = Refl

public export
syrFiveDescends : Leq (oddValue (Syr (MkOddPos 5))) 5
syrFiveDescends = syrDescends 5 (LeqS LeqZ) (LeqS (LeqS (LeqS (LeqS LeqZ))))
