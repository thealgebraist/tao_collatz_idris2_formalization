module TaoCollatz.ValuationMoment

-- The first moment (expectation) of the 2-adic valuation distribution, and the
-- resulting downward *drift* that drives Collatz/Syracuse descent.
--
-- `TaoCollatz.GeometricValuation` builds `geoValuation K`, the finitely
-- supported measure that places mass `2^{K-j}` at valuation `j` (`j = 1..K`),
-- and proves its total mass is `2^K - 1`.  This module computes the measure's
-- *first moment* (unnormalised expectation) in closed form:
--
--     weightedSum (geoValuation n) + (n + 2) = 2 * 2^n ,
--
-- i.e. `E[a] = (2^{n+1} - (n+2)) / (2^n - 1) -> 2` as `n -> infinity`.  This is
-- the mean 2-adic valuation of the Syracuse step.  Its significance: the
-- Syracuse map sends an odd `x` to (the odd part of) `3x+1`, dividing by `2^a`
-- where `a` is the valuation; the orbit's multiplicative growth per step is
-- `3 / 2^a`, so it contracts on average precisely when `E[a] > log2 3`.
--
-- We also record the *drift* quantitatively.  Since `log2 3 < 8/5` (because
-- `3^5 = 243 < 256 = 2^8`), a mean valuation exceeding `8/5` already forces the
-- contraction, and we witness this at the concrete scale `n = 4`
-- (`E[a] = 26/15 > 8/5`) together with the growth comparison `3^5 <= 2^8`.
--
-- Everything here is real, total mathematics: `%default total`, no
-- placeholders, no `believe_me`, no axioms, no holes.

import Data.Nat
import TaoCollatz.Core
import TaoCollatz.Density
import TaoCollatz.DensityProperties
import TaoCollatz.TwoAdic
import TaoCollatz.FinMeasure
import TaoCollatz.GeometricValuation

%default total

--------------------------------------------------------------------------------
-- Two addition rearrangements, used to shuffle moments.
--------------------------------------------------------------------------------

||| `(a+b)+(c+d) = (b+c)+(a+d)`.
public export
plusComm4 :
  (a : Nat) -> (b : Nat) -> (c : Nat) -> (d : Nat) ->
  plus (plus a b) (plus c d) = plus (plus b c) (plus a d)
plusComm4 a b c d =
  let lemA : (plus (plus a b) (plus c d) = plus a (plus (plus b c) d))
      lemA = trans (sym (plusAssociative a b (plus c d)))
                   (cong (plus a) (plusAssociative b c d))
      lemB : (plus (plus b c) (plus a d) = plus a (plus (plus b c) d))
      lemB = trans (cong (plus (plus b c)) (plusCommutative a d))
                   (trans (plusAssociative (plus b c) d a)
                          (plusCommutative (plus (plus b c) d) a))
  in trans lemA (sym lemB)

||| `(a+b)+(c+d) = (a+c)+(b+d)` (swap the two inner summands).
public export
plusSwapMid :
  (a : Nat) -> (b : Nat) -> (c : Nat) -> (d : Nat) ->
  plus (plus a b) (plus c d) = plus (plus a c) (plus b d)
plusSwapMid a b c d =
  trans (sym (plusAssociative a b (plus c d)))
  (trans (cong (plus a) (plusAssociative b c d))
  (trans (cong (\x => plus a (plus x d)) (plusCommutative b c))
  (trans (cong (plus a) (sym (plusAssociative c b d)))
         (plusAssociative a c (plus b d)))))

--------------------------------------------------------------------------------
-- Moment additivity under the value-shift `shift1`.
--------------------------------------------------------------------------------

||| Shifting every value up by one raises the first moment by the total mass:
||| `E[X+1] = E[X] + mass`.
public export
weightedSumShift1 :
  (d : FinDist) -> weightedSum (shift1 d) = plus (weightedSum d) (mass d)
weightedSumShift1 Empty = Refl
weightedSumShift1 (Atom v w r) =
  rewrite weightedSumShift1 r in
  plusComm4 w (mult v w) (weightedSum r) (mass r)

--------------------------------------------------------------------------------
-- Algebraic helpers for the closed-form induction.
--------------------------------------------------------------------------------

||| `(S (S (S k))) = (S (S k)) + 1`, exposing the split of the constant.
plusThreeSucc : (k : Nat) -> S (S (S k)) = plus (S (S k)) (S Z)
plusThreeSucc k = sym (cong (\x => S (S x)) (plusCommutative k (S Z)))

||| Regroup `(w+m) + (k+3)` as `(w+(k+2)) + (m+1)`.
rearr3 :
  (w : Nat) -> (m : Nat) -> (k : Nat) ->
  plus (plus w m) (S (S (S k)))
    = plus (plus w (S (S k))) (plus m (S Z))
rearr3 w m k =
  trans (cong (plus (plus w m)) (plusThreeSucc k))
        (plusSwapMid w m (S (S k)) (S Z))

||| Substitute the two closed forms into the regrouped sum.
sumWM :
  (p : Nat) -> (w : Nat) -> (m : Nat) -> (k : Nat) ->
  plus w (S (S k)) = mult 2 p -> plus m (S Z) = p ->
  plus (plus w m) (S (S (S k))) = plus (mult 2 p) p
sumWM p w m k hw hm =
  trans (rearr3 w m k)
        (trans (cong (\x => plus x (plus m (S Z))) hw)
               (cong (\y => plus (mult 2 p) y) hm))

||| `p + (2p + p) = 2 (p + p)` (i.e. `4p = 4p`).
fourP : (p : Nat) -> plus p (plus (mult 2 p) p) = mult 2 (plus p p)
fourP p =
  trans (cong (plus p) (plusCommutative (mult 2 p) p))
        (trans (the (plus p (plus p (mult 2 p)) = mult (S (S (S (S Z)))) p) Refl)
               (trans (multDistributesOverPlusLeft 2 2 p)
                      (sym (multDistributesOverPlusRight 2 p p))))

||| The inductive step for the closed form, phrased purely algebraically.
momentStep :
  (p : Nat) -> (w : Nat) -> (m : Nat) -> (k : Nat) ->
  plus w (S (S k)) = mult 2 p -> plus m (S Z) = p ->
  plus (plus (plus p Z) (plus w m)) (S (S (S k))) = mult 2 (plus p p)
momentStep p w m k hw hm =
  rewrite plusZeroRightNeutral p in
  rewrite sym (plusAssociative p (plus w m) (S (S (S k)))) in
  rewrite sumWM p w m k hw hm in
  fourP p

--------------------------------------------------------------------------------
-- The first moment of the 2-adic valuation distribution, in closed form.
--------------------------------------------------------------------------------

||| Closed form of the (unnormalised) expectation of the valuation measure:
||| `weightedSum (geoValuation n) + (n + 2) = 2 * 2^n`.  Combined with the mass
||| normalisation `mass + 1 = 2^n`, this says the mean valuation tends to `2`.
public export
weightedSumGeoValuation :
  (n : Nat) ->
  plus (weightedSum (geoValuation n)) (S (S n)) = mult 2 (pow2 n)
weightedSumGeoValuation Z = Refl
weightedSumGeoValuation (S k) =
  rewrite weightedSumShift1 (geoValuation k) in
  momentStep (pow2 k) (weightedSum (geoValuation k)) (mass (geoValuation k)) k
             (weightedSumGeoValuation k) (massGeoValuationPlusOne k)

--------------------------------------------------------------------------------
-- The number-theoretic core of the drift: 2^{n+1} >= 5n + 2 for n >= 4.
--------------------------------------------------------------------------------

||| `a <= a + d`.
public export
leqSelfPlusRight : (a : Nat) -> (d : Nat) -> Leq a (plus a d)
leqSelfPlusRight a d = leqCastR (leqPlusExtraLeft d a) (plusCommutative d a)

||| `(5 + M) + 2 = (M + 2) + 5`.
plusFiveRearr : (m : Nat) -> plus (plus 5 m) 2 = plus (plus m 2) 5
plusFiveRearr m =
  trans (cong (\x => plus x 2) (plusCommutative 5 m))
        (trans (sym (plusAssociative m 5 2))
               (plusAssociative m 2 5))

||| `2^{n+1} >= 5n + 2` for `n >= 4`, in the left-offset form `n = 4 + j` so
||| that the successor arithmetic reduces cleanly.
public export
pow2LinearShifted :
  (j : Nat) ->
  Leq (plus (mult 5 (plus 4 j)) (S (S Z))) (pow2 (S (plus 4 j)))
pow2LinearShifted Z = leqPlusExtraLeft 10 22
pow2LinearShifted (S i) =
  let a : Nat
      a = plus 4 i
      ih : (Leq (plus (mult 5 a) (S (S Z))) (pow2 (S a)))
      ih = pow2LinearShifted i
      five_le_mult : (Leq 5 (mult 5 a))
      five_le_mult =
        leqCastR (leqMultRight (the (Leq 1 a) (LeqS LeqZ)) 5)
                 (multCommutative a 5)
      h5 : (Leq 5 (pow2 (S a)))
      h5 = leqTrans (leqTrans five_le_mult (leqSelfPlusRight (mult 5 a) 2)) ih
      combined : (Leq (plus (plus (mult 5 a) 2) 5)
                      (plus (pow2 (S a)) (pow2 (S a))))
      combined = leqAdd ih h5
      lhsEq : (plus (mult 5 (S a)) 2 = plus (plus (mult 5 a) 2) 5)
      lhsEq = trans (cong (\x => plus x 2) (multRightSuccPlus 5 a))
                    (plusFiveRearr (mult 5 a))
  in leqCastL lhsEq combined

||| `2^{n+1} >= 5n + 2` for all `n >= 4`, extracted from the shifted form via a
||| witness `n = 4 + j`.
public export
pow2LinearFromWitness :
  (n : Nat) -> (j : Nat) -> n = plus 4 j ->
  Leq (plus (mult 5 n) (S (S Z))) (pow2 (S n))
pow2LinearFromWitness n j eq =
  rewrite eq in pow2LinearShifted j

--------------------------------------------------------------------------------
-- The general drift: `8 * mass <= 5 * weightedSum` for all scales `n >= 4`.
--
-- This is the mean bound `E[a] >= 8/5` (in cross-multiplied, subtraction-free
-- form), holding for every `n >= 4`.  Together with `growthComparison`
-- (`3^5 <= 2^8`, i.e. `log2 3 < 8/5`) it establishes the genuine downward
-- drift of the Syracuse step at every large scale.
--------------------------------------------------------------------------------

||| `2 * p = p + p`.
doubleEq : (p : Nat) -> mult 2 p = plus p p
doubleEq p = cong (plus p) (plusZeroRightNeutral p)

||| `8 + (a + b) = a + (8 + b)` (rotate the constant inward).
rotate8 : (a : Nat) -> (b : Nat) -> plus 8 (plus a b) = plus a (plus 8 b)
rotate8 a b =
  trans (plusAssociative 8 a b)
        (trans (cong (\x => plus x b) (plusCommutative 8 a))
               (sym (plusAssociative a 8 b)))

||| The general drift, in left-offset form `n = 4 + j`.
public export
generalDriftShifted :
  (j : Nat) ->
  Leq (mult 8 (mass (geoValuation (plus 4 j))))
      (mult 5 (weightedSum (geoValuation (plus 4 j))))
generalDriftShifted j =
  let n : Nat
      n = plus 4 j
      ms : Nat
      ms = mass (geoValuation n)
      ws : Nat
      ws = weightedSum (geoValuation n)
      p : Nat
      p = pow2 n
      -- Closed-form identities.
      eqA : (plus (mult 8 ms) 8 = mult 8 p)
      eqA = trans (sym (multDistributesOverPlusRight 8 ms 1))
                  (cong (mult 8) (massGeoValuationPlusOne n))
      eqB : (plus (mult 5 ws) (mult 5 (S (S n))) = mult 5 (mult 2 p))
      eqB = trans (sym (multDistributesOverPlusRight 5 ws (S (S n))))
                  (cong (mult 5) (weightedSumGeoValuation n))
      eqC : (mult 5 (S (S n)) = plus 10 (mult 5 n))
      eqC = trans (multRightSuccPlus 5 (S n))
                  (cong (plus 5) (multRightSuccPlus 5 n))
      eqD : (mult 5 (mult 2 p) = mult 10 p)
      eqD = multAssociative 5 2 p
      eqE : (mult 10 p = plus (mult 8 p) (mult 2 p))
      eqE = multDistributesOverPlusLeft 8 2 p
      -- Tail inequality: 5n + 2 <= 2p, in the shape we need.
      innerLeq : (Leq (plus 2 (mult 5 n)) (mult 2 p))
      innerLeq =
        leqCastL (plusCommutative 2 (mult 5 n))
                 (leqCastR (pow2LinearShifted j) (sym (doubleEq p)))
      tailLeq : (Leq (plus 10 (mult 5 n)) (plus 8 (mult 2 p)))
      tailLeq = leqAdd (leqRefl 8) innerLeq
      bigLeq : (Leq (plus (mult 8 p) (plus 10 (mult 5 n)))
                    (plus (mult 8 p) (plus 8 (mult 2 p))))
      bigLeq = leqAdd (leqRefl (mult 8 p)) tailLeq
      -- Recast the two endpoints into the `LHSbig`/`RHSbig` forms.
      eqLHSbig : (plus (mult 5 (S (S n))) (mult 8 p)
                    = plus (mult 8 p) (plus 10 (mult 5 n)))
      eqLHSbig =
        trans (cong (\x => plus x (mult 8 p)) eqC)
              (plusCommutative (plus 10 (mult 5 n)) (mult 8 p))
      eqRHSbig : (plus 8 (mult 5 (mult 2 p))
                    = plus (mult 8 p) (plus 8 (mult 2 p)))
      eqRHSbig =
        trans (cong (plus 8) (trans eqD eqE))
              (rotate8 (mult 8 p) (mult 2 p))
      finalLeq : (Leq (plus (mult 5 (S (S n))) (mult 8 p))
                      (plus 8 (mult 5 (mult 2 p))))
      finalLeq =
        leqCastL eqLHSbig (leqCastR bigLeq (sym eqRHSbig))
      -- Add the cancellation constant and rewrite both sides.
      eqLHS : (plus (plus (mult 5 (S (S n))) 8) (mult 8 ms)
                 = plus (mult 5 (S (S n))) (mult 8 p))
      eqLHS =
        trans (sym (plusAssociative (mult 5 (S (S n))) 8 (mult 8 ms)))
              (trans (cong (plus (mult 5 (S (S n))))
                           (plusCommutative 8 (mult 8 ms)))
                     (cong (plus (mult 5 (S (S n)))) eqA))
      eqRHS : (plus (plus (mult 5 (S (S n))) 8) (mult 5 ws)
                 = plus 8 (mult 5 (mult 2 p)))
      eqRHS =
        trans (cong (\x => plus x (mult 5 ws))
                    (plusCommutative (mult 5 (S (S n))) 8))
              (trans (sym (plusAssociative 8 (mult 5 (S (S n))) (mult 5 ws)))
                     (cong (plus 8)
                           (trans (plusCommutative (mult 5 (S (S n))) (mult 5 ws))
                                  eqB)))
      cancelLeq : (Leq (plus (plus (mult 5 (S (S n))) 8) (mult 8 ms))
                       (plus (plus (mult 5 (S (S n))) 8) (mult 5 ws)))
      cancelLeq = leqCastL eqLHS (leqCastR finalLeq (sym eqRHS))
  in leqCancelLeft (plus (mult 5 (S (S n))) 8) cancelLeq

||| The general drift for every `n >= 4`, via a witness `n = 4 + j`.
public export
generalDrift :
  (n : Nat) -> (j : Nat) -> n = plus 4 j ->
  Leq (mult 8 (mass (geoValuation n))) (mult 5 (weightedSum (geoValuation n)))
generalDrift n j eq = rewrite eq in generalDriftShifted j

--------------------------------------------------------------------------------
-- Concrete drift: mean valuation at scale 4 exceeds 8/5 > log2 3.
--------------------------------------------------------------------------------

||| First moment at scale 4 is 26 (values `{1|->8,2|->4,3|->2,4|->1}`).
public export
weightedSumGeoValuationFour : weightedSum (geoValuation 4) = 26
weightedSumGeoValuationFour = Refl

||| Total mass at scale 4 is 15.
public export
massGeoValuationFour : mass (geoValuation 4) = 15
massGeoValuationFour = Refl

||| Drift at scale 4: `8 * mass <= 5 * weightedSum` (i.e. mean `26/15 >= 8/5`),
||| as an instance of `generalDrift` at `n = 4 = 4 + 0`.
public export
driftFour :
  Leq (mult 8 (mass (geoValuation 4))) (mult 5 (weightedSum (geoValuation 4)))
driftFour = generalDrift 4 0 Refl

||| The growth comparison witnessing `log2 3 < 8/5`: `3^5 = 243 <= 256 = 2^8`.
||| Hence a mean valuation `>= 8/5` forces the per-step factor `3 / 2^E[a] < 1`.
public export
growthComparison :
  Leq (mult 3 (mult 3 (mult 3 (mult 3 3)))) (pow2 8)
growthComparison = leqPlusExtraLeft 13 243
