module TaoCollatz.ValuationTail

-- The exact tail (survival function) of the 2-adic valuation distribution, and
-- its consequences -- the genuine distributional core of Proposition 1.9.
--
-- `TaoCollatz.GeometricValuation` builds `geoValuation K`, the finitely
-- supported measure placing mass `2^{K-j}` at valuation `j` (`j = 1..K`), and
-- `TaoCollatz.TailBound` proves the abstract tail machinery (additivity,
-- monotonicity, Markov) on the shared carrier `FinDist`.  This module pins the
-- **exact tail** of the valuation measure:
--
--     mu({ a >= j+1 }) = 2^{n-j} - 1        (`tailGeoValuation`, in +1 form)
--
-- from which follow the exponential decay bound `mu({a >= j+1}) <= 2^{n-j}`
-- (`tailGeoValuationLe`), the exact geometric halving law
-- `mu({a >= j}) = 2 * mu({a >= j+1})` (`tailHalving`), the complementary
-- distribution function (`massLtGeComplement`), and a genuine Markov instance on
-- the real distribution (`markovGeoValuation`).
--
-- This is the concrete, machine-checked distribution of the Syracuse valuation
-- random variable (items C1/C2/C3 of `REMAINING_WORK.md`) -- exactly the object
-- whose tail estimate is Proposition 1.9.  Everything is real, total
-- mathematics: `%default total`, no placeholders, no `believe_me`, no axioms, no
-- holes.

import Data.Nat
import TaoCollatz.Core
import TaoCollatz.TwoAdic
import TaoCollatz.Density
import TaoCollatz.FinMeasure
import TaoCollatz.TailBound
import TaoCollatz.GeometricValuation
import TaoCollatz.ValuationMoment

%default total

--------------------------------------------------------------------------------
-- The tail commutes with the value-shift used to build `geoValuation`.
--------------------------------------------------------------------------------

||| Shifting every value up by one raises the tail threshold by one:
||| `mu_{+1}({x >= t+1}) = mu({x >= t})`.
public export
massGeShift1 : (t : Nat) -> (d : FinDist) -> massGe (S t) (shift1 d) = massGe t d
massGeShift1 t Empty = Refl
massGeShift1 t (Atom v w r) with (decLeq (S t) (S v)) | (decLeq t v)
  _ | IsLeq _ | IsLeq _ = cong (plus w) (massGeShift1 t r)
  _ | IsLeq (LeqS p) | IsGt q = void (leqSuccAbsurd v (leqTrans q p))
  _ | IsGt (LeqS p) | IsLeq q = void (leqSuccAbsurd v (leqTrans p q))
  _ | IsGt _ | IsGt _ = massGeShift1 t r

--------------------------------------------------------------------------------
-- The exact tail of the valuation distribution (Prop. 1.9 distributional core).
--------------------------------------------------------------------------------

||| Exact survival function of the 2-adic valuation measure:
||| `mu({ a >= j+1 }) + 1 = 2^{n-j}`, i.e. `mu({a >= j+1}) = 2^{n-j} - 1`.
||| Together with the mass normalisation this is the full (truncated) geometric
||| distribution of the Syracuse valuation random variable.
public export
tailGeoValuation :
  (n : Nat) -> (j : Nat) ->
  plus (massGe (S j) (geoValuation n)) 1 = pow2 (minus n j)
tailGeoValuation Z j = Refl
tailGeoValuation (S k) Z =
  rewrite massGeShift1 0 (geoValuation k) in
  rewrite massGeZero (geoValuation k) in
  rewrite sym (plusAssociative (pow2 k) (mass (geoValuation k)) 1) in
  rewrite massGeoValuationPlusOne k in
  Refl
tailGeoValuation (S k) (S i) =
  rewrite massGeShift1 (S i) (geoValuation k) in
  tailGeoValuation k i

--------------------------------------------------------------------------------
-- Exponential (sub-exponential) tail bound.
--------------------------------------------------------------------------------

||| The valuation tail decays exponentially: `mu({a >= j+1}) <= 2^{n-j}`.
||| This is the elementary large-deviation control (item C3) that the paper's
||| sub-Gaussian estimates refine.
public export
tailGeoValuationLe :
  (n : Nat) -> (j : Nat) ->
  Leq (massGe (S j) (geoValuation n)) (pow2 (minus n j))
tailGeoValuationLe n j =
  leqCastR (leqPlusExtraRight (massGe (S j) (geoValuation n)) 1)
           (tailGeoValuation n j)

--------------------------------------------------------------------------------
-- Exact geometric halving law of the tail.
--------------------------------------------------------------------------------

||| Below the support boundary the tail difference is exactly one step of the
||| `minus`: `minus n j = S (minus n (S j))` whenever `j < n`.
public export
minusSuccStep :
  (n : Nat) -> (j : Nat) -> Leq (S j) n -> minus n j = S (minus n (S j))
minusSuccStep (S n) Z _ = cong S (sym (minusZeroRight n))
minusSuccStep (S n) (S j) (LeqS le) = minusSuccStep n j le

||| `pow2 (S m) = 2 * pow2 m`.
public export
pow2Succ : (m : Nat) -> pow2 (S m) = mult 2 (pow2 m)
pow2Succ m = cong (plus (pow2 m)) (sym (plusZeroRightNeutral (pow2 m)))

||| Exact geometric decay of the survival function:
||| `mu({a >= j}) = 2 * mu({a >= j+1})` (in the `+1`-shifted, subtraction-free
||| form), valid for every `j < n`.  This is `P(a >= j) = 2 P(a >= j+1)`, the
||| defining ratio of the geometric valuation law.
public export
tailHalving :
  (n : Nat) -> (j : Nat) -> Leq (S j) n ->
  plus (massGe (S j) (geoValuation n)) 1
    = mult 2 (plus (massGe (S (S j)) (geoValuation n)) 1)
tailHalving n j le =
  rewrite tailGeoValuation n j in
  rewrite tailGeoValuation n (S j) in
  rewrite minusSuccStep n j le in
  pow2Succ (minus n (S j))

--------------------------------------------------------------------------------
-- Complementary distribution function.
--------------------------------------------------------------------------------

||| The lower part of the measure: total mass sitting at values `< t`.
public export
massLt : Nat -> FinDist -> Nat
massLt t Empty = Z
massLt t (Atom v w r) = case decLeq t v of
  IsLeq _ => massLt t r
  IsGt _ => plus w (massLt t r)

||| The distribution function and the survival function are complementary:
||| `mu({x < t}) + mu({x >= t}) = mu(Nat)`.
public export
massLtGeComplement :
  (t : Nat) -> (d : FinDist) -> plus (massLt t d) (massGe t d) = mass d
massLtGeComplement t Empty = Refl
massLtGeComplement t (Atom v w r) with (decLeq t v)
  _ | IsLeq _ =
    -- massLt = massLt r ; massGe = w + massGe r ; mass = w + mass r
    rewrite plusCommutative (massLt t r) (plus w (massGe t r)) in
    rewrite sym (plusAssociative w (massGe t r) (massLt t r)) in
    rewrite plusCommutative (massGe t r) (massLt t r) in
    rewrite massLtGeComplement t r in
    Refl
  _ | IsGt _ =
    -- massLt = w + massLt r ; massGe = massGe r ; mass = w + mass r
    rewrite sym (plusAssociative w (massLt t r) (massGe t r)) in
    rewrite massLtGeComplement t r in
    Refl

--------------------------------------------------------------------------------
-- Markov's inequality on the genuine valuation distribution.
--------------------------------------------------------------------------------

||| Markov's inequality specialised to the real valuation measure:
||| `t * mu({a >= t}) <= E[a] * (2^n - 1)`, i.e. `t * mu({a >= t}) <= weightedSum`.
public export
markovGeoValuation :
  (t : Nat) -> (n : Nat) ->
  Leq (mult t (massGe t (geoValuation n))) (weightedSum (geoValuation n))
markovGeoValuation t n = markov t (geoValuation n)

||| The closed-form first moment threaded through Markov: with
||| `weightedSum (geoValuation n) + (n+2) = 2 * 2^n`, Markov yields
||| `t * mu({a >= t}) + (n+2) <= 2^{n+1}`.
public export
markovGeoValuationClosed :
  (t : Nat) -> (n : Nat) ->
  Leq (plus (mult t (massGe t (geoValuation n))) (S (S n))) (mult 2 (pow2 n))
markovGeoValuationClosed t n =
  leqCastR
    (leqAdd (markovGeoValuation t n) (leqRefl (S (S n))))
    (weightedSumGeoValuation n)

--------------------------------------------------------------------------------
-- Concrete sanity checks.
--------------------------------------------------------------------------------

||| Over 3 scales: `mu({a >= 2}) = 2^{3-1} - 1 = 3`.
public export
tailThreeAtTwo : massGe 2 (geoValuation 3) = 3
tailThreeAtTwo = Refl

||| Exact tail identity at `n = 3, j = 1`: `mu({a >= 2}) + 1 = 2^2 = 4`.
public export
tailGeoThreeOne : plus (massGe 2 (geoValuation 3)) 1 = 4
tailGeoThreeOne = tailGeoValuation 3 1

||| Halving check at `n = 3, j = 1`: `mu({a>=2})+1 = 2*(mu({a>=3})+1)`.
public export
tailHalvingThreeOne :
  plus (massGe 2 (geoValuation 3)) 1 = mult 2 (plus (massGe 3 (geoValuation 3)) 1)
tailHalvingThreeOne = tailHalving 3 1 (LeqS (LeqS LeqZ))
