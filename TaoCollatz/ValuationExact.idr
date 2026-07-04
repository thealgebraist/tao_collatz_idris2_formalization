module TaoCollatz.ValuationExact

-- A GENERALIZATION that subsumes large chunks of the elementary valuation /
-- descent development.
--
-- `DropTimeExact` proved the 2-adic drop time exactly in the first three cases
-- (`= 0` for odd, `= 1` for `2 || m`, `= 2` for `4 || m`), each by a bespoke
-- computation, and `ValuationTwoClass` proved `syrValuation (8t+1) = 2` by yet
-- another bespoke half/half chase.  All of these are instances of a single
-- general fact, proved here once and for all:
--
--     for every `k` and every ODD `m`,   oddPartDropTime (2^k * m) = k.
--
-- i.e. the 2-adic valuation of `2^k * m` is exactly `k`.  From it we get, in one
-- line each:
--
--   * the whole exact drop-time ladder `= 0, 1, 2, ..., k, ...` (the special
--     cases of `DropTimeExact` become corollaries, and every higher value is
--     free);
--   * the *exact* Syracuse valuation from any 2-adic factorisation of `3n+1`
--     (`syrValuationFromFactor`), which gobbles up the residue-class valuation
--     computations (e.g. `ValuationTwoClass`);
--   * a single clean descent criterion `syrValuation n >= 2 ==> Syr(n) <= n`,
--     from which every "good step" / descending-family lemma follows.
--
-- Everything here is real mathematics: `%default total`, no placeholders, no
-- `believe_me`, no axioms, no holes.

import TaoCollatz.Core
import TaoCollatz.Dynamics
import TaoCollatz.TwoAdic
import TaoCollatz.SyracuseStructure
import TaoCollatz.SyracuseDescent
import TaoCollatz.FirstPassageDescent
import TaoCollatz.ValuationBounds
import TaoCollatz.DropTimeExact
import TaoCollatz.GoodStep
import TaoCollatz.Density
import Data.Nat

%default total

--------------------------------------------------------------------------------
-- Small arithmetic helpers.
--------------------------------------------------------------------------------

||| An odd number is positive (`isEven 0 = True`, so an odd number is a successor).
public export
oddImpliesPos : (m : Nat) -> isEven m = False -> Leq (S Z) m
oddImpliesPos Z h = void (falseNotTrue (sym h))
oddImpliesPos (S k) _ = LeqS LeqZ

||| A product of two positive numbers is positive.
public export
multPos : (a : Nat) -> (b : Nat) -> Leq (S Z) a -> Leq (S Z) b -> Leq (S Z) (mult a b)
multPos Z b apos _ = void (notLeqSZ apos)
multPos (S a') b _ bpos = leqTrans bpos (leqPlusExtraRight b (mult a' b))

||| `2^0 * m = m` (definitionally `plus m 0`, resolved by `plusZeroRightNeutral`).
public export
pow2ZeroMult : (m : Nat) -> mult (pow2 Z) m = m
pow2ZeroMult m = plusZeroRightNeutral m

||| `2^(k+1) * m = (2^k * m) + (2^k * m)`: multiplying by the next power of two
||| is doubling.
public export
pow2SuccMult :
  (k : Nat) -> (m : Nat) ->
  mult (pow2 (S k)) m = plus (mult (pow2 k) m) (mult (pow2 k) m)
pow2SuccMult k m = multDistributesOverPlusLeft (pow2 k) (pow2 k) m

--------------------------------------------------------------------------------
-- The general exact 2-adic valuation.
--------------------------------------------------------------------------------

||| Fuelled form: with enough fuel, the drop time of `2^k * m` for odd `m` is
||| exactly `k`.  Proved by induction on `k`, peeling one factor of two per step.
public export
dropTimeFuelPowOdd :
  (fuel : Nat) -> (k : Nat) -> (m : Nat) ->
  isEven m = False -> Leq (mult (pow2 k) m) fuel ->
  oddPartDropTimeFuel fuel (mult (pow2 k) m) = k
dropTimeFuelPowOdd fuel Z m hodd hle =
  rewrite pow2ZeroMult m in dropTimeFuelZeroOfOdd fuel m hodd
dropTimeFuelPowOdd Z (S k) m hodd hle =
  let valPos : Leq (S Z) (mult (pow2 (S k)) m)
      valPos = multPos (pow2 (S k)) m (pow2Positive (S k)) (oddImpliesPos m hodd)
  in void (notLeqSZ (leqTrans valPos hle))
dropTimeFuelPowOdd (S f) (S k) m hodd hle =
  let v : Nat
      v = mult (pow2 k) m
      pt : mult (pow2 (S k)) m = plus v v
      pt = pow2SuccMult k m
      hle2 : Leq (plus v v) (S f)
      hle2 = leqCastL (sym pt) hle
      vf : Leq v f
      vf = leqCastL (sym (halfDouble v)) (halfLeqOfLeqSucc (plus v v) f hle2)
      ih : oddPartDropTimeFuel f v = k
      ih = dropTimeFuelPowOdd f k m hodd vf
  in rewrite pt in
     rewrite isEvenDoubleTrue v in
     cong S (trans (cong (oddPartDropTimeFuel f) (halfDouble v)) ih)

||| **The generalization.**  For every `k` and every odd `m`, the 2-adic drop
||| time of `2^k * m` is exactly `k`:
|||
|||     oddPartDropTime (2^k * m) = k.
public export
dropTimePowOdd :
  (k : Nat) -> (m : Nat) -> isEven m = False ->
  oddPartDropTime (mult (pow2 k) m) = k
dropTimePowOdd k m hodd =
  dropTimeFuelPowOdd (mult (pow2 k) m) k m hodd (leqRefl (mult (pow2 k) m))

--------------------------------------------------------------------------------
-- Corollary 1: the exact drop-time ladder (subsumes `DropTimeExact`).
--------------------------------------------------------------------------------

||| The base cases `= 0, 1, 2` of `DropTimeExact` (and every higher value) are
||| now single instances of the general lemma.  Drop time of an odd number.
public export
dropTimeZeroGen : (m : Nat) -> isEven m = False -> oddPartDropTime m = 0
dropTimeZeroGen m hodd =
  trans (cong oddPartDropTime (sym (pow2ZeroMult m))) (dropTimePowOdd 0 m hodd)

||| Drop time of `2 * (odd)` is exactly one.
public export
dropTimeOneGen : (m : Nat) -> isEven m = False -> oddPartDropTime (mult (pow2 1) m) = 1
dropTimeOneGen m hodd = dropTimePowOdd 1 m hodd

||| Drop time of `4 * (odd)` is exactly two.
public export
dropTimeTwoGen : (m : Nat) -> isEven m = False -> oddPartDropTime (mult (pow2 2) m) = 2
dropTimeTwoGen m hodd = dropTimePowOdd 2 m hodd

--------------------------------------------------------------------------------
-- Corollary 2: exact Syracuse valuation from any 2-adic factorisation.
--------------------------------------------------------------------------------

||| **The general valuation reader.**  If `3n+1 = 2^k * q` with `q` odd, then the
||| Syracuse valuation of `n` is exactly `k`.  This subsumes every residue-class
||| valuation computation (e.g. `ValuationTwoClass.valuationTwoOnClass1mod8`):
||| one only has to exhibit the factorisation.
public export
syrValuationFromFactor :
  (n : Nat) -> (k : Nat) -> (q : Nat) ->
  isEven q = False ->
  plus (mult 3 n) 1 = mult (pow2 k) q ->
  syrValuation n = k
syrValuationFromFactor n k q hodd heq =
  trans (cong oddPartDropTime heq) (dropTimePowOdd k q hodd)

--------------------------------------------------------------------------------
-- Corollary 3: a single clean descent criterion.
--------------------------------------------------------------------------------

||| `syrValuation n >= 2 ==> 2^(syrValuation n) >= 4`.
public export
pow2SyrGeFour : (n : Nat) -> Leq 2 (syrValuation n) -> Leq 4 (pow2 (syrValuation n))
pow2SyrGeFour n hge = pow2GeFourOfGeTwo (syrValuation n) hge

||| **The general descent criterion.**  Any odd `n` whose Syracuse valuation is
||| at least two descends in one step: `Syr(n) <= n`.  Every "good step" lemma
||| (the mod-4 residue family, `descendsWhenGoodStep`, `familyDescends`, ...) is
||| an instance: exhibit valuation `>= 2` (e.g. via `syrValuationFromFactor`).
public export
descendsFromValuationGeTwo :
  (n : Nat) -> Leq (S Z) n -> Leq 2 (syrValuation n) ->
  Leq (oddValue (Syr (MkOddPos n))) n
descendsFromValuationGeTwo n npos hge =
  syrDescends n npos (pow2SyrGeFour n hge)

||| First-passage form: valuation `>= 2` yields a `SyrBelow` witness at time one.
public export
belowFromValuationGeTwo :
  (n : Nat) -> Leq (S Z) n -> Leq 2 (syrValuation n) ->
  SyrBelow (MkOddPos n) n
belowFromValuationGeTwo n npos hge =
  syrOneStepBelow n n (descendsFromValuationGeTwo n npos hge)

||| Fully packaged: a 2-adic factorisation `3n+1 = 2^k * q` with `q` odd and
||| `k >= 2` yields descent directly.  This is the elementary "good step"
||| statement in its most reusable form.
public export
descendsFromFactorGeTwo :
  (n : Nat) -> (k : Nat) -> (q : Nat) ->
  Leq (S Z) n -> isEven q = False -> Leq 2 k ->
  plus (mult 3 n) 1 = mult (pow2 k) q ->
  Leq (oddValue (Syr (MkOddPos n))) n
descendsFromFactorGeTwo n k q npos hodd hk heq =
  descendsFromValuationGeTwo n npos
    (leqCastR hk (sym (syrValuationFromFactor n k q hodd heq)))

--------------------------------------------------------------------------------
-- The valuation LOWER bound (arbitrary, not-necessarily-odd cofactor).
--------------------------------------------------------------------------------

||| Fuelled form of the lower bound: the drop time of `2^k * s` is at least `k`
||| for any positive `s` (odd or not).  Same peeling induction as the exact
||| lemma, but without needing `s` odd, so it applies to every "good step" whose
||| `3n+1` is merely divisible by `2^k`.
public export
dropTimeFuelPowGe :
  (fuel : Nat) -> (k : Nat) -> (s : Nat) ->
  Leq (S Z) s -> Leq (mult (pow2 k) s) fuel ->
  Leq k (oddPartDropTimeFuel fuel (mult (pow2 k) s))
dropTimeFuelPowGe fuel Z s spos hle = LeqZ
dropTimeFuelPowGe Z (S k) s spos hle =
  let valPos : Leq (S Z) (mult (pow2 (S k)) s)
      valPos = multPos (pow2 (S k)) s (pow2Positive (S k)) spos
  in void (notLeqSZ (leqTrans valPos hle))
dropTimeFuelPowGe (S f) (S k) s spos hle =
  let v : Nat
      v = mult (pow2 k) s
      pt : mult (pow2 (S k)) s = plus v v
      pt = pow2SuccMult k s
      hle2 : Leq (plus v v) (S f)
      hle2 = leqCastL (sym pt) hle
      vf : Leq v f
      vf = leqCastL (sym (halfDouble v)) (halfLeqOfLeqSucc (plus v v) f hle2)
      ih : Leq k (oddPartDropTimeFuel f v)
      ih = dropTimeFuelPowGe f k s spos vf
  in rewrite pt in
     rewrite isEvenDoubleTrue v in
     LeqS (leqCastR ih (cong (oddPartDropTimeFuel f) (sym (halfDouble v))))

||| **The general valuation lower bound.**  For every `k` and every positive `s`,
||| the 2-adic drop time of `2^k * s` is at least `k`.  Subsumes the good-step
||| valuation bounds (`dropTimeGeTwo` etc.): if `2^k | (3n+1)` then
||| `syrValuation n >= k`.
public export
dropTimePowGe :
  (k : Nat) -> (s : Nat) -> Leq (S Z) s ->
  Leq k (oddPartDropTime (mult (pow2 k) s))
dropTimePowGe k s spos =
  dropTimeFuelPowGe (mult (pow2 k) s) k s spos (leqRefl (mult (pow2 k) s))

||| **The most reusable good-step descent.**  If `3n+1 = 2^k * s` with `s >= 1`
||| and `k >= 2` (i.e. `4 | (3n+1)`), then one Syracuse step descends -- with NO
||| oddness requirement on `s`.  Every descending-family lemma (the mod-4 family
||| `familyDescends`, `descendsWhenGoodStep`, ...) is a direct instance.
public export
descendsFromFactorPow2 :
  (n : Nat) -> (k : Nat) -> (s : Nat) ->
  Leq (S Z) n -> Leq (S Z) s -> Leq 2 k ->
  plus (mult 3 n) 1 = mult (pow2 k) s ->
  Leq (oddValue (Syr (MkOddPos n))) n
descendsFromFactorPow2 n k s npos spos hk heq =
  descendsFromValuationGeTwo n npos
    (leqTrans hk
      (leqCastR (dropTimePowGe k s spos)
        (cong oddPartDropTime (sym heq))))
