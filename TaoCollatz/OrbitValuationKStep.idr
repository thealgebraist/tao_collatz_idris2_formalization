module TaoCollatz.OrbitValuationKStep

-- Genuine, fully-proved *k-step* slice of the Syracuse orbit valuation
-- distribution, for **every** `k`, generalising the concrete one-, two- and
-- three-step slices (`ValuationTwoClass`, `OrbitValuationTwoStep`,
-- `OrbitValuationThreeStep`) by induction on the number of steps.
--
-- The pattern behind those slices is uniform.  On the residue class
--
--     y = 2^(2k+1) * n + 1        (density 1/2^(2k+1))
--
-- the first `k` Syracuse valuations are *all exactly two*, so the orbit
-- valuation sum is exactly `S_k(y) = 2k`, and the orbit descends below the start
-- at the positive time `k`.  The engine is a single Syracuse step
--
--     3(2^(p) * n + 1) + 1 = 2^2 * (2^(p-2) * (3n) + 1)      (p >= 3),
--
-- which reads valuation `2` and sends the class of exponent `p` (parameter `n`)
-- to the class of exponent `p-2` (parameter `3n`).  Starting at exponent
-- `2k+1` this can be iterated exactly `k` times while the exponent stays `>= 3`
-- (it lands on exponent `1`, i.e. an arbitrary odd number, after `k` steps).
--
-- `kStepValSum`   : `S_k(y) = 2k` on the class `y = 2^(2k+1) n + 1`.
-- `kStepDescent`  : `oddSize (iter k Syr y) <= oddSize y` (time-`k` descent).
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
import TaoCollatz.ValuationTail
import TaoCollatz.ValuationExact
import TaoCollatz.ValuationBounds
import TaoCollatz.ValuationTwoClass
import TaoCollatz.Pieces64
import TaoCollatz.OrbitValuationTwoStep

%default total

--------------------------------------------------------------------------------
-- Powers of two: `2^(q+3) = 4 * 2^(q+1) = 8 * 2^q`.
--------------------------------------------------------------------------------

||| `2^(q+1)` is even times anything: `isEven (2^(S q) * x) = True`.
public export
evenPow2SuccMult :
  (q : Nat) -> (x : Nat) -> isEven (mult (pow2 (S q)) x) = True
evenPow2SuccMult q x =
  rewrite multDistributesOverPlusLeft (pow2 q) (pow2 q) x in
  isEvenDoubleTrue (mult (pow2 q) x)

||| `2^(q+3) = 4 * 2^(q+1)`.
public export
pow2ThreeShift :
  (q : Nat) -> pow2 (S (S (S q))) = mult 4 (pow2 (S q))
pow2ThreeShift q =
  trans (pow2Succ (S (S q)))
        (trans (cong (mult 2) (pow2Succ (S q)))
               (multAssociative 2 2 (pow2 (S q))))

||| `2^(q+3) = 8 * 2^q`.
public export
pow2ThreeEq :
  (q : Nat) -> pow2 (S (S (S q))) = mult 8 (pow2 q)
pow2ThreeEq q =
  trans (pow2ThreeShift q)
        (trans (cong (mult 4) (pow2Succ q))
               (multAssociative 4 2 (pow2 q)))

--------------------------------------------------------------------------------
-- The abstract one-step arithmetic identity `3*(4a*n+1)+1 = 4*(a*3n+1)`.
--------------------------------------------------------------------------------

||| `3 * (4a * n) = 12 * (a*n)`.
public export
mulLeft12 :
  (a : Nat) -> (n : Nat) ->
  mult 3 (mult (mult 4 a) n) = mult (mult 12 a) n
mulLeft12 a n =
  trans (multAssociative 3 (mult 4 a) n)
        (cong (\z => mult z n) (multAssociative 3 4 a))

||| `4 * (a * 3n) = 12 * (a*n)`.
public export
mulRight12 :
  (a : Nat) -> (n : Nat) ->
  mult 4 (mult a (mult 3 n)) = mult (mult 12 a) n
mulRight12 a n =
  trans (multAssociative 4 a (mult 3 n))
        (trans (multAssociative (mult 4 a) 3 n)
               (cong (\z => mult z n)
                     (trans (multCommutative (mult 4 a) 3)
                            (multAssociative 3 4 a))))

||| The core one-step shuffle: `3 * (4a * n) = 4 * (a * 3n)`.
public export
mulShuffle :
  (a : Nat) -> (n : Nat) ->
  mult 3 (mult (mult 4 a) n) = mult 4 (mult a (mult 3 n))
mulShuffle a n = trans (mulLeft12 a n) (sym (mulRight12 a n))

||| `3 * (4a*n + 1) + 1 = 3*(4a*n) + 4`.
public export
lhsGen :
  (a : Nat) -> (n : Nat) ->
  plus (mult 3 (plus (mult (mult 4 a) n) 1)) 1
    = plus (mult 3 (mult (mult 4 a) n)) 4
lhsGen a n =
  rewrite multDistributesOverPlusRight 3 (mult (mult 4 a) n) 1 in
  sym (plusAssociative (mult 3 (mult (mult 4 a) n)) 3 1)

||| `2^2 * (a*3n + 1) = 4*(a*3n) + 4`.
public export
rhsGen :
  (a : Nat) -> (n : Nat) ->
  mult (pow2 2) (plus (mult a (mult 3 n)) 1)
    = plus (mult 4 (mult a (mult 3 n))) 4
rhsGen a n = multDistributesOverPlusRight 4 (mult a (mult 3 n)) 1

||| **The abstract one-step factorisation** `3*(4a*n+1)+1 = 2^2 * (a*3n+1)`.
public export
factorGen :
  (a : Nat) -> (n : Nat) ->
  plus (mult 3 (plus (mult (mult 4 a) n) 1)) 1
    = mult (pow2 2) (plus (mult a (mult 3 n)) 1)
factorGen a n =
  trans (lhsGen a n)
        (trans (cong (\z => plus z 4) (mulShuffle a n))
               (sym (rhsGen a n)))

--------------------------------------------------------------------------------
-- The class of exponent `q+3` and its one Syracuse step.
--------------------------------------------------------------------------------

||| The residue-class start `2^(q+3) * n + 1`.
public export
pClass : (q : Nat) -> (n : Nat) -> Nat
pClass q n = plus (mult (pow2 (S (S (S q)))) n) 1

||| `2^(q+3) * n = 8 * (2^q * n)`.
public export
classEqGen :
  (q : Nat) -> (n : Nat) ->
  mult (pow2 (S (S (S q)))) n = mult 8 (mult (pow2 q) n)
classEqGen q n =
  trans (cong (\z => mult z n) (pow2ThreeEq q))
        (sym (multAssociative 8 (pow2 q) n))

||| `a_1 = 2` on the class of exponent `q+3` (since it lies in `1 (mod 8)`).
public export
valGen :
  (q : Nat) -> (n : Nat) -> syrValuation (pClass q n) = 2
valGen q n =
  rewrite classEqGen q n in valuationTwoOnClass1mod8 (mult (pow2 q) n)

||| The odd cofactor `2^(q+1) * 3n + 1` is odd.
public export
oddCofGen :
  (q : Nat) -> (n : Nat) ->
  isEven (plus (mult (pow2 (S q)) (mult 3 n)) 1) = False
oddCofGen q n =
  trans (cong isEven (plusCommutative (mult (pow2 (S q)) (mult 3 n)) 1))
        (isEvenPlusEven 1 (mult (pow2 (S q)) (mult 3 n))
                        (evenPow2SuccMult q (mult 3 n)))

||| The concrete factorisation on the class of exponent `q+3`.
public export
factorPClass :
  (q : Nat) -> (n : Nat) ->
  plus (mult 3 (pClass q n)) 1
    = mult (pow2 2) (plus (mult (pow2 (S q)) (mult 3 n)) 1)
factorPClass q n =
  rewrite pow2ThreeShift q in factorGen (pow2 (S q)) n

||| **One Syracuse step**: the class of exponent `q+3` (param `n`) maps to the
||| class of exponent `q+1` (param `3n`).
public export
syrStepGen :
  (q : Nat) -> (n : Nat) ->
  oddValue (Syr (MkOddPos (pClass q n)))
    = plus (mult (pow2 (S q)) (mult 3 n)) 1
syrStepGen q n =
  rewrite factorPClass q n in
  oddFactorPow2Mult 2 (plus (mult (pow2 (S q)) (mult 3 n)) 1) (oddCofGen q n)

||| The `OddPos` form of the one Syracuse step.
public export
syrStepGenOdd :
  (q : Nat) -> (n : Nat) ->
  Syr (MkOddPos (pClass q n))
    = MkOddPos (plus (mult (pow2 (S q)) (mult 3 n)) 1)
syrStepGenOdd q n = cong MkOddPos (syrStepGen q n)

--------------------------------------------------------------------------------
-- The k-step orbit valuation sum, by induction on k.
--------------------------------------------------------------------------------

||| The `k`-step start `2^(2k+1) * n + 1`.
public export
kStart : (k : Nat) -> (n : Nat) -> Nat
kStart k n = plus (mult (pow2 (S (mult 2 k))) n) 1

||| The `(k+1)`-step start is the exponent-`(2k+3)` class start: `2^(2k+3) n + 1`.
public export
kStartSuccEq :
  (k : Nat) -> (n : Nat) -> kStart (S k) n = pClass (mult 2 k) n
kStartSuccEq k n =
  cong (\e => plus (mult (pow2 (S e)) n) 1) (multRightSuccPlus 2 k)

||| **Main result (valuation sum).**  On the density-`1/2^(2k+1)` residue class
||| `y = 2^(2k+1) * n + 1`, the `k`-step Syracuse orbit valuation sum is
||| *exactly* `S_k(y) = 2k`: every one of the first `k` orbit valuations is `2`.
public export
kStepValSum :
  (k : Nat) -> (n : Nat) ->
  syrValSum k (MkOddPos (kStart k n)) = mult 2 k
kStepValSum Z n = Refl
kStepValSum (S k) n =
  trans (cong (\z => syrValSum (S k) (MkOddPos z)) (kStartSuccEq k n))
        (trans (cong2 plus (valGen (mult 2 k) n)
                     (trans (cong (syrValSum k) (syrStepGenOdd (mult 2 k) n))
                            (kStepValSum k (mult 3 n))))
               (sym (multRightSuccPlus 2 k)))

--------------------------------------------------------------------------------
-- The time-k descent, by induction on k.
--------------------------------------------------------------------------------

||| First step descends: `oddSize (MkOddPos (kStart k (3n))) = Syr y <= y`, where
||| `y = 2^(2k+3) n + 1` is the exponent-`(2k+3)` start.
public export
headDescentGen :
  (k : Nat) -> (n : Nat) ->
  Leq (oddSize (MkOddPos (plus (mult (pow2 (S (mult 2 k))) (mult 3 n)) 1)))
      (pClass (mult 2 k) n)
headDescentGen k n =
  leqCastL (sym (syrStepGen (mult 2 k) n))
    (descendsFromValuationGeTwo (pClass (mult 2 k) n)
       (leqPlusExtraLeft (mult (pow2 (S (S (S (mult 2 k))))) n) 1)
       (leqCastR (leqRefl 2) (sym (valGen (mult 2 k) n))))

||| **Main result (descent).**  On the class `y = 2^(2k+1) * n + 1` the orbit
||| descends below the start at the positive time `k`:
||| `oddSize (iter k Syr y) <= oddSize y`.
public export
kStepDescent :
  (k : Nat) -> (n : Nat) ->
  Leq (oddSize (iter k Syr (MkOddPos (kStart k n))))
      (oddSize (MkOddPos (kStart k n)))
kStepDescent Z n = leqRefl (oddSize (MkOddPos (kStart Z n)))
kStepDescent (S k) n =
  leqCastL
    (cong (\z => oddSize (iter (S k) Syr (MkOddPos z))) (kStartSuccEq k n))
    (leqCastR
       (leqCastL
          (cong oddSize (cong (iter k Syr) (syrStepGenOdd (mult 2 k) n)))
          (leqTrans (kStepDescent k (mult 3 n)) (headDescentGen k n)))
       (sym (kStartSuccEq k n)))
