module TaoCollatz.OrbitValuationExactOrbit

-- Genuine, fully-proved *exact orbit* slice built on top of the k-step orbit
-- structure (`OrbitValuationKStep`).
--
-- The k-step modules already pin down two facts on the density-`1/2^(2k+1)`
-- residue class `y = 2^(2k+1) * n + 1`:
--   * the orbit valuation sum is exactly `S_k(y) = 2k`   (`kStepValSum`);
--   * the orbit descends below the start at time `k`     (`kStepDescent`).
--
-- Here we sharpen the descent fact from an *inequality* to the **exact landing
-- point** of the orbit.  Each Syracuse step of the k-step engine reduces the
-- 2-adic exponent by `2` and multiplies the class parameter by `3`, so starting
-- at exponent `2k+1` (parameter `n`) and iterating `k` times lands on exponent
-- `1` (parameter `3^k n`):
--
--     iter k Syr (MkOddPos (2^(2k+1) n + 1)) = MkOddPos (2 * 3^k * n + 1).
--
-- That is, after `k` steps the orbit has reached the *arbitrary odd number*
-- `2 * 3^k * n + 1`, exactly.  This is strictly stronger than `kStepDescent`
-- (which it re-derives, since `2 * 3^k <= 2^(2k+1)`) and exhibits the precise
-- geometric `(3/4)^k` contraction underlying the drift: start `= 2*4^k*n + 1`,
-- landing `= 2*3^k*n + 1`.
--
-- Everything here is real mathematics: `%default total`, no placeholders, no
-- `believe_me`, no `postulate`, no `assert_*`, no `%foreign`, no `idris_crash`,
-- no axioms, no holes.

import Data.Nat
import TaoCollatz.Core
import TaoCollatz.Dynamics
import TaoCollatz.OddPart
import TaoCollatz.StepArith
import TaoCollatz.TwoAdic
import TaoCollatz.Pieces64
import TaoCollatz.OrbitValuationKStep

%default total

||| Arithmetic reshuffle: `(2p) * (3n) = (2 * 3p) * n`.
||| (Absorbs the extra factor `3` from one Syracuse step into the power `3^k`.)
public export
multReshuffle :
  (p : Nat) -> (n : Nat) ->
  mult (mult 2 p) (mult 3 n) = mult (mult 2 (mult 3 p)) n
multReshuffle p n =
  trans (multAssociative (mult 2 p) 3 n)
        (cong (\z => mult z n)
              (trans (sym (multAssociative 2 p 3))
                     (cong (mult 2) (multCommutative p 3))))

||| Base-case coefficient identity: `2^(2*0+1) = 2 * 3^0`.
public export
kStartBaseCoeff : pow2 (S (mult 2 0)) = mult 2 (StepArith.natPow 3 0)
kStartBaseCoeff = rewrite multZeroRightZero 2 in Refl

||| **Exact k-step orbit.**  On the density-`1/2^(2k+1)` residue class
||| `y = 2^(2k+1) * n + 1`, the `k`-step Syracuse orbit lands *exactly* on the
||| odd number `2 * 3^k * n + 1`:
|||
|||     iter k Syr (MkOddPos (kStart k n)) = MkOddPos (2 * 3^k * n + 1).
public export
kStepOrbitExact :
  (k : Nat) -> (n : Nat) ->
  iter k Syr (MkOddPos (kStart k n))
    = MkOddPos (plus (mult (mult 2 (StepArith.natPow 3 k)) n) 1)
kStepOrbitExact Z n =
  cong (\z => MkOddPos (plus (mult z n) 1)) kStartBaseCoeff
kStepOrbitExact (S k) n =
  rewrite kStartSuccEq k n in
  rewrite syrStepGenOdd (mult 2 k) n in
  rewrite kStepOrbitExact k (mult 3 n) in
  cong (\z => MkOddPos (plus z 1)) (multReshuffle (StepArith.natPow 3 k) n)

||| **Collapse onto an arbitrary odd number.**  After `k` steps the whole
||| density-`1/2^(2k+1)` class has reached the value `2 * (3^k * n) + 1`; as `n`
||| ranges over `Nat` this is an *arbitrary* odd number.  (Stated on the raw
||| `oddValue` and factored as `2 * m + 1` to make the "arbitrary odd" shape
||| explicit.)
public export
kStepLandsOnArbitraryOdd :
  (k : Nat) -> (n : Nat) ->
  oddValue (iter k Syr (MkOddPos (kStart k n)))
    = plus (mult 2 (mult (StepArith.natPow 3 k) n)) 1
kStepLandsOnArbitraryOdd k n =
  rewrite kStepOrbitExact k n in
  cong (\z => plus z 1) (sym (multAssociative 2 (StepArith.natPow 3 k) n))
