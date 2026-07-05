module TaoCollatz.StepArith

-- Elementary arithmetic used to discharge the deterministic *growth side* of the
-- Syracuse descent (Step 2 of `HoleProof`): the closed inequality
-- `3^{5k} <= 2^{8k}` for every `k`.
--
-- Everything here is ordinary, total `Nat` arithmetic built on the project's
-- custom `Leq` and `pow2`.  There are no holes and no placeholders.

import TaoCollatz.Core
import TaoCollatz.TwoAdic
import TaoCollatz.Density
import Data.Nat

%default total

--------------------------------------------------------------------------------
-- Ordinary iterated product `b ^ k`.
--------------------------------------------------------------------------------

||| `natPow b k = b^k` (an ordinary iterated product on `Nat`).
public export
natPow : Nat -> Nat -> Nat
natPow _ Z = S Z
natPow b (S k) = mult b (natPow b k)

--------------------------------------------------------------------------------
-- Monotonicity of multiplication under `Leq`.
--------------------------------------------------------------------------------

||| Multiplication is monotone in its left factor (for a fixed left multiplier).
public export
leqMultLeft : (c : Nat) -> {b, d : Nat} -> Leq b d -> Leq (mult c b) (mult c d)
leqMultLeft Z bd = LeqZ
leqMultLeft (S k) bd = leqAdd bd (leqMultLeft k bd)

||| Swap the two outer factors of a right-nested product.
public export
mulSwapMid : (a : Nat) -> (b : Nat) -> (c : Nat) ->
  mult a (mult b c) = mult b (mult a c)
mulSwapMid a b c =
  trans (multAssociative a b c)
    (trans (cong (\z => mult z c) (multCommutative a b))
           (sym (multAssociative b a c)))

||| Multiplication is monotone in both factors simultaneously.
public export
multBothMono :
  {a, b, c, d : Nat} -> Leq a c -> Leq b d -> Leq (mult a b) (mult c d)
multBothMono {b} {c} ac bd =
  leqTrans (leqMultRight ac b) (leqMultLeft c bd)

--------------------------------------------------------------------------------
-- Powers of two form a multiplicative character of `(Nat, +)` (re-proved
-- locally to keep this module's dependencies minimal).
--------------------------------------------------------------------------------

||| `pow2 (a + b) = pow2 a * pow2 b`.
public export
pow2AddLocal : (a : Nat) -> (b : Nat) -> pow2 (plus a b) = mult (pow2 a) (pow2 b)
pow2AddLocal Z b = rewrite plusZeroRightNeutral (pow2 b) in Refl
pow2AddLocal (S k) b =
  rewrite pow2AddLocal k b in
  sym (multDistributesOverPlusLeft (pow2 k) (pow2 k) (pow2 b))

--------------------------------------------------------------------------------
-- Laws for `natPow`.
--------------------------------------------------------------------------------

||| `b^(m + n) = b^m * b^n`.
public export
natPowAdd :
  (b : Nat) -> (m : Nat) -> (n : Nat) ->
  natPow b (plus m n) = mult (natPow b m) (natPow b n)
natPowAdd b Z n = rewrite plusZeroRightNeutral (natPow b n) in Refl
natPowAdd b (S k) n =
  rewrite natPowAdd b k n in
  multAssociative b (natPow b k) (natPow b n)

||| `b^(m * k) = (b^m)^k`.
public export
powMulLaw :
  (b : Nat) -> (m : Nat) -> (k : Nat) ->
  natPow b (mult m k) = natPow (natPow b m) k
powMulLaw b m Z = rewrite multZeroRightZero m in Refl
powMulLaw b m (S j) =
  rewrite multRightSuccPlus m j in
  rewrite natPowAdd b m (mult m j) in
  rewrite powMulLaw b m j in
  Refl

||| `pow2 (m * k) = (pow2 m)^k`.
public export
pow2MulLaw :
  (m : Nat) -> (k : Nat) -> pow2 (mult m k) = natPow (pow2 m) k
pow2MulLaw m Z = rewrite multZeroRightZero m in Refl
pow2MulLaw m (S j) =
  rewrite multRightSuccPlus m j in
  rewrite pow2AddLocal m (mult m j) in
  rewrite pow2MulLaw m j in
  Refl

--------------------------------------------------------------------------------
-- Monotone powers and the closed growth bound.
--------------------------------------------------------------------------------

||| If `a <= b` then `a^k <= b^k`.
public export
iterGrowth :
  (a : Nat) -> (b : Nat) -> Leq a b -> (k : Nat) -> Leq (natPow a k) (natPow b k)
iterGrowth a b h Z = leqRefl (S Z)
iterGrowth a b h (S j) = multBothMono h (iterGrowth a b h j)

||| **Step 2, arithmetic core.**  From the strict single-block comparison
||| `3^5 <= 2^8`, the deterministic growth `3^{5k}` is dominated by the
||| contraction budget `2^{8k}` for every number of five-step blocks `k`.
public export
iteratedGrowthProof :
  Leq (natPow 3 5) (pow2 8) ->
  (k : Nat) -> Leq (natPow 3 (mult 5 k)) (pow2 (mult 8 k))
iteratedGrowthProof base5 k =
  rewrite powMulLaw 3 5 k in
  rewrite pow2MulLaw 8 k in
  iterGrowth (natPow 3 5) (pow2 8) base5 k
