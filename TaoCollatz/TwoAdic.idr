module TaoCollatz.TwoAdic

-- Genuine, fully-proved 2-adic infrastructure for the odd-part / Syracuse map.
--
-- The odd part of a positive integer and its 2-adic valuation are the basic
-- data the Syracuse map is built on (`Syr` divides out all factors of two).
-- This module makes that structure explicit and *proves*, from first
-- principles, the fundamental factorisation
--
--     n = oddFactor n * 2 ^ (oddPartDropTime n)          (for every n)
--
-- together with the fact that `oddFactor n` is genuinely odd for `n >= 1`.
-- These are the honest arithmetic facts (part of the "Syracuse valuation
-- variables" infrastructure, item C2 of `REMAINING_WORK.md`) that any real
-- formalisation of the paper's 2-adic analysis must rest on.
--
-- Everything here is real mathematics: `%default total`, no placeholders, no
-- `believe_me`, no axioms, no holes.

import TaoCollatz.Core
import TaoCollatz.Dynamics
import Data.Nat

%default total

--------------------------------------------------------------------------------
-- Small contradiction helpers.
--------------------------------------------------------------------------------

public export
notLeqSZ : Leq (S m) Z -> Void
notLeqSZ LeqZ impossible

public export
falseNotTrue : (False = True) -> Void
falseNotTrue Refl impossible

--------------------------------------------------------------------------------
-- Powers of two.
--------------------------------------------------------------------------------

||| `pow2 k = 2 ^ k`, defined by doubling so it reduces to a `plus` (matching
||| the additive shape of the counting arguments elsewhere in the development).
public export
pow2 : Nat -> Nat
pow2 Z = S Z
pow2 (S k) = plus (pow2 k) (pow2 k)

public export
pow2Positive : (k : Nat) -> Leq (S Z) (pow2 k)
pow2Positive Z = leqRefl (S Z)
pow2Positive (S k) =
  leqTrans (pow2Positive k) (leqPlusExtraRight (pow2 k) (pow2 k))
  where
    leqPlusExtraRight : (a : Nat) -> (d : Nat) -> Leq a (plus a d)
    leqPlusExtraRight Z d = LeqZ
    leqPlusExtraRight (S a) d = LeqS (leqPlusExtraRight a d)

--------------------------------------------------------------------------------
-- Elementary facts about `half` and `isEven`.
--------------------------------------------------------------------------------

||| `half n <= n`.
public export
leqSuccRightLocal : (n : Nat) -> Leq n (S n)
leqSuccRightLocal Z = LeqZ
leqSuccRightLocal (S n) = LeqS (leqSuccRightLocal n)

public export
halfLeqSelf : (n : Nat) -> Leq (half n) n
halfLeqSelf Z = LeqZ
halfLeqSelf (S Z) = LeqZ
halfLeqSelf (S (S k)) =
  LeqS (leqTrans (halfLeqSelf k) (leqSuccRightLocal k))

||| If `n <= S fuel` then `half n <= fuel`: halving strictly shrinks (except at
||| zero), so it fits inside a fuel one smaller.
public export
halfLeqOfLeqSucc : (n : Nat) -> (fuel : Nat) -> Leq n (S fuel) -> Leq (half n) fuel
halfLeqOfLeqSucc Z fuel _ = LeqZ
halfLeqOfLeqSucc (S Z) fuel _ = LeqZ
halfLeqOfLeqSucc (S (S k)) fuel (LeqS h) =
  leqTrans (LeqS (halfLeqSelf k)) h

||| An even number is exactly twice its half.
public export
evenHalf : (n : Nat) -> isEven n = True -> plus (half n) (half n) = n
evenHalf Z _ = Refl
evenHalf (S Z) Refl impossible
evenHalf (S (S k)) h =
  rewrite sym (plusSuccRightSucc (half k) (half k)) in
  rewrite evenHalf k h in Refl

||| A positive even number has a positive half.
public export
evenHalfPos : (n : Nat) -> Leq (S Z) n -> isEven n = True -> Leq (S Z) (half n)
evenHalfPos Z pos _ = void (notLeqSZ pos)
evenHalfPos (S Z) _ evp = void (falseNotTrue evp)
evenHalfPos (S (S m)) _ _ = LeqS LeqZ

--------------------------------------------------------------------------------
-- The fundamental 2-adic factorisation.
--------------------------------------------------------------------------------

||| Fuelled form: whenever the fuel suffices (`n <= fuel`), the run of
||| `oddFactorFuel` / `oddPartDropTimeFuel` gives an exact factorisation
||| `n = oddFactorFuel fuel n * 2 ^ (oddPartDropTimeFuel fuel n)`.
public export
factorFueled :
  (fuel : Nat) -> (n : Nat) -> Leq n fuel ->
  n = mult (oddFactorFuel fuel n) (pow2 (oddPartDropTimeFuel fuel n))
factorFueled Z Z LeqZ = Refl
factorFueled (S f) n le with (isEven n) proof evenProof
  factorFueled (S f) n le | True =
    let ih = factorFueled f (half n) (halfLeqOfLeqSucc n f le) in
    trans (sym (evenHalf n evenProof))
          (trans (cong (\z => plus z z) ih)
                 (sym (multDistributesOverPlusRight
                         (oddFactorFuel f (half n))
                         (pow2 (oddPartDropTimeFuel f (half n)))
                         (pow2 (oddPartDropTimeFuel f (half n))))))
  factorFueled (S f) n le | False =
    sym (multOneRightNeutral n)

||| The 2-adic factorisation of any natural number:
||| `n = oddFactor n * 2 ^ (oddPartDropTime n)`.
public export
oddFactorization :
  (n : Nat) -> n = mult (oddFactor n) (pow2 (oddPartDropTime n))
oddFactorization n = factorFueled n n (leqRefl n)

--------------------------------------------------------------------------------
-- The odd part is genuinely odd.
--------------------------------------------------------------------------------

||| Fuelled form: for a positive `n` with sufficient fuel, the extracted factor
||| is odd (`isEven = False`).
public export
oddFactorFuelOdd :
  (fuel : Nat) -> (n : Nat) -> Leq (S Z) n -> Leq n fuel ->
  isEven (oddFactorFuel fuel n) = False
oddFactorFuelOdd Z Z pos LeqZ = void (notLeqSZ pos)
oddFactorFuelOdd (S f) n pos le with (isEven n) proof evenProof
  oddFactorFuelOdd (S f) n pos le | True =
    oddFactorFuelOdd f (half n)
      (evenHalfPos n pos evenProof)
      (halfLeqOfLeqSucc n f le)
  oddFactorFuelOdd (S f) n pos le | False =
    evenProof

||| For every `n >= 1`, the odd part `oddFactor n` is genuinely odd.
public export
oddFactorIsOdd :
  (n : Nat) -> Leq (S Z) n -> isEven (oddFactor n) = False
oddFactorIsOdd n pos = oddFactorFuelOdd n n pos (leqRefl n)

--------------------------------------------------------------------------------
-- Small sanity checks (concrete, machine-checked instances).
--------------------------------------------------------------------------------

public export
factorTwelveExample : the Nat 12 = mult (oddFactor 12) (pow2 (oddPartDropTime 12))
factorTwelveExample = Refl

public export
factorFortyExample : the Nat 40 = mult (oddFactor 40) (pow2 (oddPartDropTime 40))
factorFortyExample = Refl

public export
oddFactorFortyOdd : isEven (oddFactor 40) = False
oddFactorFortyOdd = Refl
