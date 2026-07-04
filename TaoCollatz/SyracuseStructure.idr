module TaoCollatz.SyracuseStructure

-- Genuine, fully-proved structural facts about the Syracuse map `Syr`.
--
-- The Syracuse map sends an odd `n` to the odd part of `3n+1`.  Two facts are
-- fundamental for any 2-adic analysis of it (the "Syracuse valuation variables"
-- of item C2 in `REMAINING_WORK.md`):
--
--   * the output is again odd (`syrValueOdd`);
--   * the exact factorisation `3n+1 = Syr(n) * 2 ^ v`, where `v` is the 2-adic
--     valuation of `3n+1` (the geometric "valuation" random variable of the
--     paper) (`syrFactorization`).
--
-- Everything here is real mathematics: `%default total`, no placeholders, no
-- `believe_me`, no axioms, no holes.

import TaoCollatz.Core
import TaoCollatz.Dynamics
import TaoCollatz.TwoAdic
import Data.Nat

%default total

--------------------------------------------------------------------------------
-- Positivity of `3n+1`.
--------------------------------------------------------------------------------

||| `1 <= a + 1` for every `a`.
public export
oneLeqPlusOne : (a : Nat) -> Leq (S Z) (plus a (S Z))
oneLeqPlusOne Z = LeqS LeqZ
oneLeqPlusOne (S k) = LeqS LeqZ

||| `3n+1 >= 1`.
public export
threeNPlusOnePos : (n : Nat) -> Leq (S Z) (plus (mult 3 n) 1)
threeNPlusOnePos n = oneLeqPlusOne (mult 3 n)

--------------------------------------------------------------------------------
-- The Syracuse map produces odd values.
--------------------------------------------------------------------------------

||| The value produced by one Syracuse step is odd: `Syr` divides out every
||| factor of two from `3n+1`, so the result has none left.
public export
syrValueOdd : (n : Nat) -> isEven (oddValue (Syr (MkOddPos n))) = False
syrValueOdd n = oddFactorIsOdd (plus (mult 3 n) 1) (threeNPlusOnePos n)

--------------------------------------------------------------------------------
-- The Syracuse 2-adic factorisation (the valuation random variable).
--------------------------------------------------------------------------------

||| `syrValuation n` is the 2-adic valuation of `3n+1`: the number of factors of
||| two removed by one Syracuse step from the odd number `n`.  This is exactly
||| the paper's per-step geometric "valuation" random variable.
public export
syrValuation : Nat -> Nat
syrValuation n = oddPartDropTime (plus (mult 3 n) 1)

||| The defining factorisation of the Syracuse step:
||| `3n+1 = Syr(n) * 2 ^ (syrValuation n)`.
public export
syrFactorization :
  (n : Nat) ->
  plus (mult 3 n) 1 = mult (oddValue (Syr (MkOddPos n))) (pow2 (syrValuation n))
syrFactorization n = oddFactorization (plus (mult 3 n) 1)

--------------------------------------------------------------------------------
-- Concrete sanity checks.
--------------------------------------------------------------------------------

public export
syrSevenValueOdd : isEven (oddValue (Syr (MkOddPos 7))) = False
syrSevenValueOdd = Refl

public export
syrSevenFactorExample :
  the Nat 22 = mult (oddValue (Syr (MkOddPos 7))) (pow2 (syrValuation 7))
syrSevenFactorExample = Refl
