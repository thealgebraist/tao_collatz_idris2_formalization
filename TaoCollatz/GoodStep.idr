module TaoCollatz.GoodStep

-- Genuine, fully-proved characterisation of a "good" Syracuse step.
--
-- The descent lemma of `SyracuseDescent` needs valuation `>= 2`, i.e. `4`
-- divides `3n+1`.  Divisibility of `m` by four is exactly "`m` is even and
-- `m/2` is even".  This module proves, from first principles, that this
-- elementary mod-4 condition forces the 2-adic drop time of `m` to be at least
-- two, hence `2^v >= 4`, hence the Syracuse step descends:
--
--     3n+1 even, (3n+1)/2 even   ==>   Syr(n) <= n .
--
-- This closes the loop from a residue condition on `n` to genuine descent --
-- the elementary combinatorial input behind the first-passage analysis.
--
-- Everything here is real mathematics: `%default total`, no placeholders, no
-- `believe_me`, no axioms, no holes.

import TaoCollatz.Core
import TaoCollatz.Dynamics
import TaoCollatz.TwoAdic
import TaoCollatz.SyracuseStructure
import TaoCollatz.SyracuseDescent
import TaoCollatz.FirstPassageDescent
import TaoCollatz.Density

%default total

--------------------------------------------------------------------------------
-- Drop time is at least two when the number is divisible by four.
--------------------------------------------------------------------------------

||| Fuelled: an even positive number (with sufficient fuel) has drop time >= 1.
public export
dropTimeFuelGeOneOfEven :
  (fuel : Nat) -> (x : Nat) ->
  Leq (S Z) x -> Leq x fuel -> isEven x = True ->
  Leq (S Z) (oddPartDropTimeFuel fuel x)
dropTimeFuelGeOneOfEven Z x pos le _ = void (notLeqSZ (leqTrans pos le))
dropTimeFuelGeOneOfEven (S f) x pos le hev =
  rewrite hev in LeqS LeqZ

||| If `m` is even and `m/2` is even (i.e. `4 | m`), the 2-adic drop time of `m`
||| is at least two.
public export
dropTimeGeTwo :
  (m : Nat) ->
  isEven m = True -> Leq (S Z) (half m) -> isEven (half m) = True ->
  Leq 2 (oddPartDropTime m)
dropTimeGeTwo Z _ posHalf _ = void (notLeqSZ posHalf)
dropTimeGeTwo (S k) hev posHalf hhev =
  rewrite hev in
    LeqS (dropTimeFuelGeOneOfEven k (half (S k)) posHalf
            (halfLeqOfLeqSucc (S k) k (leqRefl (S k))) hhev)

--------------------------------------------------------------------------------
-- `2^dt >= 4` when `dt >= 2`.
--------------------------------------------------------------------------------

public export
pow2GeFourOfGeTwo : (dt : Nat) -> Leq 2 dt -> Leq 4 (pow2 dt)
pow2GeFourOfGeTwo Z prf = void (notLeqSZ prf)
pow2GeFourOfGeTwo (S Z) (LeqS inner) = void (notLeqSZ inner)
pow2GeFourOfGeTwo (S (S e)) (LeqS (LeqS LeqZ)) =
  leqAdd (leqAdd (pow2Positive e) (pow2Positive e))
         (leqAdd (pow2Positive e) (pow2Positive e))

--------------------------------------------------------------------------------
-- The good-step valuation bound and descent.
--------------------------------------------------------------------------------

||| If `3n+1` is divisible by four (even, with even half) then the Syracuse
||| valuation is at least two: `2^v >= 4`.
public export
valuationGeFourOfGoodStep :
  (n : Nat) ->
  isEven (plus (mult 3 n) 1) = True ->
  Leq (S Z) (half (plus (mult 3 n) 1)) ->
  isEven (half (plus (mult 3 n) 1)) = True ->
  Leq 4 (pow2 (syrValuation n))
valuationGeFourOfGoodStep n hev posHalf hhev =
  pow2GeFourOfGeTwo (syrValuation n)
    (dropTimeGeTwo (plus (mult 3 n) 1) hev posHalf hhev)

||| The good-step descent: if `3n+1` is divisible by four, one Syracuse step
||| does not increase the value (`Syr(n) <= n`), for `n >= 1`.
public export
descendsWhenGoodStep :
  (n : Nat) ->
  Leq (S Z) n ->
  isEven (plus (mult 3 n) 1) = True ->
  Leq (S Z) (half (plus (mult 3 n) 1)) ->
  isEven (half (plus (mult 3 n) 1)) = True ->
  Leq (oddValue (Syr (MkOddPos n))) n
descendsWhenGoodStep n h1 hev posHalf hhev =
  syrDescends n h1 (valuationGeFourOfGoodStep n hev posHalf hhev)

||| First-passage form of the good step: it yields a `SyrBelow` witness.
public export
goodStepBelow :
  (n : Nat) ->
  Leq (S Z) n ->
  isEven (plus (mult 3 n) 1) = True ->
  Leq (S Z) (half (plus (mult 3 n) 1)) ->
  isEven (half (plus (mult 3 n) 1)) = True ->
  SyrBelow (MkOddPos n) n
goodStepBelow n h1 hev posHalf hhev =
  syrOneStepBelow n n (descendsWhenGoodStep n h1 hev posHalf hhev)

--------------------------------------------------------------------------------
-- Concrete sanity check: n = 5, 3*5+1 = 16 = 4*4, good step, Syr(5) = 1 <= 5.
--------------------------------------------------------------------------------

public export
fiveGoodStepBelow : SyrBelow (MkOddPos 5) 5
fiveGoodStepBelow =
  goodStepBelow 5 (LeqS LeqZ) Refl (LeqS LeqZ) Refl
