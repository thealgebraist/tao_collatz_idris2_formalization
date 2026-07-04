module TaoCollatz.DropTimeExact

-- Genuine, fully-proved *exact* values of the 2-adic drop time in the smallest
-- cases.  `TwoAdic` / `GoodStep` established *lower* bounds on the drop time
-- (`oddPartDropTime`), which is all descent needs.  The distribution of the
-- Syracuse valuation, however, is governed by *exact* valuations: how many `n`
-- have valuation exactly `1`, exactly `2`, and so on.  This module proves the
-- exact base cases of that ladder:
--
--   * if `x` is odd then `oddPartDropTime x = 0` (`dropTimeZeroOfOdd`);
--   * if `m` is even and `m/2` is odd (`2 \|\| m`) then `oddPartDropTime m = 1`
--     (`dropTimeExactlyOne`).
--
-- Both are proved for the fuelled recursor first (so they hold for *any*
-- sufficient fuel, matching the way `oddPartDropTime n = oddPartDropTimeFuel n n`
-- is unfolded) and then specialised.  Together with the drop-time lower bounds
-- these pin the valuation exactly, which is what a real formalisation of the
-- geometric valuation distribution (item C2 of `REMAINING_WORK.md`) needs.
--
-- Everything here is real mathematics: `%default total`, no placeholders, no
-- `believe_me`, no axioms, no holes.

import TaoCollatz.Core
import TaoCollatz.Dynamics
import TaoCollatz.TwoAdic
import TaoCollatz.Density
import Data.Nat

%default total

--------------------------------------------------------------------------------
-- `half` of a doubled number.
--------------------------------------------------------------------------------

||| `half (m + m) = m`.
public export
halfDouble : (m : Nat) -> half (plus m m) = m
halfDouble Z = Refl
halfDouble (S k) = rewrite twoSk k in cong S (halfDouble k)

--------------------------------------------------------------------------------
-- Drop time of an odd number is zero.
--------------------------------------------------------------------------------

||| For odd `x`, the fuelled drop time is `0` regardless of the fuel: the very
||| first parity test fails, so no factor of two is removed.
public export
dropTimeFuelZeroOfOdd :
  (fuel : Nat) -> (x : Nat) -> isEven x = False -> oddPartDropTimeFuel fuel x = Z
dropTimeFuelZeroOfOdd Z x _ = Refl
dropTimeFuelZeroOfOdd (S f) x hodd = rewrite hodd in Refl

||| For odd `x`, `oddPartDropTime x = 0`.
public export
dropTimeZeroOfOdd :
  (x : Nat) -> isEven x = False -> oddPartDropTime x = Z
dropTimeZeroOfOdd x hodd = dropTimeFuelZeroOfOdd x x hodd

--------------------------------------------------------------------------------
-- Drop time is exactly one when the number is even with odd half.
--------------------------------------------------------------------------------

||| Fuelled form: if `m` is even, `m/2` is odd, `m >= 1`, and the fuel suffices,
||| then the drop time is exactly one -- one factor of two is removed and then
||| an odd number is reached.
public export
dropTimeFuelExactlyOne :
  (fuel : Nat) -> (m : Nat) ->
  Leq (S Z) m -> Leq m fuel ->
  isEven m = True -> isEven (half m) = False ->
  oddPartDropTimeFuel fuel m = 1
dropTimeFuelExactlyOne Z m pos le _ _ = void (notLeqSZ (leqTrans pos le))
dropTimeFuelExactlyOne (S f) m _ _ heven hoddHalf =
  rewrite heven in cong S (dropTimeFuelZeroOfOdd f (half m) hoddHalf)

||| If `m` is even and `m/2` is odd (i.e. `2` exactly divides `m`), then
||| `oddPartDropTime m = 1`.
public export
dropTimeExactlyOne :
  (m : Nat) ->
  Leq (S Z) m -> isEven m = True -> isEven (half m) = False ->
  oddPartDropTime m = 1
dropTimeExactlyOne m pos heven hoddHalf =
  dropTimeFuelExactlyOne m m pos (leqRefl m) heven hoddHalf

--------------------------------------------------------------------------------
-- Drop time is exactly two when `4 || m` (even, even half, odd quarter).
--------------------------------------------------------------------------------

||| Fuelled form: if `m` is even, `m/2` is even, `m/4` is odd, `m >= 1`, and the
||| fuel suffices, the drop time is exactly two.
public export
dropTimeFuelExactlyTwo :
  (fuel : Nat) -> (m : Nat) ->
  Leq (S Z) m -> Leq m fuel ->
  isEven m = True -> isEven (half m) = True -> isEven (half (half m)) = False ->
  oddPartDropTimeFuel fuel m = 2
dropTimeFuelExactlyTwo Z m pos le _ _ _ = void (notLeqSZ (leqTrans pos le))
dropTimeFuelExactlyTwo (S f) m pos le heven hevenHalf hoddQuarter =
  rewrite heven in
    cong S
      (dropTimeFuelExactlyOne f (half m)
         (evenHalfPos m pos heven)
         (halfLeqOfLeqSucc m f le)
         hevenHalf hoddQuarter)

||| If `m` is even, `m/2` is even and `m/4` is odd (i.e. `4` exactly divides
||| `m`), then `oddPartDropTime m = 2`.
public export
dropTimeExactlyTwo :
  (m : Nat) ->
  Leq (S Z) m -> isEven m = True -> isEven (half m) = True ->
  isEven (half (half m)) = False ->
  oddPartDropTime m = 2
dropTimeExactlyTwo m pos heven hevenHalf hoddQuarter =
  dropTimeFuelExactlyTwo m m pos (leqRefl m) heven hevenHalf hoddQuarter

--------------------------------------------------------------------------------
-- Concrete sanity checks.
--------------------------------------------------------------------------------

||| `10 = 2 * 5`, so `oddPartDropTime 10 = 1`.
public export
dropTimeTenExample : oddPartDropTime 10 = 1
dropTimeTenExample = dropTimeExactlyOne 10 (LeqS LeqZ) Refl Refl

||| `7` is odd, so `oddPartDropTime 7 = 0`.
public export
dropTimeSevenExample : oddPartDropTime 7 = 0
dropTimeSevenExample = dropTimeZeroOfOdd 7 Refl

||| `28 = 4 * 7`, so `oddPartDropTime 28 = 2`.
public export
dropTimeTwentyEightExample : oddPartDropTime 28 = 2
dropTimeTwentyEightExample = dropTimeExactlyTwo 28 (LeqS LeqZ) Refl Refl Refl
