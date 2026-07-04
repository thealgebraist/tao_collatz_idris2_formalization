module TaoCollatz.IteratedDescent

-- Genuine, fully-proved iterated (multi-step) descent for the Syracuse map.
--
-- `SyracuseDescent` / `GoodStep` give descent of a *single* step.  The
-- first-passage analysis of the paper is about *orbits*: it needs that if every
-- step along an orbit does not increase the value, the whole orbit stays at or
-- below its starting height.  This module proves exactly that, from the general
-- iteration lemma `iter (S k) f x = f (iter k f x)` (`iterSucc`):
--
--     (forall j, Syr(orbit_j) <= orbit_j)  ==>  orbit_k <= orbit_0   for all k.
--
-- As a concrete instance the fixed point `n = 1` gives a genuinely bounded
-- orbit.  This is the elementary "monotone orbit" input underlying the renewal
-- / stability estimate (item C5 of `REMAINING_WORK.md`).
--
-- Everything here is real mathematics: `%default total`, no placeholders, no
-- `believe_me`, no axioms, no holes.

import TaoCollatz.Core
import TaoCollatz.Dynamics
import TaoCollatz.Density
import Data.Nat

%default total

--------------------------------------------------------------------------------
-- The generic iteration-shift lemma.
--------------------------------------------------------------------------------

||| Applying `f` once more can be taken on either end of the iterate.
public export
iterSucc : (k : Nat) -> (f : a -> a) -> (x : a) -> iter (S k) f x = f (iter k f x)
iterSucc Z f x = Refl
iterSucc (S k) f x = iterSucc k f (f x)

--------------------------------------------------------------------------------
-- Iterated non-increase of the Syracuse orbit.
--------------------------------------------------------------------------------

||| If every Syracuse step along the orbit of `n` does not increase the value,
||| then no iterate exceeds the starting value.
public export
iterSyrNonIncreasing :
  (k : Nat) -> (n : OddPos) ->
  ((j : Nat) -> Leq (oddValue (Syr (iter j Syr n))) (oddValue (iter j Syr n))) ->
  Leq (oddValue (iter k Syr n)) (oddValue n)
iterSyrNonIncreasing Z n h = leqRefl (oddValue n)
iterSyrNonIncreasing (S k) n h =
  leqCastL (cong oddValue (iterSucc k Syr n))
    (leqTrans (h k) (iterSyrNonIncreasing k n h))

||| First-passage packaging: under per-step non-increase, the orbit is
||| immediately (and permanently) below its own starting value.
public export
nonIncreasingSyrBelow :
  (n : OddPos) ->
  ((j : Nat) -> Leq (oddValue (Syr (iter j Syr n))) (oddValue (iter j Syr n))) ->
  SyrBelow n (oddValue n)
nonIncreasingSyrBelow n h = Reaches 0 (leqRefl (oddValue n))

--------------------------------------------------------------------------------
-- Concrete instance: the fixed point `n = 1` has a bounded orbit.
--------------------------------------------------------------------------------

||| The Syracuse orbit of `1` is constantly `1` (`Syr 1 = 1`).
public export
syrOneFixed : (j : Nat) -> iter j Syr (MkOddPos 1) = MkOddPos 1
syrOneFixed Z = Refl
syrOneFixed (S j) = syrOneFixed j

||| Every step of the orbit of `1` is non-increasing.
public export
syrOneStepBound :
  (j : Nat) ->
  Leq (oddValue (Syr (iter j Syr (MkOddPos 1)))) (oddValue (iter j Syr (MkOddPos 1)))
syrOneStepBound j = rewrite syrOneFixed j in leqRefl 1

||| The orbit of `1` never exceeds `1`.
public export
orbitOneBounded : (k : Nat) -> Leq (oddValue (iter k Syr (MkOddPos 1))) 1
orbitOneBounded k = iterSyrNonIncreasing k (MkOddPos 1) syrOneStepBound
