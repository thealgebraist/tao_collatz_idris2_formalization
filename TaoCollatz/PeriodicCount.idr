module TaoCollatz.PeriodicCount

-- Genuine, fully-proved counting infrastructure for *periodic* predicates.
--
-- Densities of the sets that occur in any Collatz/Syracuse density analysis are
-- governed by residues (mod `2^k`): the relevant predicates are periodic.  This
-- module proves, from first principles, the exact counting identity for a
-- period-`m` predicate over a whole number of periods:
--
--     count p (q * m) = q * (count p m)                  (p periodic with period m)
--
-- so the density of a period-`m` set is exactly (count over one period)/m.  It
-- also proves the two structural lemmas this rests on: additivity of `count`
-- over a split range (`countPlus`) and extensionality of `count`
-- (`countExt`).  These are part of the counting toolkit (item C1 of
-- `REMAINING_WORK.md`).
--
-- Everything here is real mathematics: `%default total`, no placeholders, no
-- `believe_me`, no axioms, no holes.

import TaoCollatz.Core
import TaoCollatz.Density
import Data.Nat

%default total

--------------------------------------------------------------------------------
-- Extensionality and additivity of `count`.
--------------------------------------------------------------------------------

||| If `p` and `q` agree pointwise then they have the same counts.
public export
countExt :
  (p : Nat -> Bool) -> (q : Nat -> Bool) ->
  ((i : Nat) -> p i = q i) -> (bigN : Nat) ->
  count p bigN = count q bigN
countExt p q h Z = Refl
countExt p q h (S k) =
  rewrite h k in
  rewrite countExt p q h k in Refl

||| A helper rearrangement: `x + (y + z) = y + (x + z)`.
public export
plusSwapMid : (x : Nat) -> (y : Nat) -> (z : Nat) -> plus x (plus y z) = plus y (plus x z)
plusSwapMid x y z =
  rewrite plusAssociative x y z in
  rewrite plusCommutative x y in
  sym (plusAssociative y x z)

||| Additivity of `count` over a split range: counting below `a + b` is counting
||| below `a` plus counting the shifted predicate below `b`.
public export
countPlus :
  (p : Nat -> Bool) -> (a : Nat) -> (b : Nat) ->
  count p (plus a b) = plus (count p a) (count (\i => p (plus a i)) b)
countPlus p a Z =
  rewrite plusZeroRightNeutral a in
  sym (plusZeroRightNeutral (count p a))
countPlus p a (S b') =
  rewrite sym (plusSuccRightSucc a b') in
  rewrite countPlus p a b' in
  plusSwapMid (indicator (p (plus a b'))) (count p a)
              (count (\i => p (plus a i)) b')

--------------------------------------------------------------------------------
-- Periodicity: a shift by a multiple of the period leaves the predicate fixed.
--------------------------------------------------------------------------------

||| If `p` has period `m` (`p (n + m) = p n`), then shifting by any multiple of
||| `m` leaves it unchanged: `p (q*m + i) = p i`.
public export
periodMultiple :
  (p : Nat -> Bool) -> (m : Nat) ->
  ((n : Nat) -> p (plus n m) = p n) ->
  (q : Nat) -> (i : Nat) ->
  p (plus (mult q m) i) = p i
periodMultiple p m period Z i = Refl
periodMultiple p m period (S q') i =
  rewrite sym (plusAssociative m (mult q' m) i) in
  trans (cong p (plusCommutative m (plus (mult q' m) i)))
        (trans (period (plus (mult q' m) i))
               (periodMultiple p m period q' i))

--------------------------------------------------------------------------------
-- The exact count of a periodic predicate over full periods.
--------------------------------------------------------------------------------

||| For a predicate of period `m`, the count over `q` full periods is exactly
||| `q` times the count over a single period.  Hence a period-`m` set has a
||| well-defined density equal to `(count p m) / m`.
public export
periodicCount :
  (p : Nat -> Bool) -> (m : Nat) ->
  ((n : Nat) -> p (plus n m) = p n) ->
  (q : Nat) ->
  count p (mult q m) = mult q (count p m)
periodicCount p m period Z = Refl
periodicCount p m period (S q') =
  rewrite countPlus p m (mult q' m) in
  rewrite countExt (\i => p (plus m i)) p
            (\i => trans (cong p (plusCommutative m i)) (period i))
            (mult q' m) in
  cong (plus (count p m)) (periodicCount p m period q')

--------------------------------------------------------------------------------
-- General single-residue density.
--------------------------------------------------------------------------------

||| A period-`m` predicate with exactly one member per period has natural
||| density `1/m`: over `q` full periods it has exactly `q` members.  This is the
||| general "a single residue class mod `m` has density `1/m`" fact, and it
||| subsumes every concrete residue-class density computation in the development
||| (e.g. `res1mod4` density `1/4`, `res1mod8` density `1/8`): each is just this
||| lemma applied to the class's period and its one-hit-per-period certificate.
public export
singleHitDensity :
  (p : Nat -> Bool) -> (m : Nat) ->
  ((n : Nat) -> p (plus n m) = p n) ->
  count p m = 1 ->
  (q : Nat) -> count p (mult q m) = q
singleHitDensity p m period hcount q =
  trans (periodicCount p m period q)
        (trans (cong (mult q) hcount) (multOneRightNeutral q))

--------------------------------------------------------------------------------
-- Concrete sanity check: parity has period two, one "hit" per period.
--------------------------------------------------------------------------------

||| The "is odd index" predicate.
public export
isOddIndex : Nat -> Bool
isOddIndex Z = False
isOddIndex (S Z) = True
isOddIndex (S (S k)) = isOddIndex k

public export
isOddIndexPeriodic : (n : Nat) -> isOddIndex (plus n 2) = isOddIndex n
isOddIndexPeriodic Z = Refl
isOddIndexPeriodic (S Z) = Refl
isOddIndexPeriodic (S (S k)) = isOddIndexPeriodic k

||| Over `q` periods of length 2 there are exactly `q` "odd index" hits: the
||| general `periodicCount` specialised to the period-2 parity predicate.
public export
countOddIndices :
  (q : Nat) -> count (\i => isOddIndex i) (mult q 2) = mult q (count (\i => isOddIndex i) 2)
countOddIndices q =
  periodicCount (\i => isOddIndex i) 2 (\n => isOddIndexPeriodic n) q
