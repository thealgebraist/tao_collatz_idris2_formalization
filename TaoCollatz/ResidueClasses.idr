module TaoCollatz.ResidueClasses

-- Genuine, fully-proved decomposition of the good-step class mod 8.
--
-- The good-step residue class `n ≡ 1 (mod 4)` (`GoodStepDensity.res1mod4`,
-- density `1/4`) splits mod 8 into two disjoint sub-classes:
--
--     n ≡ 1 (mod 8)   -- valuation exactly 2 (cf. ValuationTwoClass)
--     n ≡ 5 (mod 8)   -- valuation >= 3 (the tail)
--
-- This module defines these two period-8 predicates, proves their periodicity,
-- their disjointness, and that their (pointwise) union is exactly `res1mod4`.
-- Combined with `DisjointDensity.countDisjoint` and `PeriodicCount` this proves
-- the exact density identity
--
--     density(1 mod 4) = density(1 mod 8) + density(5 mod 8),  i.e.  1/4 = 1/8 + 1/8,
--
-- the first genuine step of the geometric Syracuse-valuation distribution
-- (item C1/C2 of `REMAINING_WORK.md`).
--
-- Everything here is real mathematics: `%default total`, no placeholders, no
-- `believe_me`, no axioms, no holes.

import TaoCollatz.Core
import TaoCollatz.Density
import TaoCollatz.PeriodicCount
import TaoCollatz.DisjointDensity
import TaoCollatz.GoodStepDensity
import Data.Nat

%default total

--------------------------------------------------------------------------------
-- The two period-8 residue predicates.
--------------------------------------------------------------------------------

||| `n ≡ 1 (mod 8)`.
public export
res1mod8 : Nat -> Bool
res1mod8 (S Z) = True
res1mod8 (S (S (S (S (S (S (S (S k)))))))) = res1mod8 k
res1mod8 _ = False

||| `n ≡ 5 (mod 8)`.
public export
res5mod8 : Nat -> Bool
res5mod8 (S (S (S (S (S Z))))) = True
res5mod8 (S (S (S (S (S (S (S (S k)))))))) = res5mod8 k
res5mod8 _ = False

--------------------------------------------------------------------------------
-- Periodicity (period 8).
--------------------------------------------------------------------------------

public export
res1mod8Periodic : (n : Nat) -> res1mod8 (plus n 8) = res1mod8 n
res1mod8Periodic Z = Refl
res1mod8Periodic (S Z) = Refl
res1mod8Periodic (S (S Z)) = Refl
res1mod8Periodic (S (S (S Z))) = Refl
res1mod8Periodic (S (S (S (S Z)))) = Refl
res1mod8Periodic (S (S (S (S (S Z))))) = Refl
res1mod8Periodic (S (S (S (S (S (S Z)))))) = Refl
res1mod8Periodic (S (S (S (S (S (S (S Z))))))) = Refl
res1mod8Periodic (S (S (S (S (S (S (S (S k)))))))) = res1mod8Periodic k

public export
res5mod8Periodic : (n : Nat) -> res5mod8 (plus n 8) = res5mod8 n
res5mod8Periodic Z = Refl
res5mod8Periodic (S Z) = Refl
res5mod8Periodic (S (S Z)) = Refl
res5mod8Periodic (S (S (S Z))) = Refl
res5mod8Periodic (S (S (S (S Z)))) = Refl
res5mod8Periodic (S (S (S (S (S Z))))) = Refl
res5mod8Periodic (S (S (S (S (S (S Z)))))) = Refl
res5mod8Periodic (S (S (S (S (S (S (S Z))))))) = Refl
res5mod8Periodic (S (S (S (S (S (S (S (S k)))))))) = res5mod8Periodic k

--------------------------------------------------------------------------------
-- Disjointness and union = `res1mod4`.
--------------------------------------------------------------------------------

public export
res1res5Disjoint : (n : Nat) -> res1mod8 n = True -> res5mod8 n = False
res1res5Disjoint Z h = absurd h
res1res5Disjoint (S Z) _ = Refl
res1res5Disjoint (S (S Z)) h = absurd h
res1res5Disjoint (S (S (S Z))) h = absurd h
res1res5Disjoint (S (S (S (S Z)))) h = absurd h
res1res5Disjoint (S (S (S (S (S Z))))) h = absurd h
res1res5Disjoint (S (S (S (S (S (S Z)))))) h = absurd h
res1res5Disjoint (S (S (S (S (S (S (S Z))))))) h = absurd h
res1res5Disjoint (S (S (S (S (S (S (S (S k)))))))) h = res1res5Disjoint k h

||| Pointwise: `n ≡ 1 (mod 8)` or `n ≡ 5 (mod 8)` iff `n ≡ 1 (mod 4)`.
public export
res8UnionIsRes1mod4 :
  (n : Nat) -> (res1mod8 n || res5mod8 n) = res1mod4 n
res8UnionIsRes1mod4 Z = Refl
res8UnionIsRes1mod4 (S Z) = Refl
res8UnionIsRes1mod4 (S (S Z)) = Refl
res8UnionIsRes1mod4 (S (S (S Z))) = Refl
res8UnionIsRes1mod4 (S (S (S (S Z)))) = Refl
res8UnionIsRes1mod4 (S (S (S (S (S Z))))) = Refl
res8UnionIsRes1mod4 (S (S (S (S (S (S Z)))))) = Refl
res8UnionIsRes1mod4 (S (S (S (S (S (S (S Z))))))) = Refl
res8UnionIsRes1mod4 (S (S (S (S (S (S (S (S k)))))))) = res8UnionIsRes1mod4 k

--------------------------------------------------------------------------------
-- Per-period counts (density 1/8 each).
--------------------------------------------------------------------------------

public export
countRes1mod8PerPeriod : count (\i => res1mod8 i) 8 = 1
countRes1mod8PerPeriod = Refl

public export
countRes5mod8PerPeriod : count (\i => res5mod8 i) 8 = 1
countRes5mod8PerPeriod = Refl

||| `n ≡ 1 (mod 8)` has density exactly `1/8`: `q` members over `q` periods.
public export
countRes1mod8 : (q : Nat) -> count (\i => res1mod8 i) (mult q 8) = q
countRes1mod8 q =
  singleHitDensity (\i => res1mod8 i) 8 (\n => res1mod8Periodic n)
    countRes1mod8PerPeriod q

||| `n ≡ 5 (mod 8)` has density exactly `1/8`: `q` members over `q` periods.
public export
countRes5mod8 : (q : Nat) -> count (\i => res5mod8 i) (mult q 8) = q
countRes5mod8 q =
  singleHitDensity (\i => res5mod8 i) 8 (\n => res5mod8Periodic n)
    countRes5mod8PerPeriod q

--------------------------------------------------------------------------------
-- The exact density decomposition `1/4 = 1/8 + 1/8`.
--------------------------------------------------------------------------------

||| Over `q` periods of length 8, the good-step class `res1mod4` splits exactly
||| into the two mod-8 sub-classes, with `q + q` members total.
public export
goodStepDensityDecomp :
  (q : Nat) ->
  count (\i => res1mod4 i) (mult q 8)
    = plus (count (\i => res1mod8 i) (mult q 8)) (count (\i => res5mod8 i) (mult q 8))
goodStepDensityDecomp q =
  trans
    (sym (countExt (\i => res1mod8 i || res5mod8 i) (\i => res1mod4 i)
            (\i => res8UnionIsRes1mod4 i) (mult q 8)))
    (countDisjoint (\i => res1mod8 i) (\i => res5mod8 i) res1res5Disjoint (mult q 8))

||| Concretely `count res1mod4 (q*8) = q + q`.
public export
goodStepCountOverEight :
  (q : Nat) -> count (\i => res1mod4 i) (mult q 8) = plus q q
goodStepCountOverEight q =
  trans (goodStepDensityDecomp q)
        (rewrite countRes1mod8 q in rewrite countRes5mod8 q in Refl)
