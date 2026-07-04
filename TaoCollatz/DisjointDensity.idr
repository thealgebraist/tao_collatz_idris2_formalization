module TaoCollatz.DisjointDensity

-- Genuine, fully-proved *additivity* of counting over disjoint predicates.
--
-- `Density.countOrLe` gives the sub-additive bound `count (p||q) <= count p +
-- count q`.  When `p` and `q` are *disjoint* (no index satisfies both) this is
-- an exact equality:
--
--     count (\n => p n || q n) N = count p N + count q N .
--
-- This is the additivity of natural density on disjoint sets, the counting fact
-- behind decomposing a residue class into finer disjoint residue classes
-- (item C1 of `REMAINING_WORK.md`).  Combined with `PeriodicCount.periodicCount`
-- it makes the densities of disjoint periodic families add exactly.
--
-- Everything here is real mathematics: `%default total`, no placeholders, no
-- `believe_me`, no axioms, no holes.

import TaoCollatz.Core
import TaoCollatz.Density
import Data.Nat

%default total

--------------------------------------------------------------------------------
-- Additivity of the indicator on disjoint booleans.
--------------------------------------------------------------------------------

||| If `b1` and `b2` are never both true, the indicator of their disjunction is
||| the sum of their indicators.
public export
indicatorOrDisjoint :
  (b1 : Bool) -> (b2 : Bool) ->
  (b1 = True -> b2 = False) ->
  indicator (b1 || b2) = plus (indicator b1) (indicator b2)
indicatorOrDisjoint False b2 _ = Refl
indicatorOrDisjoint True b2 disj = rewrite disj Refl in Refl

--------------------------------------------------------------------------------
-- Additivity of `count` over disjoint predicates.
--------------------------------------------------------------------------------

||| Exact additivity of counting for disjoint predicates.
public export
countDisjoint :
  (p : Nat -> Bool) -> (q : Nat -> Bool) ->
  ((n : Nat) -> p n = True -> q n = False) ->
  (bigN : Nat) ->
  count (\n => p n || q n) bigN = plus (count p bigN) (count q bigN)
countDisjoint p q disj Z = Refl
countDisjoint p q disj (S k) =
  rewrite indicatorOrDisjoint (p k) (q k) (disj k) in
  rewrite countDisjoint p q disj k in
  plusRearrange (indicator (p k)) (indicator (q k)) (count p k) (count q k)

--------------------------------------------------------------------------------
-- Concrete sanity check: parity of the index splits every range exactly.
--------------------------------------------------------------------------------

||| "even index" and "odd index" are disjoint and their counts add to the total.
public export
evenIndex : Nat -> Bool
evenIndex Z = True
evenIndex (S Z) = False
evenIndex (S (S k)) = evenIndex k

public export
oddIndex : Nat -> Bool
oddIndex n = not (evenIndex n)

public export
evenOddDisjoint : (n : Nat) -> evenIndex n = True -> oddIndex n = False
evenOddDisjoint n h = rewrite h in Refl

||| The disjoint even/odd split of `count` over any range.
public export
countEvenOddSplit :
  (bigN : Nat) ->
  count (\n => evenIndex n || oddIndex n) bigN
    = plus (count (\n => evenIndex n) bigN) (count (\n => oddIndex n) bigN)
countEvenOddSplit bigN =
  countDisjoint (\n => evenIndex n) (\n => oddIndex n) evenOddDisjoint bigN
