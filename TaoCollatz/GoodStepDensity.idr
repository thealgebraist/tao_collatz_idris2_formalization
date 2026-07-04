module TaoCollatz.GoodStepDensity

-- Genuine, fully-proved density of the "good step" residue class.
--
-- By `GoodStep`, whenever `4 | (3n+1)` one Syracuse step descends.  For `n`
-- this is the residue condition `n ≡ 1 (mod 4)` (indeed `3(4t+1)+1 = 4(3t+1)`).
-- This module proves two genuine facts:
--
--   * the good-step residue set `{ n : n ≡ 1 (mod 4) }` has natural density
--     exactly `1/4`: `count over q periods = q` (via `PeriodicCount`);
--   * the explicit infinite family `n = 4t+1` consists of good-step starts:
--     each has `Syr(n) <= n`, a genuine first-passage witness.
--
-- So there is a genuine density-`1/4` set of odd starting points on which one
-- Syracuse step provably descends.  (Upgrading `1/4` to density one is exactly
-- the deep analytic content the gate `SyracuseDensityControl` still abstracts.)
--
-- Everything here is real mathematics: `%default total`, no placeholders, no
-- `believe_me`, no axioms, no holes.

import TaoCollatz.Core
import TaoCollatz.Dynamics
import TaoCollatz.TwoAdic
import TaoCollatz.SyracuseStructure
import TaoCollatz.SyracuseDescent
import TaoCollatz.GoodStep
import TaoCollatz.ValuationExact
import TaoCollatz.Density
import TaoCollatz.PeriodicCount
import Data.Nat

%default total

--------------------------------------------------------------------------------
-- The residue predicate `n ≡ 1 (mod 4)`, made period-4 by construction.
--------------------------------------------------------------------------------

public export
res1mod4 : Nat -> Bool
res1mod4 Z = False
res1mod4 (S Z) = True
res1mod4 (S (S Z)) = False
res1mod4 (S (S (S Z))) = False
res1mod4 (S (S (S (S k)))) = res1mod4 k

public export
res1mod4Periodic : (n : Nat) -> res1mod4 (plus n 4) = res1mod4 n
res1mod4Periodic Z = Refl
res1mod4Periodic (S Z) = Refl
res1mod4Periodic (S (S Z)) = Refl
res1mod4Periodic (S (S (S Z))) = Refl
res1mod4Periodic (S (S (S (S k)))) = res1mod4Periodic k

--------------------------------------------------------------------------------
-- Density 1/4 of the good-step residue class.
--------------------------------------------------------------------------------

||| Exactly one good-step residue per period of four.
public export
countRes1PerPeriod : count (\i => res1mod4 i) 4 = 1
countRes1PerPeriod = Refl

||| The good-step residue class has density exactly `1/4`: over `q` full periods
||| there are exactly `q` members.
public export
countGoodResidues :
  (q : Nat) -> count (\i => res1mod4 i) (mult q 4) = q
countGoodResidues q =
  singleHitDensity (\i => res1mod4 i) 4 (\n => res1mod4Periodic n)
    countRes1PerPeriod q

--------------------------------------------------------------------------------
-- The explicit good-step family `n = 4t + 1`.
--------------------------------------------------------------------------------

||| `3(4t+1)+1 = 12t + 4`.
public export
familyLHS :
  (t : Nat) -> plus (mult 3 (plus (mult 4 t) 1)) 1 = plus (mult 12 t) 4
familyLHS t =
  rewrite multDistributesOverPlusRight 3 (mult 4 t) 1 in
  rewrite multAssociative 3 4 t in
  sym (plusAssociative (mult 12 t) 3 1)

||| `4(3t+1) = 12t + 4`.
public export
familyRHS :
  (t : Nat) -> mult 4 (plus (mult 3 t) 1) = plus (mult 12 t) 4
familyRHS t =
  rewrite multDistributesOverPlusRight 4 (mult 3 t) 1 in
  rewrite multAssociative 4 3 t in
  Refl

||| Arithmetic identity: `3(4t+1)+1 = 4(3t+1)`.
public export
familyDivFour :
  (t : Nat) ->
  plus (mult 3 (plus (mult 4 t) 1)) 1 = mult 4 (plus (mult 3 t) 1)
familyDivFour t = trans (familyLHS t) (sym (familyRHS t))

||| Every `n = 4t+1` is a good-step start: one Syracuse step descends.  Now an
||| instance of the general power-of-two descent criterion: from
||| `3(4t+1)+1 = 2^2 * (3t+1)` the general `descendsFromFactorPow2` gives descent
||| directly (no bespoke parity/half computation needed).
public export
familyDescends :
  (t : Nat) ->
  Leq (oddValue (Syr (MkOddPos (plus (mult 4 t) 1)))) (plus (mult 4 t) 1)
familyDescends t =
  descendsFromFactorPow2 (plus (mult 4 t) 1) 2 (plus (mult 3 t) 1)
    (oneLeqPlusOne (mult 4 t)) (oneLeqPlusOne (mult 3 t))
    (LeqS (LeqS LeqZ)) (familyDivFour t)

||| First-passage form: each `n = 4t+1` reaches a value `<= n` in one step.
public export
familyBelow :
  (t : Nat) -> SyrBelow (MkOddPos (plus (mult 4 t) 1)) (plus (mult 4 t) 1)
familyBelow t = Reaches 1 (familyDescends t)
