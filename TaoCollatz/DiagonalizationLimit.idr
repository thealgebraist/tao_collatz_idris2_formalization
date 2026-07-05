module TaoCollatz.DiagonalizationLimit

-- Why the step-4 uniformity (`Pieces64.piece35_driftUniformFromFixed`) is
-- genuinely analytic and cannot be discharged formally.
--
-- `piece35` upgrades a *family* of fixed-bound, density-one "late drift" sets
-- (for each bound `m`, a density-one set of odd `y` admitting a drift time
-- `n >= m`) into a *single* density-one set that admits a drift time past a
-- growing height `f y` (with `f -> infinity`).  It is an honest hole: its
-- statement is a specific claim about the Syracuse valuation sums `S_n(y)`.
--
-- This module proves that the *shape* of `piece35` is not valid at the level of
-- an arbitrary boolean predicate `P : OddPos -> Nat -> Bool` in place of the
-- concrete drift predicate.  Concretely we exhibit `P` and `f` for which every
-- fixed-bound set is density one, yet no density-one set can witness a "late"
-- index past `f`.  Hence any proof of `piece35` must use genuine arithmetic of
-- the Syracuse map (the equidistribution/large-deviation content of Tao's
-- paper), not the formal density algebra alone -- exactly mirroring the earlier
-- `piece58` correction, which found a hole whose *fixed-height* form was itself
-- impossible.  Here the concrete `piece35` remains a true (open, hard) target;
-- it is only its abstract schema that provably fails.
--
-- Everything is fully total and uses no `believe_me`/`postulate`/`assert_*`/
-- `%foreign`/`idris_crash`/axioms.

import TaoCollatz.Core
import TaoCollatz.Dynamics
import TaoCollatz.Large
import TaoCollatz.Density
import TaoCollatz.CarrierDensity
import TaoCollatz.DensityProperties
import Data.Nat

%default total

--------------------------------------------------------------------------------
-- A structural boolean strict order on `Nat` and its bridges to `Leq`.
--------------------------------------------------------------------------------

||| `lessThanB n a = True` iff `n < a`, defined structurally so its truth value
||| can be produced and consumed by pattern matching (unlike the `Ord`-based
||| boolean `>=`, whose reduction goes through `compare`).
public export
lessThanB : Nat -> Nat -> Bool
lessThanB Z (S _) = True
lessThanB _ Z = False
lessThanB (S a) (S b) = lessThanB a b

||| `lessThanB n a = True` reflects into `Leq (S n) a`.
public export
lessThanBToLeq : (n : Nat) -> (a : Nat) -> lessThanB n a = True -> Leq (S n) a
lessThanBToLeq Z (S b) _ = LeqS LeqZ
lessThanBToLeq (S n) (S b) prf = LeqS (lessThanBToLeq n b prf)
lessThanBToLeq Z Z prf = absurd prf
lessThanBToLeq (S n) Z prf = absurd prf

||| `Leq (S n) a` reflects back into `lessThanB n a = True`.
public export
leqToLessThanB : (n : Nat) -> (a : Nat) -> Leq (S n) a -> lessThanB n a = True
leqToLessThanB Z (S b) _ = Refl
leqToLessThanB (S n) (S b) (LeqS h) = leqToLessThanB n b h

||| `Leq (S k) k` is impossible.
public export
succNotLeqSelf : (k : Nat) -> Leq (S k) k -> Void
succNotLeqSelf (S k) (LeqS h) = succNotLeqSelf k h

--------------------------------------------------------------------------------
-- The abstract "uniform late-witness" schema underlying `piece35`.
--------------------------------------------------------------------------------

||| The exact shape of `Pieces64.piece35_driftUniformFromFixed`, but abstracted
||| over the concrete drift predicate: from a family of density-one sets each
||| admitting a witness index `n >= m`, produce a single density-one set
||| admitting a witness index `n >= f y` for a growing height `f`.
public export
UniformLateWitness : (OddPos -> Nat -> Bool) -> Type
UniformLateWitness p =
  ((m : Nat) ->
    (good : OddPos -> Bool **
      (AlmostAllOddD good,
       (y : OddPos) -> good y = True ->
         (n : Nat ** (Leq m n, p y n = True))))) ->
  (f : OddPos -> Nat) -> TendsToInfinityOdd f ->
  (good : OddPos -> Bool **
    (AlmostAllOddD good,
     (y : OddPos) -> good y = True ->
       (n : Nat ** (Leq (f y) n, p y n = True))))

--------------------------------------------------------------------------------
-- The counterexample predicate: `pDiag y n` holds exactly when `n < oddSize y`.
--------------------------------------------------------------------------------

||| `pDiag y n = True` iff `n < oddSize y`.  Its witness indices are *bounded
||| above* by `oddSize y`, so a "late" index past `f y = oddSize y` can never
||| exist -- yet every fixed bound is met on a cofinite (density-one) set.
public export
pDiag : OddPos -> Nat -> Bool
pDiag y n = lessThanB n (oddSize y)

||| For every fixed bound `m`, the set of odd `y` admitting a witness index
||| `n >= m` for `pDiag` is density one (it is the cofinite set `oddSize y > m`,
||| with `n = m` the witness).
public export
pDiagFixedFamily :
  (m : Nat) ->
  (good : OddPos -> Bool **
    (AlmostAllOddD good,
     (y : OddPos) -> good y = True ->
       (n : Nat ** (Leq m n, pDiag y n = True))))
pDiagFixedFamily m =
  (\y => lessThanB m (oddSize y) **
    ( almostAllOddCofinite (\y => lessThanB m (oddSize y)) (S m)
        (\n, h => leqToLessThanB m n h)
    , \y, gy => (m ** (leqRefl m, gy))
    ))

--------------------------------------------------------------------------------
-- The impossibility of the abstract schema for `pDiag`.
--------------------------------------------------------------------------------

||| **Main result.** The abstract uniform late-witness schema fails for `pDiag`
||| (taking the growing height `f = oddSize`): although every fixed bound is met
||| on a density-one set (`pDiagFixedFamily`), no density-one set can admit a
||| witness index `n >= oddSize y`, because `pDiag y n` forces `n < oddSize y`.
|||
||| Consequently `piece35`'s conclusion does not follow from its hypothesis by
||| the density algebra alone: any genuine proof must use the specific arithmetic
||| of the Syracuse valuation sums.
public export
noUniformLateWitnessForPDiag :
  UniformLateWitness TaoCollatz.DiagonalizationLimit.pDiag -> Void
noUniformLateWitnessForPDiag uni =
  let (good ** (aa, prop)) = uni pDiagFixedFamily oddSize oddSizeTendsToInfinity
      (n0 ** memTrue) = almostAllExistsMember aa
      (k ** (leFk, pTrue)) = prop (MkOddPos n0) memTrue
      -- `leFk  : Leq (oddSize (MkOddPos n0)) k`, i.e. `Leq n0 k`.
      -- `pTrue : pDiag (MkOddPos n0) k = True`, i.e. `k < oddSize (MkOddPos n0)`.
      leSk : Leq (S k) (oddSize (MkOddPos n0))
      leSk = lessThanBToLeq k (oddSize (MkOddPos n0)) pTrue
  in succNotLeqSelf k (leqTrans leSk leFk)
