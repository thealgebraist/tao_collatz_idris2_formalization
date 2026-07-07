module TaoCollatz.ValuationDriftSplit

-- A genuine, *provable* split of the analytic core `stepA7` / `DriftPastTy` of
-- `TaoCollatz.Pieces64` (the 2-adic valuation drift in density form) into named
-- pieces.  Everything in this module is fully total and proved; the split
-- reduces the single monolithic hole `DriftPastTy` to one precisely-stated
-- honest core -- `DensityDriftEventually`: *for every sufficiently large time
-- `n`, the `8/5` drift holds on a density-one set of odd starts*.
--
-- All the surrounding plumbing is proved here, abstractly over the
-- valuation-sum function `s : Nat -> OddPos -> Nat`:
--
--   * `driftDensityCoreFromEventually` -- choose a single late time `n >= m`;
--   * `driftPastFromDensityCore`       -- package the density-one set into the
--                                         `DriftPast` witness shape (using the
--                                         boolean/prop bridge `leqBTrue`);
--   * `driftPastFromEventually`        -- the full reduction
--                                         `DensityDriftEventually => DriftPast`.
--
-- Instantiating `s = syrValSum` (in `TaoCollatz.Pieces64`) makes
-- `driftPastFromEventually` have exactly the type `DriftPastTy = StepA7Ty`, so
-- the whole of `stepA7` is now reduced to the single honest core
-- `DensityDriftEventually syrValSum`.  That core is the genuine Tao
-- large-deviation / concentration content (documented in `MATRIX_DRIFT.md`);
-- its proved mean-drift and variance backbone lives in
-- `TaoCollatz.ValuationDriftMatrix` / `TaoCollatz.ValuationVarianceMatrix`.
--
-- `%default total`; no `believe_me`/`postulate`/`assert_*`/`%foreign`/
-- `idris_crash`/axioms.

import TaoCollatz.Core
import TaoCollatz.Dynamics
import TaoCollatz.Density
import TaoCollatz.CarrierDensity
import TaoCollatz.OddToPosTransfer
import Data.Nat

%default total

--------------------------------------------------------------------------------
-- The fixed-time boolean drift predicate.
--------------------------------------------------------------------------------

||| `driftPredB s n y = True` iff the `8/5` drift target `8 * n <= 5 * s n y`
||| holds for the valuation sum `s` at time `n` and odd start `y`.  (`leqB` is
||| the structural boolean `<=` of `TaoCollatz.OddToPosTransfer`, whose truth
||| reflects into `Leq` via `leqBTrue`.)
public export
driftPredB : (Nat -> OddPos -> Nat) -> Nat -> OddPos -> Bool
driftPredB s n y = leqB (mult 8 n) (mult 5 (s n y))

--------------------------------------------------------------------------------
-- Piece 1 (honest core): eventual density-one drift.
--------------------------------------------------------------------------------

||| **The single remaining analytic core of `stepA7`.**  There is a threshold
||| `n0` past which, at *every* time `n >= n0`, the `8/5` drift
||| `8 * n <= 5 * s n y` holds on a density-one set of odd starts `y`.
|||
||| This is the concentration / large-deviation heart of Tao's argument.  Its
||| proved mean-drift backbone (`8 n E[mass] <= 5 E[weightedSum]`) is
||| `ValuationDriftMatrix.sumDriftGeoValuation`, and the linear-variance engine
||| behind the concentration is `ValuationVarianceMatrix`.
public export
DensityDriftEventually : (Nat -> OddPos -> Nat) -> Type
DensityDriftEventually s =
  (n0 : Nat **
    ((n : Nat) -> Leq n0 n ->
       AlmostAllOddD (\y => driftPredB s n y)))

--------------------------------------------------------------------------------
-- Piece 2 (proved): choose a single late time `n >= max(m, n0)`.
--------------------------------------------------------------------------------

||| From eventual density-one drift, for each fixed `m` there is a single time
||| `n >= m` at which the drift predicate is density one.  Take `n = n0 + m`,
||| which dominates both `m` (`leqPlusExtraLeft`) and `n0`
||| (`leqPlusExtraRight`).
public export
driftDensityCoreFromEventually :
  (s : Nat -> OddPos -> Nat) ->
  DensityDriftEventually s ->
  (m : Nat) ->
  (n : Nat ** (Leq m n, AlmostAllOddD (\y => driftPredB s n y)))
driftDensityCoreFromEventually s (n0 ** h) m =
  (plus n0 m **
    (leqPlusExtraLeft n0 m, h (plus n0 m) (leqPlusExtraRight n0 m)))

--------------------------------------------------------------------------------
-- Piece 3 (proved): package the fixed-time density set into the DriftPast shape.
--------------------------------------------------------------------------------

||| A fixed-time density-one drift set *is* a `DriftPast` witness at `m`: use the
||| same density-one predicate as `good`, and for each good `y` return the common
||| time `n` together with `Leq m n` and the reflected `Leq` drift bound
||| (`leqBTrue`).
public export
driftPastFromDensityCore :
  (s : Nat -> OddPos -> Nat) ->
  ((m : Nat) ->
     (n : Nat ** (Leq m n, AlmostAllOddD (\y => driftPredB s n y)))) ->
  (m : Nat) ->
  (good : OddPos -> Bool **
    (AlmostAllOddD good,
     (y : OddPos) -> good y = True ->
       (n : Nat ** (Leq m n, Leq (mult 8 n) (mult 5 (s n y))))))
driftPastFromDensityCore s core m =
  let (n ** (mLen, aa)) = core m in
  (\y => driftPredB s n y **
    ( aa
    , \y, gy => (n ** (mLen, leqBTrue (mult 8 n) (mult 5 (s n y)) gy))
    ))

--------------------------------------------------------------------------------
-- Piece 4 (proved): the full reduction, DensityDriftEventually => DriftPast.
--------------------------------------------------------------------------------

||| **The complete provable reduction.**  Eventual density-one drift yields the
||| `DriftPast` conclusion for every fixed time `m`.  This is exactly the shape
||| of `Pieces64.DriftPastTy` (instantiated at `s = syrValSum`), so filling the
||| single honest core `DensityDriftEventually syrValSum` closes `stepA7`.
public export
driftPastFromEventually :
  (s : Nat -> OddPos -> Nat) ->
  DensityDriftEventually s ->
  (m : Nat) ->
  (good : OddPos -> Bool **
    (AlmostAllOddD good,
     (y : OddPos) -> good y = True ->
       (n : Nat ** (Leq m n, Leq (mult 8 n) (mult 5 (s n y))))))
driftPastFromEventually s ev =
  driftPastFromDensityCore s (driftDensityCoreFromEventually s ev)
