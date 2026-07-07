# A provable split of `stepA7` / `DriftPastTy`

This note records how the single monolithic analytic hole `stepA7` (`?holeA7`)
of `TaoCollatz/Pieces64.idr` is replaced by a **genuine, provable split** into
named pieces, so that all the connective reasoning is proved and the only
remaining hole is a single, precisely-stated analytic core.

## What `stepA7` says

```
StepA7Ty = DriftPastTy =
  (m : Nat) ->
  (good : OddPos -> Bool **
    (AlmostAllOddD good,
     (y : OddPos) -> good y = True ->
       (n : Nat ** (Leq m n, Leq (mult 8 n) (mult 5 (syrValSum n y))))))
```

For each fixed `m`: a density-one set of odd starts reaches the `8/5` drift rate
`8 n <= 5 * S_n(y)` at some time `n >= m`.

## The split (module `TaoCollatz.ValuationDriftSplit`)

The reduction is stated abstractly over the valuation-sum function
`s : Nat -> OddPos -> Nat` and then instantiated at `s = syrValSum`.  Writing the
boolean drift predicate `driftPredB s n y = leqB (8 n) (5 * s n y)`:

1. **`DensityDriftEventually s`  (the one honest core, a hole).**
   ```
   (n0 : Nat ** ((n : Nat) -> Leq n0 n -> AlmostAllOddD (\y => driftPredB s n y)))
   ```
   *Past some threshold `n0`, at every time `n >= n0` the `8/5` drift holds on a
   density-one set.*  This is the concentration / large-deviation heart of Tao's
   argument.

2. **`driftDensityCoreFromEventually`  (proved).**  Choose one late time
   `n = n0 + m`, which is `>= m` (`leqPlusExtraLeft`) and `>= n0`
   (`leqPlusExtraRight`); hand back the density-one set at that `n`.

3. **`driftPastFromDensityCore`  (proved).**  The fixed-time density-one set *is*
   a `DriftPast` witness at `m`: reuse it as `good`, and for each good `y` return
   the common time `n`, `Leq m n`, and the reflected drift bound via the
   boolean/prop bridge `leqBTrue`.

4. **`driftPastFromEventually`  (proved).**  Composition of (2) and (3): the full
   reduction `DensityDriftEventually s => DriftPast` shape.

## Wiring (in `TaoCollatz/Pieces64.idr`)

```
driftDensityEventually : DensityDriftEventually syrValSum
driftDensityEventually = ?holeA7core          -- the single remaining core

stepA7 : StepA7Ty
stepA7 = driftPastFromEventually syrValSum driftDensityEventually
```

`driftPastFromEventually syrValSum _` has type exactly `DriftPastTy`, so this
type-checks and reduces the old whole-statement hole `?holeA7` to the single
sharper hole `?holeA7core`.  Everything else in the chain (the `leqB`/`Leq`
bridge, the late-time choice `n >= m`, and the witness packaging) is proved and
total.

## Why the core stays a hole

`AlmostAllOddD` is genuine natural density.  The eventual-drift core is Tao's
concentration statement about the Syracuse valuation sums; it cannot be produced
from the density algebra alone (`TaoCollatz.DiagonalizationLimit` records why).
Its proved backbone is the transfer-matrix layer: the mean drift
`8 n * E[mass] <= 5 * E[weightedSum]` (`ValuationDriftMatrix.sumDriftGeoValuation`)
and the linear-variance engine (`ValuationVarianceMatrix`).  Turning that
expectation-plus-variance into a density-one statement is the Chebyshev
normalisation (needs a rational/real measure layer, not `Nat`) together with the
coupling of the true orbit valuations to the independent model — the two honest
gaps documented in `MATRIX_DRIFT.md`.

## Verification note

This project is Idris2; no Idris2 toolchain is available in the current
environment, so the new module was checked by hand against the already-compiling
patterns it mirrors (`DiagonalizationLimit.pDiagFixedFamily` for the dependent
pair / density-one witness shape, and `OddToPosTransfer.leqBTrue` for the
boolean/prop bridge).  No `believe_me`/`postulate`/`assert_*`/`%foreign`/
`idris_crash`/axioms are introduced; `%default total` is kept.
