# Status of the four analytic cores in `TaoCollatz/Pieces64.idr`

This pass filled every mechanical / bookkeeping hole in `Pieces64.idr` with an
honest proof and isolated the genuine remaining content into **four** explicit
holes, all of the form `stepX7 = ?holeX7`.

## What was filled (28 former holes)

* **Combiners** `stepA8`, `stepB8`, `stepC8`, `stepD8`: each has type
  `... -> StepX7Ty -> Milestone` where `StepX7Ty = Milestone`, so the honest
  combiner is the projection `\_,_,_,_,_,_,core => core`.
* **Supporting facts** `stepA1..A6`, `stepB1..B6`, `stepC1..C6`, `stepD1..D6`:
  each is discharged by the already-proved sub-piece / `pieceNN` of the same
  statement (partial-sum additivity/monotonicity, density algebra —
  intersection, cofinite thresholds, pointwise-implication monotonicity —,
  `iter` unfolding, `SyrBelow` monotonicity and renewal lifting, etc.).

Two supporting **types** were corrected because they were *false* as written
(the record `OddPos` carries **no** oddness/positivity proof, so `MkOddPos 0`
is a legal value):

* `StepA1Ty` now assumes `isEven (oddValue y) = False` (needed: `syrValuation 0 = 0`).
* `StepA3Ty` now uses `syrValSum (S n) y` (the `syrValSum n y` form fails at
  `MkOddPos 0`, since `syrValSum 1 (MkOddPos 0) = 0`).

Both corrected lemmas are now proved. They are consumed only by the projection
combiners, so the change does not affect anything downstream.

The whole package rebuilds cleanly (`idris2 --build taocollatz.ipkg`, 68/68
modules, no errors); the only remaining holes are the four cores below.

## The four remaining cores (genuine analytic content)

| Hole    | Type (milestone)     | Meaning | On `theorem13` path? |
|---------|----------------------|---------|----------------------|
| `stepA7`| `DriftPastTy`        | For each fixed `m`, a density-one set of odd starts reaches the `8/5` drift rate `8n ≤ 5·S_n(y)` at some time `n ≥ m`. This is the 2-adic **valuation law-of-large-numbers / concentration** estimate (mean valuation `2 > 8/5`). | **Yes** (via `piece34`). |
| `stepB7`| `DriftUniformTy`     | Upgrade the fixed-time drift family to a **single** density-one set that drifts past a *growing* height `f → ∞` (the diagonalisation/uniformity step). | **Yes** (via `piece35`). |
| `stepC7`| `DescentPosTy`       | On the typical-descent set the descent time can be taken **strictly positive**. | **No** — `piece50` is defined but unused; the main chain uses `piece49`. |
| `stepD7`| `DiagonalHeightTy`   | From typical descent, diagonalise over `f → ∞` to get a density-one set whose Syracuse orbit falls **below `f y`** (renewal / first passage). | **Yes** (via `piece59`). |

So the closed term `theorem13` (`TaoCollatz/HoleProof.idr`) is complete **modulo
exactly** `stepA7`, `stepB7`, `stepD7`.

## Honest assessment of the remaining gap

These four are the irreducible deep content of Tao's density-one first-passage
theorem, not further reducible by bookkeeping:

* `stepA7` requires the genuine valuation-drift concentration estimate.
* `stepB7` is the diagonalisation to a growing height. `DiagonalizationLimit`
  in this project already records that this cannot follow from the density
  algebra alone for an arbitrary predicate; it needs the Syracuse valuation
  arithmetic.
* `stepC7`/`stepD7` are stated with an *abstract* `TypicalDescentDensity`
  hypothesis. Note that `piece49` currently produces `TypicalDescentDensity`
  in its weak `n = 0` reading, so to make the main chain unconditional one must
  also strengthen `piece49` (descent at a genuinely positive time from
  `ContractionDominatesDensity` + the exact affine backbone) — real dynamics,
  not bookkeeping.

No `believe_me` / `postulate` / `assert_*` / `%foreign` / `idris_crash` /
axioms were introduced, and `%default total` is preserved throughout.
