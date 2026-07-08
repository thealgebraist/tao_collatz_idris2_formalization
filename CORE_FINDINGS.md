# Findings on the four remaining analytic holes

This note records what the four remaining Idris holes in
`TaoCollatz/Pieces64.idr` actually are, a **mathematical error** that was found
and corrected in the previous decomposition, and why the holes that remain are
the genuine analytic heart of Tao's density-form Collatz result.

Everything here was checked against the code that builds with Idris2 0.8.0
(`idris2 --build taocollatz.ipkg`, exit 0). No axioms, `believe_me`,
`postulate`, `assert_*` or `@[implemented_by]`-style escapes were introduced.

## The four holes

After the group split, the central theorem's remaining content sits in four
holes:

| hole | type | meaning |
|------|------|---------|
| `?coreA_driftPast` (`gA15`) | `DriftPastTy` | for each fixed `m`, on a density-one set of odd starts there is *some* time `n >= m` with `8n <= 5·S_n(y)` |
| `?coreB_diagonalization` (`gB15`) | `DriftUniformTy` | upgrade the fixed-time drift family to a single density-one set that drifts past a *growing* height `f -> ∞` |
| `?coreC_positiveDescent` (`gC15`) | `DescentPosTy` | on a density-one set the Syracuse descent time can be taken strictly positive (`n >= 1`) |
| `?coreD_renewal` (`gD15`) | `DiagonalHeightTy` | density-one first passage below a growing height `f -> ∞` (`SyrBelow y (f y)`) |

Here `S_n(y) = syrValSum n y` is the sum of the first `n` Syracuse 2-adic
valuations, and `AlmostAllOddD p` means the complement of `p` has natural
density zero (genuine natural density, `TaoCollatz.Density`).

## Correction: the previous group-A core was FALSE

Before this pass, the group-A core was stated as
`DensityDriftEventually syrValSum`:

> there is a threshold `n0` such that at **every** time `n >= n0` the `8/5`
> drift `8n <= 5·S_n(y)` holds on a density-one set of odd starts.

This statement is **mathematically false**. For any *fixed* `n`, the
drift-failure set

    { y odd : 8n > 5·S_n(y) }   (equivalently  S_n(y)/n < 8/5)

has **positive** natural density — it is the large-deviation probability
`P(S_n/n < 8/5)`, which is strictly positive for every `n` (it only decays
*as* `n -> ∞`). Hence it is never negligible, so
`AlmostAllOddD (driftPredB syrValSum n)` fails for **every** `n`, and no `n0`
can work. `DensityDriftEventually syrValSum` is therefore uninhabited.

Direct computation over odd `y` (counted with `driftPredB`) confirms the
failure density is positive and decays slowly:

| n | failure proportion (odd y up to ~8000) |
|---|------|
| 1 | ~50% |
| 2 | ~50% |
| 3 | ~31% |
| 5 | ~23% |
| 8 | ~19% |
| 10 | ~15% |
| 15 | ~10% |
| 20 | ~8% |

The previous `stepA7 = driftPastFromEventually syrValSum driftDensityEventually`
reduction was logically valid (eventual-drift implies drift-past-`m`), but it
reduced the **true** goal `DriftPastTy` to the strictly stronger **false** goal
`DensityDriftEventually`, making the hole unfillable.

**Fix applied.** `gA15`/`stepA7` now target `DriftPastTy` directly (the true
density-form valuation law of large numbers): for each fixed `m`, on a
density-one set there is *some* `n >= m` with the `8/5` drift. This is true (the
exceptional `y` whose running average valuation never again exceeds `8/5` form a
density-zero set) and is exactly what the downstream reduction needs. The false
`DensityDriftEventually`/`driftDensityEventually` route was removed.

After the fix all four remaining holes are genuine, **true** (inhabited)
propositions; there are no false holes.

## Why the remaining holes are hard

- `coreA` (`DriftPastTy`) is Tao's density-form valuation LLN: for a.e. odd `y`
  the running average 2-adic valuation exceeds `8/5` again past every fixed
  time. Its honest proof is the concentration/equidistribution estimate for the
  Syracuse valuation sequence.
- `coreB` (`DriftUniformTy`) is the diagonalisation to a growing height.
  `TaoCollatz.DiagonalizationLimit.noUniformLateWitnessForPDiag` shows this
  cannot follow from the density algebra alone for an arbitrary family; it needs
  the specific valuation structure (drift at *all* large times), i.e. the same
  concentration content as `coreA`.
- `coreC` (`DescentPosTy`) upgrades "descent at some time" to "descent at a
  positive time". Its stated hypothesis `TypicalDescentDensity` is trivially
  inhabited (descent at `n = 0`), so ruling out the `n = 0` reading genuinely
  needs the contraction dynamics.
- `coreD` (`DiagonalHeightTy`) is the density-one first passage below a growing
  height. Its stated hypothesis `TypicalDescentDensity` is again trivially
  inhabited (`piece49_descentDensityFromContraction` discharges it with
  `n = 0`), so `coreD` carries essentially the *entire* first-passage theorem
  on its own. As the previous notes already recorded, first passage below a
  *fixed* height `b = 1` would be stronger than Tao's theorem and is open; the
  growing-height version is exactly Tao's density-one conclusion.

## Status

- Build: `idris2 --build taocollatz.ipkg` succeeds (exit 0, all 71 modules).
- Remaining holes: `?coreA_driftPast`, `?coreB_diagonalization`,
  `?coreC_positiveDescent`, `?coreD_renewal` (all genuine, non-vacuous, true
  propositions). `?piece58`/`?pieceNN` appear only inside comments.
- These four holes are the genuine analytic content of Tao's density-form
  Collatz result; closing them honestly amounts to formalizing that result and
  is beyond a by-hand Idris development. No shortcuts (axioms, `believe_me`,
  weakening to `Unit`/`True`, vacuous premises) were used, and the previously
  false core was corrected to its true form.

## Re-verification and dependency map (later pass)

A later pass rebuilt the package from scratch with Idris2 0.8.0
(`idris2 --build taocollatz.ipkg`, exit 0, all 71 modules) and independently
re-checked the situation. Findings:

- The four `?`-holes are exactly `?coreA_driftPast`, `?coreB_diagonalization`,
  `?coreC_positiveDescent`, `?coreD_renewal`; every other `?` occurrence is
  inside a comment. No `believe_me`/`postulate`/`assert_*`/`%foreign`/
  `idris_crash`/axiom appears outside comments.

- **Critical-path map.** Tracing `syracuseDensityControl` (the closed statement
  of Theorem 1.3, density form) back through `HoleProof.step4/step6/step7` and
  the `piece62/63/64` capstones shows the main theorem depends on **coreA,
  coreB and coreD only**:
  * `step4` (drift) routes through `piece36 -> piece35 -> piece34`, i.e. through
    `gB15 = coreB` and `gA15 = coreA`;
  * `step6` (typical descent) uses the deliberately weak `piece49`
    (`n = 0` reading of `TypicalDescentDensity`) and does **not** touch coreC;
  * `step7` (first passage) routes through `piece59 -> subD8 -> gD15 = coreD`.
  Hence `?coreC_positiveDescent` (`DescentPosTy`, positive descent time) is an
  auxiliary strengthening milestone that is *off* the critical path; filling it
  would remove a hole but would not change the main theorem's dependencies.

- **Why coreC/coreD are not a shortcut over coreA/coreB.** Positive descent and
  first passage both require the *growing-height* drift (`ContractionDominates
  Density`, produced by `step5`/`piece44` from the uniform drift = coreB), not
  the fixed-time drift alone. Concretely, a candidate `n`-step descent bound
  from the exact affine backbone `2^{S_n} * Syr^n(x) = 3^n x + c` needs the
  affine constant `c` controlled; the naive guess `c < 2^{S_n}` is **false**
  (e.g. `x = 7`, `n = 2`: `S_2 = 2`, `c = 5 > 4 = 2^{S_2}`), which is exactly
  why descent below the start needs `n` large — i.e. the growing-height drift,
  i.e. coreB (hence coreA). So coreC and coreD carry the same concentration
  content as coreA/coreB and are not independently easier.

- **Why coreA is the true barrier.** `ValuationDriftMatrix` /
  `ValuationVarianceMatrix` develop mean/variance (moment) machinery for a
  *model* valuation distribution (`FinDist`), but the density statement in
  `DriftPastTy` is about the *actual* Syracuse valuation sequence and requires
  the equidistribution/concentration input (Tao's Syracuse-random-variable
  equidistribution mod `2^k`) that is not formalized in the project. This is
  the genuine analytic heart and is not derivable from the surrounding proved
  algebra.

No unsound construct was added and no hole was closed in this pass: the four
holes remain genuine, non-vacuous, true propositions constituting the analytic
heart of Tao's theorem.
