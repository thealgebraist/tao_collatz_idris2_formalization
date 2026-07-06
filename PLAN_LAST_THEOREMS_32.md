# A constructive 32-step plan for the last theorems

This document gives a **constructive, buildable, 32-step plan** for discharging
the last remaining analytic content of Tao's Theorem 1.3 in the Idris2
development, i.e. for filling the four honest assembler holes that still gate the
main theorem.

## What "the last theorems" are

The whole tree builds under Idris2 0.8.0 (`idris2 --build taocollatz.ipkg`,
exit 0), is `%default total`, and uses **no** `believe_me` / `postulate` /
`assert_*` / `%foreign` / `idris_crash` / axioms. After the 64-piece
decomposition and its 32-sub-piece refinement (see `PIECES64.md`), the entire
proof rests on exactly **four** genuine, non-vacuous holes in
`TaoCollatz/Pieces64.idr`:

| Hole | Parent | Paper step | Milestone type | Content |
|---|---|---|---|---|
| `?subA8` | `piece34_driftPastMDensity` | step 4 | `DriftPastTy` | large-deviation valuation drift past a fixed time, density form (Prop. 1.9) |
| `?subB8` | `piece35_driftUniformFromFixed` | step 4 | `DriftUniformTy` | uniform diagonalisation of the fixed-time drift to a growing height `f` |
| `?subC8` | `piece50_descentTimePositive` | step 6 | `DescentPosTy` | typical descent at a **strictly positive** time |
| `?subD8` | `piece59_diagonalHeight` | step 7 | `DiagonalHeightTy` | renewal first passage below a growing height `f` |

Every supporting sub-piece (`subA1..A7`, `subB1..B7`, `subC1..C7`, `subD1..D7`)
is already in place with a genuine type; the four assemblers are where the real
analytic mathematics must go. Filling all four — **with no other change** —
upgrades `theorem13`, `theorem13Strict`, `theorem13PaperDomain`,
`theorem13HasMember` to an unconditional proof.

## Two honesty constraints the plan must respect

Both are already machine-recorded in the tree and must not be violated:

1. **No fixed-height first passage.** `piece58` (first passage below *every*
   fixed `b`, including `b = 0, 1`) is uninhabited (it would imply orbits reach
   `1`). Step 7 must diagonalise only against a height `f -> infinity`. See the
   commented-out `piece58` and `piece60_diagonalCoherence`.
2. **No purely-formal diagonalisation.** `TaoCollatz/DiagonalizationLimit.idr`
   proves the *abstract* schema behind `?subB8` (`UniformLateWitness p` for the
   growing height) is **false** for `pDiag y n := (n < oddSize y)`. Hence any
   real proof of `?subB8` must use the concrete arithmetic of the Syracuse
   valuation sums `syrValSum`, not the density algebra alone.

## Global protocol (applies to every step)

- After each step: `idris2 --build taocollatz.ipkg` must exit 0.
- After each step: `grep -RnE 'believe_me|postulate|assert_|%foreign|idris_crash|^ *axiom' TaoCollatz/` must stay empty, and no new `?`-hole may appear except the ones this plan explicitly introduces and then closes.
- New theory goes in **new modules** added to `taocollatz.ipkg`; `Pieces64.idr` is edited only to wire finished results into the assemblers (it is already 1322 lines — keep new content out of it).
- Each step names the existing declarations it reuses so it stays concrete.

Reusable infrastructure already present: `FinMeasure` (`FinDist`, `mass`,
`weightedSum`, `massGe`, `mix`, `scale`, `dirac`), `Convolution` (`convolve`,
`convPow`, `charFn`, `charFnConvolve`), `TailBound` (`markov`,
`massGeMonoThreshold`), `ValuationTail` (`tailGeoValuation`,
`tailGeoValuationLe`, `tailHalving`, `markovGeoValuation`), `ValuationMoment`
(`weightedSumGeoValuation`, `generalDrift` = E[a] >= 8/5, `growthComparison` =
3^5 <= 2^8), `ContractionDrift` (`SyracuseStepContraction`,
`growthBelowContractionScale`), `ValuationDistribution` /
`ValuationTwoClass` / `PeriodicResidue` / `PeriodicCount` (residue-class
equidistribution of the first valuation), `DescentSetPositive`
(`goodStepDescentSet`, `descentOnRes1mod4`), `Density` / `CarrierDensity` /
`DensityExtra` (natural-density "almost all" closure algebra),
`Pieces64.exactAffine` (the exact affine backbone).

---

## Phase A — close `?subA8`: large-deviation drift past a fixed time (step 4)

Goal: `subA8_assemble : TyA1 -> ... -> TyA7 -> DriftPastTy`, i.e. for every fixed
`m` a density-one set of odd `y` carrying some `n >= m` with `8n <= 5 S_n(y)`.

1. **Joint valuation law along the orbit.** New module `OrbitValuationLaw`.
   Define the distribution of the partial sum `S_n` as an explicit `FinDist`
   built by `n`-fold convolution of the single-step valuation law:
   `orbitValLaw n = convPow geoValuation n` (reuse `Convolution.convPow`,
   `ValuationTail.geoValuation`). Prove `mass (orbitValLaw n) = pow2 (mult 2 n)`
   or the appropriate normaliser (reuse `massConvPow`), so the law is a genuine
   normalised carrier, not `Unit`.

2. **First moment of `S_n`.** In `OrbitValuationLaw`, prove the closed form
   `weightedSum (orbitValLaw n) = mult n (weightedSum geoValuation ...)`
   via `charFnConvolve` / additivity of `weightedSum` under `convolve`, then
   combine with `ValuationMoment.generalDrift` to get the mean-drift inequality
   `mult 5 (weightedSum (orbitValLaw n)) >= mult 8 n` (E[S_n] >= (8/5) n).

3. **Second moment / variance of `S_n`.** Add `weightedSumSq : FinDist -> Nat`
   to `FinMeasure` and prove `weightedSumSq (orbitValLaw n) = mult n c_var` for
   the per-step constant (linear variance), reusing convolution additivity of
   the second cumulant. This seeds the concentration toolkit (item C3 of
   `REMAINING_WORK.md`).

4. **Concentration inequality on the law.** New module `OrbitConcentration`.
   From steps 2–3 prove a Chebyshev/Markov large-deviation bound on the law:
   the mass of `{ S_n : 5 S_n < 8 n }` is at most a factor decaying in `n`
   (reuse `TailBound.markov`, `ValuationTail.markovGeoValuation`,
   `massGeMonoThreshold`). This is the finitary heart of Prop. 1.9.

5. **Equidistribution transfer (law -> density).** New module
   `ValuationEquidistribution`. Prove the bridge lemma: for each `n`, the natural
   density of `{ y : OddPos : 5 (syrValSum n y) < 8 n }` equals the law-mass from
   step 4, because the valuation vector `(a_1(y),...,a_n(y))` equidistributes
   over residue classes mod `2^{2n}` (reuse `ValuationDistribution.res1mod8Form`,
   `ValuationTwoClass`, `PeriodicResidue`, `PeriodicCount`). This is the genuine
   Syracuse-arithmetic input the density algebra cannot supply.

6. **Density-one drift set for a fixed `n`.** Combine steps 4–5: the complement
   `{ y : 5 (syrValSum n y) < 8 n }` has small density, so
   `{ y : 8 n <= 5 (syrValSum n y) }` has density -> 1 as `n` grows
   (reuse `Density`/`CarrierDensity` closure, `subA5_intersect`,
   `subA4_sizeCofinite`). Prove it as a reusable lemma `driftAtDensity n`.

7. **Existence past `m` on a density-one set.** For fixed `m`, choose `n >= m`
   large enough that `driftAtDensity n` gives density `> 1/2`; take the
   density-one union over `n >= m` (monotone in `n` via step 4's decay), yielding
   `good` with `AlmostAllOddD good` and, for each `good y`, some `n >= m` with
   `8n <= 5 S_n(y)`. Package with `subA3_valSumGeLen`, `subA6_driftMono`.

8. **Close `?subA8`.** Assemble steps 6–7 into `subA8_assemble` (consuming the
   already-proved `subA1..subA7` for the plumbing), replacing `?subA8` in
   `Pieces64.idr`. `piece34_driftPastMDensity` becomes hole-free; rebuild green
   and re-grep for banned constructs.

---

## Phase B — close `?subB8`: uniform diagonalisation to a growing height (step 4)

Goal: `subB8_assemble : TyB1 -> ... -> TyB7 -> DriftUniformTy`, upgrading the
fixed-`m` family from Phase A to a single density-one set that works for a
height `f -> infinity`. Must use concrete `syrValSum` arithmetic (see honesty
constraint 2).

9. **Explicit coherent family.** Reconstruct the Phase-A good sets `good_m` as an
   *explicit predicate* `goodM m y := decision (8 (nWit m y) <= 5 (syrValSum (nWit m y) y))`
   with `nWit m y >= m` the least valid witness, so the family is defined by a
   concrete formula rather than an abstract existential. Prove `good_m` is
   antitone in `m` (larger `m` = smaller set), the coherence `?subB8` needs.

10. **Quantitative complement rate.** Prove a decay bound
    `densityComplement (goodM m) <= rate m` with `rate m -> 0`, threading the
    step-4 concentration decay explicitly through the equidistribution transfer
    (step 5). This quantitative rate is exactly what the abstract schema in
    `DiagonalizationLimit` lacks.

11. **Diagonal predicate against `f`.** Define `goodDiag f y := goodM (f y) y`
    using `subB4_heightReachable` to get a witness time `n >= f y` and
    `subB1_inflatedGrows` for the inflated height. This is the concrete
    diagonal that `DiagonalizationLimit` shows cannot be built abstractly.

12. **Density one of the diagonal.** Prove `AlmostAllOddD (goodDiag f)` from the
    decay rate of step 10: because `f y -> infinity`, the local threshold used at
    `y` tightens, but the complement rate is summable over the (finitely many
    relevant) thresholds — formalise via `Density`/`CarrierDensity` closure and a
    Borel–Cantelli-style density lemma (new lemma `diagDensityOne`). This is the
    genuine analytic core of `?subB8`.

13. **Drift survives at the diagonal witness.** For `goodDiag f y` show the
    witness `n` satisfies both `Leq (f y) n` and `8n <= 5 S_n(y)`, using
    `subB3_boundWeaken` and `subB5_driftMono`.

14. **Height-monotone transfer.** Wire `subB2_heightTransfer` so the statement
    holds for any `g >= f` with `f -> infinity`, matching `DriftUniformTy`'s
    universally-quantified height.

15. **Predicate-implication plumbing.** Discharge the density bookkeeping
    (`subB6_intersect`, `subB7_densityMono`) needed to present `goodDiag` as a
    `Bool`-valued predicate with `AlmostAllOddD`.

16. **Close `?subB8`.** Assemble steps 11–15 into `subB8_assemble`, replacing
    `?subB8`. Confirm it does **not** reduce to the false abstract schema by
    checking it genuinely mentions `syrValSum` (cross-check against
    `DiagonalizationLimit.noUniformLateWitnessForPDiag`). `piece35` /
    `piece36` / `piece62_step4` become hole-free; rebuild green and re-grep.

---

## Phase C — close `?subC8`: descent at a strictly positive time (step 6)

Goal: `subC8_assemble : TyC1 -> ... -> TyC7 -> DescentPosTy`, producing a
density-one set with descent `oddSize (iter n Syr y) <= oddSize y` at some
`n >= 1`. The weak hypothesis `TypicalDescentDensity` alone is satisfiable at
`n = 0`, so the assembler must build the positive-time descent from the genuine
drift (Phase A output `piece33`, the `m = 1` instance) and `exactAffine`, which
are in module scope.

17. **Contraction from drift at a positive time.** New module `PositiveDescent`.
    From `piece33_driftLargeDensity` (density-one `n >= 1` with `8n <= 5 S_n(y)`)
    and `ContractionDrift.growthComparison` (3^5 <= 2^8) derive the scale
    inequality `mult (natPow 3 n) (oddSize y) <= pow2 (syrValSum n y)` on the
    density-one set (reuse `growthBelowContractionScale`, `StepArith2`).

18. **Affine identity to a size bound.** Feed the scale inequality of step 17
    into `Pieces64.exactAffine` (the exact `2^{S_n} Syr^n = 3^n x + c`
    backbone). Prove `pow2 (syrValSum n y) * oddSize (iter n Syr y) = 3^n * oddSize y + c`
    and hence, dividing by `pow2 (syrValSum n y)`, `oddSize (iter n Syr y) <= oddSize y`
    once `3^n oddSize y <= pow2 (syrValSum n y)`.

19. **Control the additive constant `c`.** Prove `c < pow2 (syrValSum n y)` on a
    density-one size threshold (`subA4_sizeCofinite` / large `oddSize y`), so the
    additive term cannot spoil the descent. Bound `c` by the geometric partial
    sum `sum 3^k pow2(...)` from the induction in `exactAffine`.

20. **Positive-time descent, density form.** Combine steps 17–19: on the
    intersection (density one, `subC6_intersect`) of the drift set (`n >= 1`) and
    the size threshold, `oddSize (iter n Syr y) <= oddSize y` with `n >= 1`.
    This is the genuine statement `n = 0` cannot give.

21. **Discharge the trivial-time exclusion.** Use `subC3_composePos`,
    `subC4_iterSucc`, `subC5_stepPos` to certify the witness index is a genuine
    successor and lands on a positive value, ruling out the `n = 0` reading
    demanded by `DescentPosTy`.

22. **Witness repackaging.** Wrap the witness with `subC7_repackage` and
    `subC2_descentCompose` into the exact `(n ** (Leq 1 n, Leq ...))` shape.

23. **Density bookkeeping.** Present the good set as a `Bool` predicate with
    `AlmostAllOddD` via `subC6_intersect` and the `Density` closure algebra;
    confirm non-degeneracy analogous to `piece54_descentNondegenerate`.

24. **Close `?subC8`.** Assemble steps 20–23 into `subC8_assemble` (using the
    module-scope `piece33` / `exactAffine`, not the weak formal input),
    replacing `?subC8`. `piece50_descentTimePositive` becomes hole-free; rebuild
    green and re-grep.

---

## Phase D — close `?subD8`: renewal first passage below a growing height (step 7)

Goal: `subD8_assemble : TyD1 -> ... -> TyD7 -> DiagonalHeightTy`, i.e. from
typical (positive-time) descent, a density-one set whose orbit falls below a
growing `f`. Must diagonalise only against `f -> infinity` (honesty
constraint 1).

25. **Renewal step from positive descent.** New module `RenewalFirstPassage`.
    Package the Phase-C output (`piece50` positive descent) as one renewal step:
    a density-one set on which `oddSize (iter n Syr y) <= oddSize y` with
    `n >= 1`, plus the lift `subD4_renewalLift` carrying `SyrBelow` of the orbit
    point back to the start.

26. **Strict decrease measure.** Strengthen step 25 (or the size threshold) to a
    *strict* decrease `oddSize (iter n Syr y) < oddSize y` on a density-one set,
    using the same drift/affine margin as Phase C (the constant-`c` slack of
    step 19 gives a strict gap for large `oddSize`). This makes `oddSize` a
    well-founded rank for the renewal.

27. **Well-founded renewal iteration.** Define a total Idris function
    `passBelow : (y : OddPos) -> (bound : Nat) -> ...` that repeatedly applies
    the positive strict-descent step until `oddSize <= bound`, terminating by
    structural recursion on a `Nat` fuel equal to `oddSize y` (no `assert_*`;
    fuel decreases with the strict decrease of step 26). Produces a concrete
    first-passage time.

28. **Density one across finitely many rounds.** Prove the renewal set stays
    density one: at most `oddSize y` rounds are needed, each intersecting a
    density-one descent set (`subD6_intersect`, `piece57_renewalUniform`);
    finite intersections of density-one sets are density one.

29. **First passage below the growing height.** For `f -> infinity`, run
    `passBelow` with `bound = f y`: since `oddSize` strictly decreases and `f y`
    can be any value, the orbit reaches `oddSize <= f y`, giving
    `SyrBelow y (f y)` via `subD1_descentToSyrBelow` / `subD3_belowLift`.
    Crucially this uses `f -> infinity` only through `subD5_heightTransfer` and
    never asserts passage below a fixed `b` (avoids the uninhabited `piece58`).

30. **Height/predicate plumbing.** Discharge `subD2_belowMono`,
    `subD5_heightTransfer`, `subD6_intersect`, `subD7_densityMono` to assemble
    the `(good ** (AlmostAllOddD good, ... SyrBelow y (f y)))` shape of
    `DiagonalHeightTy`.

31. **Cross-check against the impossibility.** Verify (by inspecting the term)
    that `subD8_assemble` genuinely consumes `TendsToInfinityOdd f` and never
    instantiates a fixed height — i.e. it does not resurrect `piece58`. Record
    the check in the module docstring, mirroring the `piece60` note.

32. **Close `?subD8` and finish.** Assemble steps 27–31 into `subD8_assemble`,
    replacing `?subD8`. Now `piece59_diagonalHeight` / `piece64_step7` are
    hole-free, so `HoleProof`'s `step4`/`step6`/`step7` all rest on proved
    terms. Final verification: `idris2 --build taocollatz.ipkg` exit 0, the
    banned-construct grep is empty, and no `?`-hole remains
    (`grep -RnE '\?[a-z]' TaoCollatz/` shows none of `subA8`/`subB8`/`subC8`/
    `subD8`). Update `TRACKING.md` / `REMAINING_WORK.md` to mark the four nodes
    as carrying genuine content. `theorem13` is then unconditional.

---

## Dependency summary

```
Phase A (steps 1-8)  ──►  ?subA8  ──►  piece34 ─┐
Phase B (steps 9-16) ──►  ?subB8  ──►  piece35 ─┴► piece62_step4 ─┐
Phase C (steps 17-24)──►  ?subC8  ──►  piece50 ───► (step6 aux)   ├► theorem13
                          exactAffine ──────────► piece63_step6 ──┤
Phase D (steps 25-32)──►  ?subD8  ──►  piece59 ───► piece64_step7 ─┘
```

- Phase B depends on Phase A (it diagonalises A's family).
- Phase C depends on Phase A's `piece33` and on `exactAffine` (already proved).
- Phase D depends on Phase C's positive-time descent.
- The new modules to add to `taocollatz.ipkg`: `OrbitValuationLaw`,
  `OrbitConcentration`, `ValuationEquidistribution`, `PositiveDescent`,
  `RenewalFirstPassage` (plus the small additions to `FinMeasure`).

The genuinely hard, research-level content is concentrated in **steps 4–5**
(finitary concentration + equidistribution transfer, Prop. 1.9), **steps 10–12**
(quantitative diagonalisation, the part `DiagonalizationLimit` proves needs real
Syracuse arithmetic), and **steps 26–27** (strict-descent renewal). Everything
else is arithmetic/plumbing that reuses declarations already in the tree.
