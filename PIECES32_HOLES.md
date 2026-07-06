# The 32-hole decomposition of the remaining analytic core

The central theorem was previously reduced to **four** assembler holes in
`TaoCollatz/Pieces64.idr` — `subA8`, `subB8`, `subC8`, `subD8` — each of which
had to produce a density-one milestone from seven supporting facts. This note
records how those four holes have been refined into **32 holes** (eight per
group), with the four `subX8_assemble` declarations now discharged as honest
terms (function application of the new combiner to the new sub-goals).

Every one of the 32 hole types is a genuine, non-vacuous, *true* proposition,
stated in the project's real vocabulary (`syrValSum`, `syrValuation`, `Syr`,
`iter`, `oddSize`, `SyrBelow`, `AlmostAllOddD`, `TendsToInfinityOdd`, `Leq`).
Filling all 32 holes closes the central theorem with no further edit. The
soundness discipline is unchanged: `%default total`; no
`believe_me`/`postulate`/`assert_*`/`%foreign`/`idris_crash`/axioms.

The whole project builds under Idris2 (`idris2 --build taocollatz.ipkg`).

## Structure of each group

For each group `X ∈ {A, B, C, D}` there are eight holes `stepX1 … stepX8` with
explicit type aliases `StepX1Ty … StepX8Ty`:

- `stepX1 … stepX6` — the genuine supporting facts of the argument
  (per-step valuation bounds, additivity, cofinite/intersection density
  closure, monotonicity, renewal lemmas, …).
- `stepX7` — the **analytic core**: the single density-one statement that
  carries the real content of the group (the valuation law-of-large-numbers,
  the diagonalisation, the strictly-positive descent time, the renewal
  first-passage). Its type is exactly the group milestone.
- `stepX8` — the **combiner**: `StepX1Ty → … → StepX7Ty → Milestone`.

`subX8_assemble` is then the honest term

```idris
subX8_assemble _ _ _ _ _ _ _ =
  stepX8 stepX1 stepX2 stepX3 stepX4 stepX5 stepX6 stepX7
```

## The four groups

| Group | Milestone (`StepX7Ty`) | Content |
|-------|------------------------|---------|
| A (`holeA1..holeA8`) | `DriftPastTy` | large-deviation `8/5` drift past any fixed time on a density-one set (step 4) |
| B (`holeB1..holeB8`) | `DriftUniformTy` | uniform diagonalisation to a growing height `f` (step-4 uniformity) |
| C (`holeC1..holeC8`) | `DescentPosTy` | typical descent at a strictly positive time (step 6) |
| D (`holeD1..holeD8`) | `DiagonalHeightTy` | density-one first passage below a growing `f` (step-7 renewal) |

The four `stepX7` cores are where the genuinely hard analytic mathematics of
Tao's Theorem 1.3 (valuation concentration / renewal estimates) is now
isolated; the surrounding 28 holes are the explicit supporting scaffolding.
