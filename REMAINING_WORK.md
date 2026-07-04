# What is left for a 100% self-contained proof

This file is a single, focused matrix of everything that still stands between the
current Idris2 development and a **100% self-contained, unconditional** machine
proof of Tao's Theorem 1.3 ("almost all Collatz orbits attain almost bounded
values"). It complements `TRACKING.md` (which catalogues what *is* done); here we
list only the **gaps**.

The whole tree builds under Idris2 0.8.0 (`idris2 --build taocollatz.ipkg`), is
`%default total`, and uses **no** `believe_me`, `postulate`, `assert_total`,
`assert_smaller`, `%foreign`, `idris_crash`, axioms, or holes. So the remaining
gaps are **not** cheats: they are honestly-typed nodes whose *payload* carries no
analytic content yet. Filling them is the mathematics that is left.

## Legend

| Mark | Meaning |
|---|---|
| 🟥 **Missing content** | Type is an honest placeholder (payload `Type`, inhabited by `Unit`) or an explicit hypothesis; **no analytic mathematics is proved**. This is the real work. |
| 🟧 **Missing infrastructure** | A supporting theory (probability/measure/Fourier) that Idris's base library does not provide and must be built before the content nodes can even be stated with teeth. |
| 🟦 **Structural, waiting** | Reduction/plumbing lemma that is *already fully proved*; it becomes real automatically the moment its placeholder input carries content — no further proof work. |

---

## A. The single gate: what the whole proof currently rests on

Everything downstream (the reduction chain, the genuine natural-density model,
the odd-part/Syracuse simulation) is proved. The entire proof is reduced to
**one** honest, non-vacuous hypothesis. Discharging it (from §B/§C below) makes
the main theorem unconditional.

| # | What must be proved | Idris node | Module | Status |
|---|---|---|---|---|
| A1 | Density-one Syracuse first-passage control: for every `f → ∞`, almost all `x` have `SyrBelow (oddPart x) (f x)` | `SyracuseDensityControl` (hypothesis of `theorem13GenuineFromSyracuse`) | `MinimalProof` | 🟥 Missing content |

> This is precisely the analytic conclusion of Tao's Theorem 1.6 / Prop. 1.9 /
> Prop. 7.8, transported to the genuine natural-density "almost all" of the
> `Density` / `CarrierDensity` model. Once A1 is a real term, `MinimalProof`'s
> `theorem13GenuineFromSyracuse` yields the genuine main theorem with no other
> assumptions.

---

## B. Deep analytic estimates (the mathematical heart)

These are the genuinely hard estimates from the paper. Their Idris types are
opaque placeholders (payload `Type`, inhabited by `()`); the reductions that
consume them are real, but no analytic content is proved.

| # | Paper result | Idris placeholder | Module | Status |
|---|---|---|---|---|
| B1 | Prop. 1.9 — 2-adic valuation tail estimate for the Syracuse first passage | `FirstPassageTailEstimate` payload upgraded to `genuineTailEstimate` (exact survival function `tailGeoValuation`), threaded via `proposition19` | `ValuationTail`, `GenuineEstimates`, `PaperAssumptions` | 🟩 **Genuine distributional content proved** (exact tail + exp. decay + halving + Markov); the density-one *almost-all* upgrade still routes through gate A1 |
| B2 | Prop. 7.8 — renewal / stability (monotonicity) estimate | `FirstPassageStabilityEstimate` payload upgraded to `genuineStabilityEstimate` (tail monotonicity), threaded via `renewalMonotonicity` | `ValuationTail`, `GenuineEstimates`, `PaperAssumptions` | 🟩 **Genuine monotonicity content proved**; full quantitative renewal estimate still routes through gate A1 |
| B3 | Prop. 1.14 — fine-scale mixing / equidistribution of the Syracuse random variable | `FineScaleMixing` | `PaperInterfaces` | 🟥 Missing content |
| B4 | Prop. 1.17 — Fourier / characteristic-function decay | `FourierDecay` | `PaperInterfaces` | 🟥 Missing content |
| B5 | Prop. 7.1 — key quantitative Fourier estimate | `KeyFourierEstimate` | `PaperInterfaces` | 🟥 Missing content |
| B6 | Prop. 7.3 — renewal "white points" combinatorial input | `RenewalWhitePoints` | `PaperInterfaces` | 🟥 Missing content |
| B7 | Prop. 1.11 — stabilisation of first passage | `StabilisationOfFirstPassage`, `analyticInputToStabilisation` | `Dependencies` | 🟦 Structural, waiting (real once B1–B2 are real) |

---

## C. Supporting infrastructure that must be built first

The base library gives none of this; it has to be formalized before B1–B6 can be
*stated* with real content (let alone proved).

| # | Missing theory | Needed for | Status |
|---|---|---|---|
| C1 | Probability / measure layer: distributions on `N`, measures on the 2-adics `Z_2`, expectations, tail bounds | B1, B2, B3 | 🟧 Missing infrastructure |
| C2 | The Syracuse valuation random variables `a_n(x)` and their (geometric) distribution | B1 | 🟧 Missing infrastructure |
| C3 | Sub-Gaussian / exponential tail-bound toolkit | B1, B2 | 🟧 Missing infrastructure |
| C4 | Discrete Fourier analysis / characteristic functions on `Z/NZ` and their decay estimates | B4, B5 | 🟧 Missing infrastructure |
| C5 | Renewal-process formalism (first-passage times, monotonicity) | B2, B6 | 🟧 Missing infrastructure |

---

## D. Measure-theoretic "almost all" resolution

The genuine natural-density model (`Density`, `CarrierDensity`) is built and
non-degenerate. What remains is to connect it to the paper's *logarithmic*-density
"almost all" and to populate the density leaves from the analytic base estimate.

| # | Gap | Idris node | Module | Status |
|---|---|---|---|---|
| D1 | Replace the opaque smallness payload / fixed-0 error bound with a genuine logarithmic-density notion | `AlmostAllOn`, `ExceptionalControl`, `ExceptionalSmall`, `LogarithmicSmallness` | `Large` | 🟥 Missing content |
| D2 | Wire the genuine `Density`/`CarrierDensity` arithmetic into the chain leaves (needs the analytic base estimate of §B) | `AlmostAllPosD`, `AlmostAllOddD` ⟶ `SyracuseDensityControl` | `CarrierDensity`, `MinimalProof` | 🟦 Structural, waiting |

---

## E. Already discharged — NOT part of the remaining work

Listed here so the matrix is unambiguous about the boundary.

| Item | Idris node | Module | Status |
|---|---|---|---|
| Odd-threshold system (was a hypothesis) | `theorem16ToTheorem13Constructive`, `centralTheoremUnconditional` | `OddThreshold` | ✅ Proved (hypothesis removed) |
| Odd-part ⇔ Syracuse orbit simulation | `provenOddPartOrbitSimulation`, `colBelowFromSyrBelow` | `OddPart`, `MinimalProof` | ✅ Proved |
| Full reduction chain 1.6⇒1.3, 3.1⇒1.6, 1.11⇒3.1 | `theorem16ToTheorem13*`, `theorem31ToTheorem16FromPrinciple`, `proposition11ToTheorem31FromIteration` | `Dependencies` | ✅ Proved (plumbing) |
| Genuine natural-density "almost all" + closure algebra | `Negligible`, `AlmostAll`, `and/orAlmostAll`, `AlmostAllPosD`, `AlmostAllOddD`, non-degeneracy | `Density`, `DensityProperties`, `DensityClosure`, `CarrierDensity`, `DensityExtra` | ✅ Proved |
| Algebraic core (matrices, affine monoid, parity group, determinant growth) | `Matrix`, `Affine`, `Parity`, `Algebra`, `OddStepClosed`, `Determinant`, `MatrixDynamics`, `MatrixGrowth` | (those modules) | ✅ Proved |

---

## Bottom line

A 100% self-contained proof requires, in order:

1. **Build infrastructure C1–C5** (probability/measure on `N`/`Z_2`, tail bounds,
   discrete Fourier analysis, renewal processes). None exists in the base library.
2. **Prove the analytic estimates B1–B6** on top of that infrastructure; B7 and
   D2 then follow automatically (they are already-proved structural reductions).
3. **Upgrade the "almost all" resolution D1** to genuine logarithmic density and
   thread the B-estimates through to discharge the single gate **A1**
   (`SyracuseDensityControl`).

At that point `theorem13GenuineFromSyracuse` (already proved) delivers the
genuine main theorem with **zero** hypotheses and **zero** placeholders — a fully
self-contained formalization of Theorem 1.3.

**Count of remaining content nodes:** 1 gate (A1) + 6 deep estimates (B1–B6) +
1 "almost all" resolution (D1) = **8 mathematical nodes**, sitting on **5 pieces
of missing infrastructure (C1–C5)**. Everything else (structural node B7,
wiring D2, and all of §E) is already proved and waits only on these.
