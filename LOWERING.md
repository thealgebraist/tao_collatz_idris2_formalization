# Lowering the remaining holes to simpler domains

This note answers the request to *find an equivalent way to formalize the four
remaining holes of the central theorem by lowering the theories down to a
simpler domain* — group theory, matrix theory, lattice/order theory, or basic
axiomatic (ZFC) set theory and arithmetic constructions.

It states, per domain, exactly **what can be lowered** (with the concrete,
machine-checked Idris artifact that does it) and **what cannot** (with the
machine-checked reason). The short version:

* The **scaffolding** around the holes (the "almost all / natural density"
  layer, the affine/valuation algebra, the moment/measure model) genuinely
  lowers to order/lattice theory and to matrix/measure theory, and this is done
  in the project.
* The **content** of the holes — Tao's density-form valuation
  equidistribution / large-deviation estimate — is *irreducible*: it provably
  does **not** follow from the density algebra of any of these simpler domains.
  The project contains a machine-checked proof of this obstruction. Lowering
  cannot make the holes disappear, only relocate them; a genuine closure would
  be an elementary proof of the density form of Collatz, which is not known.

All Idris artifacts referenced below build with Idris2 0.8.0
(`idris2 --build taocollatz.ipkg`, exit 0) with `%default total` and no
`believe_me` / `postulate` / `assert_*` / `%foreign` / `idris_crash` / axioms.

---

## The four holes (recap)

In `TaoCollatz/Pieces64.idr`:

| hole | type | content |
|------|------|---------|
| `?coreA_driftPast` (`gA15`) | `DriftPastTy` | for each fixed `m`, a.e. odd `y` has some time `n ≥ m` with `8n ≤ 5·S_n(y)` (density-form valuation LLN) |
| `?coreB_diagonalization` (`gB15`) | `DriftUniformTy` | upgrade that family to a single density-one set drifting past a *growing* height `f → ∞` |
| `?coreC_positiveDescent` (`gC15`) | `DescentPosTy` | on a density-one set the Syracuse descent time can be taken `n ≥ 1` |
| `?coreD_renewal` (`gD15`) | `DiagonalHeightTy` | density-one first passage below a growing height `f → ∞` |

Here `S_n(y) = syrValSum n y` and `AlmostAllOddD p` = "the complement of `p` has
natural density zero" (`TaoCollatz.Density`, a genuine density, not a cofinite
placeholder).

---

## 1. Order / lattice theory — `TaoCollatz/DensityFilter.idr` (new)

**What lowers.** The entire "almost all" layer is pure order/lattice theory.
The natural-density-one predicates on the odd numbers form a genuine **proper
filter** on the boolean lattice `(OddPos -> Bool)`:

* `densityFilter : OddFilter` packages the three filter laws as the already-proved
  density closure lemmas — top membership (`almostAllOddTrue`), upward closure
  under the pointwise order `Implies` (`almostAllOddMono`), and closure under
  binary meet `\x => p x && q x` (`andAlmostAllOdd`).
* `densityFilterProper : InDensity botOdd -> Void` proves it is **proper** (the
  empty set / bottom element is not density one).

Each hole is then **faithfully relocated** into this order-theoretic language:
the types `DriftPastFilterTy`, `DriftUniformFilterTy`, `DescentPosFilterTy`,
`DiagonalHeightFilterTy` are the hole types with every `AlmostAllOddD good`
replaced by the filter membership `InDensity good`, and the equivalences

```
driftPast_toFilter / driftPast_fromFilter        : DriftPastTy      <-> DriftPastFilterTy
driftUniform_toFilter / driftUniform_fromFilter  : DriftUniformTy   <-> DriftUniformFilterTy
descentPos_toFilter / descentPos_fromFilter      : DescentPosTy     <-> DescentPosFilterTy
diagonalHeight_toFilter / diagonalHeight_fromFilter : DiagonalHeightTy <-> DiagonalHeightFilterTy
```

are all the **identity** (the two sides are definitionally equal, so nothing is
weakened). Filling an order-theoretic hole is *exactly* filling the analytic one.

**What does not lower (machine-checked).** A filter is closed only under
**finite** meets. The content of `coreB`/`coreD` is a *countable / diagonal*
combination — selecting, along a growing height `f → ∞`, one member of a whole
family of density-one sets — and the density-one filter is **not** closed under
that operation. This is not a soft claim: `TaoCollatz.DiagonalizationLimit`
proves

```
noUniformLateWitnessForPDiag : UniformLateWitness pDiag -> Void
```

i.e. for the explicit predicate `pDiag y n = (n < oddSize y)`, every fixed
bound `m` is met on a density-one set (`pDiagFixedFamily`), yet **no** density-one
set can witness a late index past `f y = oddSize y`. Consequently the abstract
"diagonal-selection closure" that would reduce `coreB` to a filter property is
**false**, so `coreB` cannot be discharged by order/lattice algebra alone: any
proof must use the specific arithmetic of the Syracuse valuation sums (namely
that the drift witness times are genuinely unbounded, not capped like `pDiag`).

---

## 2. Matrix theory / finite measure theory — already in the project

**What lowers.** The analytic core `coreA` reduces, at the level of the *mean*,
to classic 2×2/3×3 matrix algebra on a finitely supported measure carrier:

* `TaoCollatz/FinMeasure.idr`, `TaoCollatz/Convolution.idr` — the measure
  carrier `FinDist`, its `mass` / `weightedSum`, convolution `⋆` and the
  convolution/Fourier laws (`massConvolve`, `charFnConvolve`).
* `TaoCollatz/ValuationDriftMatrix.idr` — the **transfer matrix** whose powers
  generate the moment vector `(mass, weightedSum)` of the `n`-step convolution
  power; the `8/5` drift cone is invariant under it, giving
  `sumDriftGeoValuation` = the drift `8·n·mass ≤ 5·weightedSum` **in
  expectation** for the genuine geometric 2-adic valuation measure.
* `TaoCollatz/ValuationVarianceMatrix.idr` — the 3×3 covariance transfer matrix
  and the second-moment convolution law, giving `Var(S_n) = O(n)` — the input to
  a Chebyshev concentration bound.

So "the mean valuation drifts at rate `2 > 8/5`, with linearly growing variance"
is fully machine-checked classic linear algebra (see `MATRIX_DRIFT.md`).

**What does not lower.** Two steps remain, and both are genuinely analytic
(documented, not papered over, in `MATRIX_DRIFT.md`):

1. **Concentration / normalisation.** Turning `E[S_n] ≥ 8n/5` plus
   `Var(S_n) = O(n)` into a *density-one* statement is Chebyshev, which needs a
   **rational/real** normalisation of the (unnormalised, `Nat`-valued) `FinDist`
   moments by the total mass — it cannot be carried out inside `Nat`. This is the
   "arithmetic construction" gap of §4.
2. **Coupling to the genuine dynamics.** The model computes moments of the
   *independent* geometric increment; `S_n(y)` is the valuation sum along the
   *actual* Syracuse orbit. Identifying / dominating the true orbit valuations by
   the independent model is the equidistribution content of Tao's paper — exactly
   the content §1's `DiagonalizationLimit` shows the density algebra cannot
   supply.

---

## 3. Group theory (affine / matrix action) — the arithmetic backbone

**What lowers.** The exact Syracuse dynamics is an affine action, captured by
`ExactAffineDynamics` (`Pieces64`): for every odd `x` and `n`,

```
2^{S_n(x)} · oddSize(iter n Syr x) = 3^n · oddSize(x) + c
```

This is the backbone behind the contraction estimate `piece30_contractionArith`
(`8n ≤ 5·S_n` and `n ≥ 243·c^5` force `3^n·c ≤ 2^{S_n}`), and it is exactly the
image of the monoid generated by the affine maps `x ↦ (3x+1)/2^v`. The
project's `TaoCollatz/Matrix.idr`, `TaoCollatz/MatrixDynamics.idr`,
`TaoCollatz/MatrixGrowth.idr`, `TaoCollatz/Determinant.idr` develop the honest
2×2 integer-matrix layer for this action; the growth comparison `3^5 ≤ 2^8` is
the group-theoretic drift condition.

**What does not lower.** The affine/matrix action is *deterministic algebra*; it
says nothing about how often the valuation `v = a_k(x)` is large. The
distribution of the exponents `a_k` along an orbit — which is what makes the
product `∏ 3/2^{a_k}` contract for typical `x` — is again equidistribution, not
a group identity. Group/matrix theory delivers the backbone, not the statistics.

---

## 4. Basic set theory / explicit arithmetic constructions

**What lowers.** Every notion used in the holes is already built from first
principles with explicit arithmetic constructions, with no appeal to classical
choice or an oracle: natural density (`Negligible`/`AlmostAll` in
`TaoCollatz/Density.idr`) is a concrete `∀k. ∃n₀. ∀N≥n₀. count·(k+1) ≤ N`
statement; the valuation `oddPartDropTime`, the sums `syrValSum`, the measure
`FinDist`, and the geometric model `geoValuation` are all explicit inductive /
recursive constructions over `Nat`. In this sense the whole development already
lives in "basic axiomatic set theory + explicit arithmetic".

**The one genuinely missing arithmetic construction.** As noted in §2, the
concentration step needs the moments *normalised* — a rational/real measure
layer — because the mean `weightedSum/mass` and the Chebyshev deviation are not
`Nat`. Adding a `ℚ`- (or `Integer`-cross-multiplied) expectation layer and
proving Chebyshev on the **model** measure would close gap 2.1 *at the model
level*, reducing `coreA` to the single **coupling/equidistribution bridge**
(gap 2.2). That bridge — "the empirical distribution of `(a_1,…,a_n)` along a
typical Syracuse orbit matches the geometric model" — is the irreducible core
and is **not** a set-theoretic or arithmetic identity: it is the analytic
theorem itself.

---

## Summary table

| domain | lowers the … | artifact | residual (irreducible) |
|--------|--------------|----------|------------------------|
| order / lattice | "almost all" density layer → proper filter; holes relocated | `DensityFilter.idr` (new) | diagonal/countable closure is **false** (`DiagonalizationLimit`) |
| matrix / measure | mean drift + linear variance of the model | `ValuationDriftMatrix`, `ValuationVarianceMatrix` | concentration (needs ℚ) + coupling |
| group / affine | exact affine backbone + growth comparison | `Matrix*`, `Pieces64.ExactAffineDynamics` | exponent statistics |
| set theory / arithmetic | all notions are explicit constructions over `Nat` | `Density`, `FinMeasure`, `GeometricValuation` | rational normalisation, then coupling |

**Bottom line.** All four holes reduce to a single irreducible statement — the
2-adic valuation **equidistribution / concentration** of the genuine Syracuse
orbit (Tao's Theorem, density form). Every simpler domain lowers the
surrounding structure faithfully, and the project now makes the order/lattice
lowering explicit and machine-checked, but no simpler domain can lower the
content: `DiagonalizationLimit.noUniformLateWitnessForPDiag` is a machine-checked
proof that the natural density-algebra route to the key hole cannot exist.
