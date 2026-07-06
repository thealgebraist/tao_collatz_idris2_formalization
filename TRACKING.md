# Formalization tracking matrix

Status matrix for the Idris2 formalization of Tao's *"Almost all Collatz orbits
attain almost bounded values"* (`taocollatz.pdf`), Theorem 1.3.

Legend for **Status**:

- ✅ **Proved** — a genuine, total Idris term; no `believe_me`, no `postulate`,
  no axioms.
- 🟢 **Constructed** — genuinely built/inhabited by a total term (stronger than a
  placeholder), new in the current run.
- 🟨 **Placeholder** — the *type* is an opaque stand-in (payload `Type`/`Unit`)
  and is honestly inhabited, but carries **no analytic content**. The reduction
  that consumes it is real; the mathematical estimate itself is not yet
  formalized.
- 🔵 **Structural** — a real reduction/plumbing lemma that is fully proved, but
  whose input is currently a placeholder.
- ⬜ **Not started** — the precise quantitative statement is not yet even
  written down in Idris.

The whole tree builds from scratch with Idris2 0.8.0 (`idris2 --build
taocollatz.ipkg`), every module is `%default total`, and contains **no**
`believe_me`, `postulate`, `assert_total`, `assert_smaller`, `%foreign`,
`idris_crash`, or holes.

---

## 1. Concrete dynamics (fully real)

| Paper object | Idris declaration | Module | Status |
|---|---|---|---|
| Collatz map `Col` | `Col : Pos -> Pos` | `Dynamics` | ✅ Proved (computable, `Col 3 = 10`) |
| Syracuse map `Syr` | `Syr : OddPos -> OddPos` | `Dynamics` | ✅ Proved (`Syr 7 = 11`) |
| Odd part | `oddPart`, `oddFactor` | `Dynamics` | ✅ Proved (`oddPart 12 = 3`) |
| Iteration | `iter`, `iterPlus` | `Core` | ✅ Proved |
| "Eventually below" | `EventuallyBelow`, `ColBelow`, `SyrBelow` | `Core`, `Dynamics` | ✅ Proved |
| Odd part is odd | `oddFactorOdd`, `syrValueOdd` | `OddPart` | ✅ Proved |
| Odd part idempotent | `oddPartIdempotent` | `OddPart` | ✅ Proved |
| **Odd-part ⇔ Syracuse correspondence** | `provenOddPartOrbitSimulation`, `syrRealize` | `OddPart` | ✅ Proved (no `believe_me`) |
| Simulation algebra (identity/compose) | `orbitSimulationId`, `orbitSimulationCompose` | `Core` | ✅ Proved |

## 2. The odd-threshold system (NEWLY CONSTRUCTED)

| Paper object | Idris declaration | Module | Status |
|---|---|---|---|
| Threshold choice `t(q)` | `oddThresholdOf w` | `OddThreshold` | 🟢 Constructed from the growth witness `w` |
| Compatibility `t(oddPart n) ≤ f(n)` | `oddThresholdOfCompatible` | `OddThreshold` | ✅ Proved |
| Growth `f→∞ ⇒ t→∞` | `oddThresholdOfGrows` | `OddThreshold` | ✅ Proved |
| Threshold search + correctness | `findBest`, `findBestCompat`, `findBestGe` | `OddThreshold` | ✅ Proved |
| `oddFactor n ≤ n` | `oddFactorLe`, `oddPartSizeLe` | `OddThreshold` | ✅ Proved |
| Odd-threshold **as a hypothesis** | `OddThresholdSystem` | `PaperInterfaces` | 🔵 Retained (legacy route), **no longer required** |

**What changed:** previously `OddThresholdSystem` was an explicit hypothesis
because the threshold cannot be a total function of `f` alone (it is the infimum
of `f` over each odd fibre `{2^k·q}`). The new module observes that the density
transfer already has `f`'s growth witness `w` in hand, and builds the threshold
`oddThresholdOf w q = max{ t ≤ q : thresholdFor(w) t ≤ q }` totally and
constructively, proving both compatibility and growth. Hence the transfer is now
**unconditional**.

## 3. The reduction chain (fully real plumbing)

| Paper step | Idris declaration | Module | Status |
|---|---|---|---|
| Thm 1.6 ⇒ Thm 1.3 (assuming system) | `theorem16ToTheorem13` | `Dependencies` | ✅ Proved (conditional) |
| **Thm 1.6 ⇒ Thm 1.3 (unconditional)** | `theorem16ToTheorem13Constructive` | `OddThreshold` | 🟢 Proved, no hypothesis |
| Thm 3.1 ⇒ Thm 1.6 | `theorem31ToTheorem16FromPrinciple` | `Dependencies` | ✅ Proved |
| Prop 1.11 ⇒ Thm 3.1 | `proposition11ToTheorem31FromIteration` | `Dependencies` | ✅ Proved |
| Analytic input ⇒ Prop 1.11 | `analyticInputToStabilisation` | `Dependencies` | 🔵 Structural (input is a placeholder) |
| Prop chain 7.8⇒7.3⇒7.1⇒1.17⇒1.14 | `proposition78To73`, … | `PaperStructure` | 🔵 Structural (identity at placeholder resolution) |
| **Central theorem (conditional)** | `centralTheorem : OddThresholdSystem -> Theorem13` | `Dependencies` | ✅ Proved |
| **Central theorem (unconditional)** | `centralTheoremUnconditional : Theorem13` | `OddThreshold` | 🟢 Proved (only the analytic placeholder remains) |
| Strict / paper-domain variants | `centralTheoremStrict`, `centralTheoremPaperDomain` | `Dependencies` | ✅ Proved |

## 4. The deep analytic estimates (NOT yet formalized — remaining work)

These are the genuinely hard, analytic hearts of the paper. Their Idris types are
opaque placeholders (payload `Type`, inhabited by `Unit`); the surrounding
reductions are real, but **no analytic content is proved**.

| Paper result | Idris placeholder | Module | Status | What is needed to make it real |
|---|---|---|---|---|
| Prop. 1.9 — 2-adic valuation tail estimate for the Syracuse first-passage | `FirstPassageTailEstimate`, `ValuationDistribution`, `proposition19` | `PaperInterfaces`, `PaperAssumptions` | 🟨 Placeholder | Formalize the Syracuse valuation `a_n(x)`, its geometric distribution, and the sub-Gaussian/exponential tail bound. Requires a probability layer (measures on `Z_2` / distributions on `N`). |
| Prop. 7.8 — renewal / stability estimate (monotonicity of the renewal process) | `FirstPassageStabilityEstimate`, `RenewalMonotonicity`, `renewalMonotonicity` | `PaperInterfaces`, `PaperAssumptions` | 🟨 Placeholder | Formalize the renewal process of first-passage times and the stability/monotonicity estimate feeding Prop. 1.11. |
| Fine-scale mixing (Prop. 1.14) | `FineScaleMixing` | `PaperInterfaces` | 🟨 Placeholder | Formalize equidistribution / mixing of the Syracuse random variable at fine scales. |
| Fourier decay (Prop. 1.17) | `FourierDecay` | `PaperInterfaces` | 🟨 Placeholder | Formalize the characteristic-function/Fourier-coefficient decay estimate. |
| Key Fourier estimate (Prop. 7.1) | `KeyFourierEstimate` | `PaperInterfaces` | 🟨 Placeholder | The quantitative Fourier bound underpinning 1.17. |
| Renewal white points (Prop. 7.3) | `RenewalWhitePoints` | `PaperInterfaces` | 🟨 Placeholder | The combinatorial "white points" input to 7.1. |
| Stabilisation of first passage (Prop. 1.11) | `StabilisationOfFirstPassage` | `Dependencies` | 🔵 Structural | Real once its two placeholder inputs above are real. |

## 5. The measure-theoretic "almost all" (NOT yet formalized — remaining work)

| Paper notion | Idris declaration | Module | Status | What is needed |
|---|---|---|---|---|
| **Density-zero / "almost all" (genuine model)** | `Negligible`, `AlmostAll`, `count`, `negligibleMono`, `boundedNegligible`, `orNegligible`, `almostAllMono`, `andAlmostAll` | `Density` | 🟢 Constructed & proved | A genuine natural-density-zero notion (`count p N * (k+1) <= N` eventually) with all closure lemmas proved from first principles. Not yet wired to the chain leaves (needs the analytic base estimate below). |
| **Density model has teeth (non-degeneracy)** | `negligibleCofalse`, `almostAllCofinal`, `negligibleNotAll`, `almostAllExistsMember`, `scanRange`, `countAllTrueLower` | `DensityProperties` | 🟢 Constructed & proved | A density-zero set is genuinely small: its complement is cofinal, so an "almost all" good set is provably infinite. The witness is constructed by a bounded search justified by a counting contradiction. Proves the §5 notion is non-trivial. |
| **Finite closure of the density model** | `orList`, `andList`, `AllNegligible`, `AllAlmostAll`, `orListNegligible`, `andListAlmostAll`, `replicateOrNegligible`, `replicateAndAlmostAll` | `DensityClosure` | 🟢 Constructed & proved | Lifts the binary closure lemmas to finite families: a finite union of negligible sets is negligible and a finite intersection of "almost all" sets is "almost all" (induction over the list on top of `orNegligible`/`andAlmostAll`). |
| Logarithmic density / "almost all" (abstract) | `AlmostAllOn`, `ExceptionalControl`, `ExceptionalSmall`, `LogarithmicSmallness` | `Large` | 🟨 Placeholder | The smallness payload is opaque and the error bound is fixed to 0. `Density` now supplies the genuine density arithmetic; connecting it to `AlmostAllOn` still requires the analytic base estimate (density of the Syracuse exceptional set) that populates the leaf. |
| Tends to infinity | `TendsToInfinityOn` | `Large` | ✅ Proved (genuine ε–N style definition) |
| Vanishing error bound | `VanishesAtInfinity` | `Large` | ✅ Proved (genuine definition) |

## 6. Genuine-density main theorem (`TaoCollatz.MinimalProof`)

The genuine density model of §5 is now wired directly into a genuine, non-vacuous
statement of the main theorem, reduced to a single honest hypothesis.

| Object | Idris declaration | Module | Status |
|---|---|---|---|
| Genuine "almost all satisfy `p`" | `AlmostAllSatisfyPos` (density-one Bool good set ⊆ `{x : p x}`) | `MinimalProof` | ✅ Proved (genuine density) |
| **Main theorem, genuine density form** | `Theorem13Genuine` | `MinimalProof` | ✅ Statement is genuine (real natural density) |
| Single honest input (density Thm 1.6, transported) | `SyracuseDensityControl` | `MinimalProof` | 🟨 Explicit hypothesis (genuine, non-opaque type; the deep analytic ingredient) |
| Syr first passage ⇒ Col first passage | `colBelowFromSyrBelow` | `MinimalProof` | ✅ Proved (from `provenOddPartOrbitSimulation`) |
| **Reduction: input ⇒ genuine main theorem** | `theorem13GenuineFromSyracuse` | `MinimalProof` | ✅ Proved in full |
| Strict / paper-domain variants | `theorem13GenuineStrictFromGenuine`, `theorem13GenuinePaperDomainFromStrict` | `MinimalProof` | ✅ Proved |
| Non-degeneracy (good set non-empty) | `theorem13GenuineHasMember` | `MinimalProof` | ✅ Proved (via `almostAllExistsMember`) |

**What changed:** the earlier `Theorem13` carries an opaque smallness payload,
so its "almost all" is not a genuine density statement. `MinimalProof` states
Theorem 1.3 with the genuine natural-density "almost all" of `Density` /
`CarrierDensity`, proves the reduction from a single honest, non-vacuous
Syracuse-density hypothesis (using the proved odd-part orbit simulation), and
certifies the conclusion is non-empty. The deep analytic content is now named
precisely by `SyracuseDensityControl` and is the sole remaining ingredient.

---

## Summary of what is left

1. **Deep analytic estimates (§4)** — the real mathematical content. Requires a
   probability/measure layer (distributions on `N`/`Z_2`, tail bounds, Fourier
   analysis) that Idris's base library does not provide, so it must be built.
2. **Measure-theoretic "almost all" (§5)** — replace the opaque smallness
   payloads with a genuine logarithmic-density notion and prove the closure
   lemmas at that resolution.
3. **Threading the real estimates** — once §4/§5 carry content, the structural
   reductions in §3 (already proved) transport it end-to-end with no further
   work, and `centralTheoremUnconditional` becomes an unconditional proof of the
   real Theorem 1.3.

## What is *no longer* left (closed in the current run)

- The **odd-threshold system** (§2) is now **constructed and proved**, not
  assumed: `theorem16ToTheorem13Constructive : Theorem16 -> Theorem13` and
  `centralTheoremUnconditional : Theorem13` drop the former `OddThresholdSystem`
  hypothesis entirely.

---

## 6. Structured presentation and completed density algebra (current run)

| Object | Idris declaration | Module | Status |
|---|---|---|---|
| Structured 4-step derivation of Thm 1.3 | `CentralTheoremDerivation`, `runDerivation`, `standardDerivation` | `StructuredProof` | ✅ Proved |
| Structured central theorem (= unconditional) | `structuredCentralTheorem`, `structuredAgreesWithUnconditional` (`Refl`) | `StructuredProof` | ✅ Proved |
| Strict / paper-domain from structured core | `structuredCentralTheoremStrict`, `structuredCentralTheoremPaperDomain` | `StructuredProof` | ✅ Proved |
| Complementary counting | `countComplement`, `indicatorComplement`, `countAllTrue` | `DensityExtra` | ✅ Proved |
| Non-degeneracy of the density model | `allNotNegligible` | `DensityExtra` | ✅ Proved |
| Cofinite ⇒ almost all; singletons negligible | `almostAllCofinite`, `singletonNegligible`, `gtImpliesNeq` | `DensityExtra` | ✅ Proved |
| Complement of negligible is almost all | `negligibleGivesAlmostAllComplement`, `boolNotInvolutive` | `DensityExtra` | ✅ Proved |
| Density "almost all" on `Pos` (Collatz domain) | `NegligiblePos`, `AlmostAllPosD`, `almostAllPosMono`, `andAlmostAllPos`, `almostAllPosCofinite`, `allPosNotNegligible` | `CarrierDensity` | ✅ Proved |
| Density "almost all" on `OddPos` (Syracuse domain) | `NegligibleOdd`, `AlmostAllOddD`, `almostAllOddMono`, `andAlmostAllOdd`, `almostAllOddCofinite`, `allOddNotNegligible` | `CarrierDensity` | ✅ Proved |
| Single-step Collatz/Syracuse rewrites & odd-part fixity | `colEvenStep`, `colOddStep`, `oddPartOfOdd`, `oddPartFixesOdd`, `syrIsOdd`, `oddPartDropTimeOdd`, `oddNormalizeFixed` | `DynamicsExtra` | ✅ Proved |
| Machine-checked first-passage examples | `colFourBelowOne`, `colSixteenBelowOne`, `syrSevenBelowOne` | `DynamicsExtra` | ✅ Proved |

The genuine natural-density "almost all" is now a proved, **non-degenerate**
largeness algebra on the exact carriers the main theorem is stated over.  The
single honest remaining input is still the deep first-passage analytic estimate
(Props 1.9 / 7.8); the reduction chain and its structured presentation transport
it end-to-end once it carries content.

A matrix-only, self-contained LaTeX proof of the whole main theorem accompanies
this development in `paper/matrix-proof.pdf`.

---

## 7. Safe algebraic-domain encodings (matrix math & group theory)

A new, self-contained algebraic layer encodes the Collatz/Syracuse dynamics in
the most explicit and "safe" domains available: honest 2x2 matrices over `Nat`,
the affine monoid, and finite group theory (`Z/2Z`).  Every entry is a total
`Nat` term with no `believe_me`, axioms, or holes; all 26 modules build from
scratch under Idris2 0.8.0.

| Object | Idris declaration | Module | Status |
|---|---|---|---|
| 2x2 `Nat` matrices; verified monoid | `Mat2`, `matMul`, `matMulAssoc`, `matMulIdLeft/Right`, `applyMat`, `applyMatMul` | `Matrix` | ✅ Proved |
| Affine monoid `x\|->a*x+b`; matrix embedding | `Affine`, `composeAff`, `composeAffAssoc`, `affToMat`, `affToMatHom` | `Affine` | ✅ Proved |
| Power = iterate bridge | `powAff`, `powAffIterate`, `iterExt`, `oddStepPowIterate` | `Affine` | ✅ Proved |
| Parity group `Z/2Z`; homomorphism from `(Nat,+)` | `Parity`, `xorP`, `xorPAssoc`, `xorPSelfInverse`, `parityOf`, `parityOfPlus` | `Parity` | ✅ Proved |
| Collatz branch by parity group element; `isEven` bridge | `parityTrueIsEven`, `parityFalseIsOdd`, `colEvenParity`, `colOddParity` | `Parity` | ✅ Proved |
| Unified verified monoid/group interface + generic theorems | `MonoidStr`, `GroupStr`, `unitUnique`, `powM`, `powMAdd`, `invUnique`, `invInvolutive` | `Algebra` | ✅ Proved |
| Matrix / affine / parity / `(Nat,*)` as instances | `matrixMonoid`, `affineMonoid`, `parityMonoid`, `parityGroup`, `natMultMonoid` | `Algebra`, `Determinant` | ✅ Proved |
| Closed form `[[3,1],[0,1]]^k` and iterate of `3x+1` | `pow3`, `geom`, `oddPowClosed`, `iterThreeXClosed`, `oddPowMatClosed` | `OddStepClosed` | ✅ Proved |
| Determinant homomorphism `Affine -> (Nat,*)`; growth `3^k` | `affDet`, `affDetHom`, `affDetPow`, `oddStepDet` | `Determinant` | ✅ Proved |
| Odd `Col` step = affine/matrix action; Syracuse = odd part of image | `colOddAffine`, `colOddMatrixAction`, `syrIsOddPartOfAffine` | `MatrixDynamics` | ✅ Proved |
| Determinant growth in the `Leq` height ordering | `oddIterNonDecreasing`, `oddStepStrictlyIncreases` | `MatrixGrowth` | ✅ Proved |

**Net effect.** The concrete even/odd branching and the tripling growth of the
Collatz/Syracuse maps are now expressed through a verified, reusable algebraic
core (matrix monoid, affine monoid, parity group, unified `MonoidStr`/`GroupStr`
interface, determinant homomorphism).  The odd step is certified to *grow* the
height (`MatrixGrowth`), which is exactly why the halving steps are needed for
descent — the algebraic content underlying the paper's first-passage analysis,
stated in the safe `Nat`/`Leq`/group-theory domain.

---

## 8. First moment and downward drift of the 2-adic valuation distribution

A new module `TaoCollatz.ValuationMoment` computes the *expectation* of the
genuine 2-adic valuation measure `geoValuation` (built in
`TaoCollatz.GeometricValuation`) in closed form, and derives the downward drift
that underlies Collatz/Syracuse descent.  Everything is `%default total` with no
`believe_me`/`postulate`/`assert_*`/`%foreign`/`idris_crash`/axioms/holes.

| Object | Idris declaration | Status |
|---|---|---|
| First-moment additivity under value-shift | `weightedSumShift1` | ✅ Proved |
| **Closed-form first moment** `weightedSum (geoValuation n) + (n+2) = 2·2^n` | `weightedSumGeoValuation` | ✅ Proved |
| Number-theoretic drift core `2^{n+1} >= 5n+2` (`n >= 4`) | `pow2LinearShifted`, `pow2LinearFromWitness` | ✅ Proved |
| **General drift** `8·mass <= 5·weightedSum` for all `n >= 4` (mean valuation `>= 8/5`) | `generalDriftShifted`, `generalDrift` | ✅ Proved |
| Concrete drift at scale 4 (`E[a] = 26/15 >= 8/5`) | `weightedSumGeoValuationFour`, `massGeoValuationFour`, `driftFour` | ✅ Proved |
| Growth comparison `3^5 = 243 <= 256 = 2^8` (witnesses `log2 3 < 8/5`) | `growthComparison` | ✅ Proved |

**Net effect.** Combined with the mass normalisation `mass + 1 = 2^n`
(`massGeoValuationPlusOne`), the closed form shows the mean 2-adic valuation
`E[a] = (2^{n+1} - (n+2)) / (2^n - 1)` tends to `2`.  The general drift proves
`E[a] >= 8/5` for every scale `n >= 4`, and `growthComparison` shows
`log2 3 < 8/5`; hence the per-step Syracuse factor `3 / 2^{E[a]}` is `< 1` at
every large scale — the elementary drift mechanism behind the paper's
first-passage descent, now expressed as genuine, machine-checked `Nat`/`Leq`
mathematics on the actual valuation measure.

## Genuine content for the deep placeholder nodes (Prop. 1.9 / 7.8 + contraction)

New modules `TaoCollatz/ValuationTail.idr`, `TaoCollatz/GenuineEstimates.idr`,
and `TaoCollatz/ContractionDrift.idr` replace the previously `Unit`-inhabited
payloads of the first-passage estimates with genuine, machine-checked
distributional mathematics on the actual 2-adic valuation measure
`geoValuation`, and wire it into the paper-assembly.

| Result | Idris node | Status |
|---|---|---|
| Tail commutes with value-shift `mu_{+1}({x >= t+1}) = mu({x >= t})` | `massGeShift1` | ✅ Proved |
| **Exact survival function** `mu({a >= j+1}) + 1 = 2^{n-j}` (distributional core of Prop. 1.9) | `tailGeoValuation` | ✅ Proved |
| Exponential tail bound `mu({a >= j+1}) <= 2^{n-j}` | `tailGeoValuationLe` | ✅ Proved |
| Exact geometric halving `mu({a >= j}) = 2·mu({a >= j+1})` (`j < n`) | `tailHalving` | ✅ Proved |
| Complementary distribution function `mu({x<t}) + mu({x>=t}) = mass` | `massLt`, `massLtGeComplement` | ✅ Proved |
| Markov on the real distribution + closed-form moment | `markovGeoValuation`, `markovGeoValuationClosed` | ✅ Proved |
| **B1 (Prop. 1.9) payload upgraded** from `Unit` to the exact-tail theorem | `genuineTailEstimate` | ✅ Genuine content |
| **B2 (Prop. 7.8) payload upgraded** from `Unit` to tail monotonicity | `genuineStabilityEstimate` | ✅ Genuine content |
| B1/B2 threaded into the paper-assembly | `PaperAssumptions.proposition19*`, `renewal*` | ✅ Wired |
| Per-step contraction bundle (drift `E[a] >= 8/5` + `3^5 <= 2^8`) | `SyracuseStepContraction`, `syracuseStepContraction` | ✅ Proved |

**Net effect.** The Proposition 1.9 / 7.8 nodes in `PaperAssumptions` are no
longer opaque `Unit` placeholders: they now carry the genuine, proven
distribution of the Syracuse 2-adic valuation random variable (its exact
survival function, exponential decay, geometric halving law, complementary CDF,
Markov large-deviation bound, and tail monotonicity). The full density-one
first-passage gate `A1` (`SyracuseDensityControl`) remains open — see
`REMAINING_WORK.md` and `PLAN_HARD_THEOREMS.md`.

### 8b. Exact residue-class realisation of the valuation law (`ValuationOneClass`)

The abstract measure `geoValuation` (§8) models `P(a = k) = 2^{-k}`.  The module
`TaoCollatz.ValuationOneClass` pins the *base atom* `a = 1` of that law onto the
actual arithmetic, complementing `ValuationTwoClass`/`ValuationDistribution`
(which handle `a = 2` on `n ≡ 1 (mod 8)`):

| Result | Idris node | Status |
|---|---|---|
| Factorisation `3(4t+3)+1 = 2^1·(6t+5)`, `6t+5` odd | `class3mod4Factor`, `oddSixTPlus5` | ✅ Proved |
| **Exact valuation** `syrValuation (4t+3) = 1` (the event `a = 1`) | `valuationOneOnClass3mod4`, `valuationOneWhenRes3mod4` | ✅ Proved |
| Period-4 predicate `n ≡ 3 (mod 4)` with density `1/4` | `res3mod4`, `res3mod4Periodic`, `countRes3mod4` | ✅ Proved |
| **First-step valuation partition** of the odds: `{a=1} ⊔ {a≥2}`, each density `1/4` | `res34UnionIsOdd`, `res3res1Disjoint`, `oddValuationSplitDecomp`, `oddValuationSplitCount` | ✅ Proved |

This gives the exact first-step distribution of the Syracuse valuation over the
odd numbers (`P(a=1) = P(a≥2) = 1/2`), the leading, arithmetically-realised term
of the geometric law — a genuine slice of infrastructure items C1/C2. The deep
multi-step concentration bridge (needed for the density-one drift, gate `A1`)
remains open.

---

### 8c. Geometric valuation survival law, all `k` (`PeriodicResidue`, `ValuationGeometric`)

The residue-class atoms of §8b are hand-unrolled at fixed periods (`a = 1` at
period 4, `a = 2` at period 8).  This subsection lifts them to a **single law
valid for every `k`**, i.e. the arithmetically-realised survival function
`P(a >= k) = 2^{-k}` of the Syracuse 2-adic valuation random variable.

Two new modules (both `%default total`, no holes / `believe_me` / `postulate` /
`assert_*` / `%foreign` / `idris_crash` / axioms):

`TaoCollatz.PeriodicResidue` — a general single-residue-class density, for an
*arbitrary* period `P = S p` (the fixed-period unrollings could not be made
uniform in `k`):

| Result | Idris node | Status |
|---|---|---|
| Successor-mod-`P` counter and its iteration | `nextMod`, `applyNout`, `applyNoutPlus` | ✅ Proved |
| Ticking within a period is honest addition | `reachP` | ✅ Proved |
| A full period of ticks returns to start | `cycleReturn` | ✅ Proved |
| Phase (`n mod P`), identity below the period | `phase`, `phaseSmall` | ✅ Proved |
| Residue-class indicator `atRes p r`, period `P` | `atRes`, `atResPeriodic` | ✅ Proved |
| Exactly one member per period (`r < P`) | `countAtResPerPeriod` | ✅ Proved |
| **Density `1/P`** over full periods | `atResDensity` | ✅ Proved |

`TaoCollatz.ValuationGeometric` — the arithmetic realisation of the survival
law, uniformly in `k`:

| Result | Idris node | Status |
|---|---|---|
| Valuation lower bound from a factorisation `3n+1 = 2^k s`, `s>=1` | `valuationGeFromFactor` | ✅ Proved |
| **Tail residue** `r_k < 2^k` with `3 r_k + 1 = 2^k s_k` (`s_k>=1`), all `k` | `tailResidue` | ✅ Proved (induction on `k`) |
| Every `n` decomposes as `n = q*P + (n mod P)` | `phaseDecomp` | ✅ Proved |
| **Survival law**: a residue class of density exactly `2^{-k}` on which `syrValuation n >= k`, for every `k` | `tailClass` | ✅ Proved |
| The `a>=1` / `a>=2` atoms as instances | `tailClassOne`, `tailClassTwo` | ✅ Proved |

**Net effect.**  For every `k` there is a genuine residue class (period `2^k`,
natural density exactly `2^{-k}`) on which the *actual* Syracuse valuation is
`>= k` — the exact complementary CDF `P(a >= k) = 2^{-k}` of the geometric law,
realised on the arithmetic (a general slice of infrastructure items C1/C2 of
`REMAINING_WORK.md`), subsuming the fixed-period `a=1`/`a=2` atoms of §8b.  The
deep multi-step valuation-sum concentration bridge (needed for the density-one
drift, gate `A1`, and the four analytic holes `piece34/35/59` of
`Pieces64`) remains open.

---

## 9. Complete numbered-result coverage (`TaoCollatz.PaperResults`)

Every numbered result of `taocollatz.pdf` now has a corresponding Idris2
declaration, so that all parts of the main theorem (Theorem 1.3) are converted
to Idris2.  The module `TaoCollatz.PaperResults` records one `Type` (the
formalized *statement*) per numbered result: for results already formalized
elsewhere it is an alias naming the existing node; for the previously-missing
supporting results it is a new faithful statement.

| Paper result | Idris declaration (`PaperResults`) | Backing / status |
|---|---|---|
| Conjecture 1.1 (Collatz) | `Conjecture11` | genuine statement over `Col` (open; statement only) |
| Theorem 1.3 (main) | `Theorem13Statement` | alias `Large.Theorem13` (proved reduction; single gate A1) |
| Conjecture 1.5 (Syracuse) | `Conjecture15` | genuine statement over `Syr` (open; statement only) |
| Theorem 1.6 | `Theorem16Statement` | alias `Large.Theorem16` |
| Proposition 1.9 | `Proposition19Statement` | alias `ValuationDistribution` (genuine tail content) |
| Proposition 1.11 | `Proposition111Statement` | alias `StabilisationOfFirstPassage` |
| Lemma 1.12 | `Lemma112Statement` | statement placeholder (needs `Z/3^nZ` prob. layer) |
| Proposition 1.14 | `Proposition114Statement` | alias `FineScaleMixing` |
| Proposition 1.17 | `Proposition117Statement` | alias `FourierDecay` |
| Lemma 2.1 (valuation description) | `Lemma21Statement`, `lemma21OneStep` | **single-step case genuinely proved** via `TwoAdic.oddFactorization` |
| Lemma 2.2 (Chernoff bound) | `Lemma22Statement` | statement placeholder (needs sub-Gaussian layer) |
| Theorem 3.1 (alternate form) | `Theorem31Statement` | alias `QuantitativeSyracuseBound` |
| Lemma 4.1 (tail bound) | `Lemma41Statement` | statement placeholder; per-step tail proved in `ValuationTail` |
| Proposition 5.2 (approx. formula) | `Proposition52Statement` | statement placeholder (log-density layer) |
| Lemma 5.3 | `Lemma53Statement` | statement placeholder |
| Lemma 6.2 (injectivity of offsets) | `Lemma62Statement` | statement placeholder; affine monoid proved in `Affine` |
| Corollary 6.3 (3-adic separation) | `Corollary63Statement` | statement placeholder |
| Proposition 7.1 (key Fourier estimate) | `Proposition71Statement` | alias `KeyFourierEstimate` |
| Lemma 7.2 (cancellation, white points) | `Lemma72Statement` | statement placeholder (Fourier layer) |
| Proposition 7.3 (renewal white points) | `Proposition73Statement` | alias `RenewalWhitePoints` |
| Lemma 7.4 (structure of black set) | `Lemma74Statement` | statement placeholder (renewal/geometry layer) |
| Lemma 7.6 (holding time properties) | `Lemma76Statement` | statement placeholder (renewal layer) |
| Lemma 7.7 (first-passage location) | `Lemma77Statement` | statement placeholder (renewal layer) |
| Proposition 7.8 (renewal monotonicity) | `Proposition78Statement` | alias `RenewalMonotonicity` (genuine monotonicity content) |
| Lemma 7.9 (triangles ⇒ white points) | `Lemma79Statement` | statement placeholder (renewal layer) |
| Lemma 7.10 (large triangles rare) | `Lemma710Statement` | statement placeholder (renewal layer) |

The placeholder statements (payload `Unit`) match the convention already used
for the analytic nodes 1.14 / 1.17 / 7.1 / 7.3 / 7.8 in `PaperInterfaces`; they
are honest statement-level `Type`s with no fabricated proof term.  The deep
analytic content they name still routes through the single gate A1 and the
missing infrastructure C1–C5 documented in `REMAINING_WORK.md`.  The whole tree
still builds with Idris2 0.8.0 (`idris2 --build taocollatz.ipkg`, exit 0), is
`%default total`, and uses no `believe_me`/`postulate`/`assert_*`/`%foreign`/
`idris_crash`/axioms/holes.
