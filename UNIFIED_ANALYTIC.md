# A unified, minimal model of the paper's analytic domains

Fully unconditional closure of Tao's Theorem 1.3 requires the paper's
research-scale analytic machinery — 2-adic **measure theory**, **tail bounds**,
**Fourier / characteristic-function decay**, and **renewal theory**. In the
earlier development these four domains appeared only as opaque interface nodes
(payload `Type`, inhabited by `()`), so they carried no mathematics.

This round replaces that with a single, rigorous, *generalized minimal* theory:
all four domains are modelled as functionals on **one inductive algebraic
datatype**, and the facts that make each domain "work" are proved once, in
generality, on that carrier. Everything is `%default total`, with no
`believe_me` / `postulate` / `assert_*` / `%foreign` / `idris_crash` / axioms /
holes, and the whole package (47 modules) builds with
`idris2 --build taocollatz.ipkg`.

## The one carrier

```idris
data FinDist : Type where
  Empty : FinDist
  Atom  : (value : Nat) -> (weight : Nat) -> FinDist -> FinDist
```

`FinDist` is a finitely supported measure on `Nat` — a `Nat`-weighted multiset
of points. It is the constructive stand-in for a probability/measure space
(the 2-adic measure layer) and for the Syracuse valuation random variable.

## The four domains as functionals on that carrier

| Domain | Object | Module | Key proved law |
|---|---|---|---|
| Measure theory | `mass`, `weightedSum`, `dirac`, `scale`, `mix` | `FinMeasure` | additivity (`massMix`, `weightedSumMix`) and scaling (`massScale`, `weightedSumScale`) |
| Tail / large deviation | `massGe t` (upper tail `μ{x ≥ t}`) | `TailBound` | **Markov** `t · μ{x ≥ t} ≤ E[x]` (`markov`), tail monotonicity (`massGeMonoThreshold`), tail additivity (`massGeMix`) |
| Renewal theory | `convolve`, `convPow` (`n`-step kernel) | `Convolution` | mass multiplicativity (`massConvolve`) and the renewal power law (`massConvPow`) |
| Fourier / char. functions | `charFn χ` (transform against a character) | `Convolution` | **convolution theorem** `charFn χ (μ ⋆ ν) = charFn χ μ · charFn χ ν` (`charFnConvolve`) and its power form (`charFnConvPow`) |

The convolution theorem is the hinge: read with `χ v = z^v` it is the
generating-function identity behind renewal analysis; read with `χ` a root of
unity it is the finite-Fourier identity behind the paper's Fourier-decay
estimates. One proof, both domains.

## The unifying abstraction

`TaoCollatz.UnifiedAnalytic` collapses the four domains into a single record:

```idris
record FirstPassageModel where
  increment     : FinDist          -- the valuation-increment measure
  character     : Nat -> Nat       -- a multiplicative character
  characterHom  : ...              -- χ(a+b) = χ(a)·χ(b)
  characterUnit : character Z = S Z
```

From this data alone the four domain laws are generic theorems: `modelMass`
(measure), `modelTailBound` (tail/Markov), `modelRenewalMass` (renewal) and
`modelRenewalFourier` (Fourier).

## A concrete 2-adic instance

`TaoCollatz.GeometricValuation` builds `geoValuation K`, the genuine 2-adic
valuation measure (value `j` carries weight `2^{K-j}`, the count of residues of
valuation `j` mod `2^K`), and proves its exact geometric normalisation
`mass + 1 = 2^K` (`massGeoValuationPlusOne`). `valuationModel K` packages it as
a `FirstPassageModel` with the power-of-two character.

## Giving the paper's nodes genuine content

The opaque `Unit`/`()` payloads of the interface nodes are now inhabited with
real statements proved from the theory above:

* `genuineTailEstimate : FirstPassageTailEstimate` — payload = Markov's tail
  bound for the actual geometric 2-adic valuation measure (Prop. 1.9 node).
* `genuineValuationDistribution : ValuationDistribution` — Prop. 1.9 packaged
  with teeth.
* `genuineStabilityEstimate : FirstPassageStabilityEstimate` — payload = the
  renewal power law (Prop. 7.8 node).

These are drop-in genuine witnesses for the previously content-free placeholders,
demonstrating that the interface nodes are not vacuous and are met by real
mathematics from the unified theory.

## Scope

This is a rigorous *simplified model* of the four domains and a genuine
2-adic-valuation instance, not the full research-scale estimates that would
discharge the single remaining analytic gate `SyracuseDensityControl`. It
provides the reusable measure/tail/renewal/Fourier infrastructure (items
C1–C5 of `REMAINING_WORK.md`) on which such estimates would be built, with the
algebraic backbone (convolution theorem, Markov, renewal power laws) fully
machine-checked.
