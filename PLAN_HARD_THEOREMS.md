# 16-Step Plan: Adding Proofs for the Hard Last Theorems

This plan attacks the remaining *content* nodes catalogued in `REMAINING_WORK.md`
— the deep analytic estimates B1–B6, the single gate A1
(`SyracuseDensityControl`), and the "almost all" resolution D1 — by replacing the
opaque `Unit`-inhabited placeholder payloads with **genuine, machine-checked
mathematics** on the finitely-supported measure carrier `FinDist`.

The strategy is bottom-up: build the distributional core of the valuation
random variable (the actual object of Prop. 1.9 / 7.8), give the placeholder
payloads real teeth, and thread the genuine estimates into the paper-assembly
(`PaperAssumptions`). Everything must remain `%default total` with no
`believe_me`/`postulate`/`assert_*`/`%foreign`/`idris_crash`/axioms/holes, and
`idris2 --build taocollatz.ipkg` must stay green after every step.

Honesty note: fully discharging A1 is Tao's theorem itself and is not claimed
here. What this plan delivers is the *genuine distributional content* underneath
B1/B2 (exact geometric tail, its exponential decay, monotone/renewal
structure), upgrading those nodes from vacuous `Unit` payloads to real proven
propositions, plus the plumbing that consumes them.

## Steps

1. **Toolchain + baseline.** Build Idris2 0.8.0 from source (Chez backend),
   confirm `idris2 --build taocollatz.ipkg` is green as a baseline. *(done)*

2. **Shift lemma.** Prove `massGeShift1 : massGe (S t) (shift1 d) = massGe t d`
   — the tail commutes with the value shift used to build `geoValuation`.

3. **Exact geometric tail (core of Prop. 1.9).** Prove
   `tailGeoValuation : plus (massGe (S j) (geoValuation n)) 1 = pow2 (minus n j)`,
   i.e. `mu({a >= j+1}) = 2^{n-j} - 1`. This is the exact CDF/tail of the
   2-adic valuation distribution.

4. **Exponential tail bound.** Derive
   `tailGeoValuationLe : Leq (massGe (S j) (geoValuation n)) (pow2 (minus n j))`,
   the sub-exponential decay `mu({a >= j+1}) <= 2^{n-j}` (item C3).

5. **Geometric halving / decay ratio.** Prove that consecutive tails halve:
   `plus (massGe (S j) (geoValuation n)) 1 = mult 2 (plus (massGe (S (S j)) (geoValuation n)) 1)`
   under `Leq (S j) n` — the exact geometric decay law `P(a>=j) = 2 P(a>=j+1)`.

6. **CDF complement.** Express the lower part
   `mass (geoValuation n) = plus (massGe (S j) ...) (massLt ...)` so the tail and
   the distribution function are genuinely complementary (distribution layer C1).

7. **Markov instance on the real distribution.** Specialise `TailBound.markov`
   plus the closed-form first moment (`ValuationMoment.weightedSumGeoValuation`)
   to `geoValuation`, giving a genuine numeric large-deviation bound
   `mult t (massGe t (geoValuation n)) <= weightedSum (geoValuation n)`.

8. **Package B1 payload.** Build `genuineTailEstimate : FirstPassageTailEstimate`
   whose `tailEstimatePayload` is the *genuine* exact-tail proposition of step 3
   (not `Unit`), with `tailEstimateEvidence` the real proof.

9. **Package B2 payload.** Build
   `genuineStabilityEstimate : FirstPassageStabilityEstimate` whose payload is the
   genuine tail-monotonicity (`massGeMonoThreshold` on `geoValuation`) — the
   structural renewal/stability content of Prop. 7.8.

10. **Wire B1/B2 into `PaperAssumptions`.** Replace `trivialTailEstimate` /
    `trivialStabilityEstimate` (payload `Unit`) with the genuine estimates from
    steps 8–9, so `proposition19Dual` and `renewalMonotonicityDual` carry real
    content, keeping the whole tree green.

11. **Genuine `ValuationDistribution`.** Confirm the `MkValuationDistribution`
    built from the genuine tail estimate is non-vacuous, and add a corollary
    extracting the exact tail back out of a `ValuationDistribution` value.

12. **Mean-drift → contraction, quantitative.** Combine
    `ValuationMoment.generalDrift` (`E[a] >= 8/5`) with
    `growthComparison` (`3^5 <= 2^8`) into a single packaged statement that the
    per-step Syracuse factor is `< 1` at every scale `n >= 4`.

13. **Second-moment / concentration seed.** Add the second moment
    `weightedSumSq (geoValuation n)` (or the variance surrogate) and prove its
    closed form, seeding the sub-Gaussian toolkit C3 needed for B1's tail beyond
    Markov.

14. **Density-transfer skeleton for A1.** State, as an explicit honest
    hypothesis record, the *reduction* from the genuine valuation tail +
    monotonicity to `SyracuseDensityControl`, and prove every structural step
    that does **not** require the analytic input, isolating the true remaining
    gap as small as possible.

15. **D1 logarithmic-density upgrade (partial).** Introduce a genuine
    logarithmic-density notion and prove the closure/monotonicity algebra for it,
    replacing the fixed-0 error placeholder where the surrounding lemmas allow.

16. **Integrate, document, verify.** Add the new module(s) to `taocollatz.ipkg`,
    run a clean `idris2 --build`, grep for banned constructs, and update
    `TRACKING.md` / `REMAINING_WORK.md` to reflect which nodes now carry genuine
    content and what precisely remains.
