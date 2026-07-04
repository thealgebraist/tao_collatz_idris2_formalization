# Progress: genuine descent / density infrastructure (8 iterations)

This round added eight new, fully-proved Idris2 modules (`%default total`, no
`believe_me` / `postulate` / `assert_*` / `%foreign` / holes / axioms) building
genuine mathematical infrastructure toward the single remaining analytic gate
`SyracuseDensityControl` (see `REMAINING_WORK.md`). The whole package
(`idris2 --build taocollatz.ipkg`) builds from scratch.

Honest scope note: a *fully unconditional* proof of Tao's Theorem 1.3 requires
formalising the deep analytic argument of the paper (2-adic measure theory,
sub-Gaussian tail bounds, discrete Fourier decay, renewal theory). That is a
research-scale effort and is **not** completed here, and nothing below fakes it:
the gate genuinely requires a *natural-density-one* set, so it cannot be
inhabited trivially. What follows is real, checked mathematics that supplies
concrete pieces of the infrastructure that gate rests on.

## New modules

1. **`TaoCollatz.TwoAdic`** — the 2-adic factorisation
   `n = oddFactor n * 2 ^ (oddPartDropTime n)` for every `n`, and that
   `oddFactor n` is genuinely odd for `n >= 1`. (Infrastructure C2.)
2. **`TaoCollatz.SyracuseStructure`** — the Syracuse map produces odd values;
   the exact step factorisation `3n+1 = Syr(n) * 2 ^ (syrValuation n)`, defining
   the per-step valuation random variable. (C2.)
3. **`TaoCollatz.PeriodicCount`** — the counting toolkit: extensionality
   (`countExt`), additivity over a split range (`countPlus`), and the exact
   count of a period-`m` predicate over full periods
   `count p (q*m) = q * count p m`. (C1.)
4. **`TaoCollatz.SyracuseDescent`** — the descent lemma: if the valuation of
   `3n+1` is at least two (`2^v >= 4`) then `Syr(n) <= n`; with the quantitative
   `4 * Syr(n) <= 3n+1` and a factor-of-four cancellation lemma.
5. **`TaoCollatz.ValuationBounds`** — parity algebra (`isEven` of sums, of `3n`)
   and the valuation lower bound: `syrValuation n >= 1` for odd `n`. (C2.)
6. **`TaoCollatz.FirstPassageDescent`** — bridges descent to the gate's own
   first-passage predicate: a good step yields a genuine `SyrBelow` witness.
7. **`TaoCollatz.GoodStep`** — the good-step characterisation: `4 | (3n+1)`
   (i.e. `3n+1` even with even half) forces the drop time `>= 2`, hence
   `2^v >= 4`, hence descent `Syr(n) <= n`.
8. **`TaoCollatz.GoodStepDensity`** — the good-step residue class `n ≡ 1 (mod 4)`
   has natural density exactly `1/4` (`count over q periods = q`, via
   `PeriodicCount`); and the explicit infinite family `n = 4t+1` are all
   good-step starts (`3(4t+1)+1 = 4(3t+1)`), each with a `SyrBelow` witness.

## What this buys, honestly

Together these give a rigorous, checked account of the *elementary* half of the
first-passage story: exactly which Syracuse steps descend (valuation `>= 2`), the
2-adic factorisation behind the valuation, the periodic-density toolkit for
residue classes, and a genuine density-`1/4` set of odd starts on which a single
step provably drops. The remaining gap to `SyracuseDensityControl` is the
genuinely hard analytic step: upgrading such positive-density "one good step"
statements to density-**one** first passage below an arbitrary `f -> infinity`
(the content of Tao's Propositions 1.9 / 7.8 and the Fourier/renewal analysis).
