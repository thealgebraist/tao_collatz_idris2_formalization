# Progress: valuation distribution & positive-density descent (8 more iterations)

This round adds eight further fully-proved Idris2 modules (`%default total`, no
`believe_me` / `postulate` / `assert_*` / `%foreign` / `idris_crash` / holes /
axioms) advancing the elementary, checked infrastructure toward the single
remaining analytic gate `SyracuseDensityControl` (see `REMAINING_WORK.md`). The
whole package (`idris2 --build taocollatz.ipkg`, 42 modules) builds from scratch.

Honest scope note (unchanged): a *fully unconditional* proof of Tao's Theorem
1.3 still requires the deep analytic argument (2-adic measure theory, tail
bounds, Fourier decay, renewal theory). Nothing here fakes that. What follows is
real, checked mathematics supplying concrete pieces the gate rests on: the
*exact* Syracuse valuation on residue classes (the geometric-distribution data),
the additivity/positivity of natural density on those classes, and iterated
descent.

## New modules

1. **`TaoCollatz.DropTimeExact`** — *exact* small values of the 2-adic drop
   time: `oddPartDropTime x = 0` for odd `x`; `= 1` when `2 || x`; `= 2` when
   `4 || x` (proved for the fuelled recursor, so fuel-independent).
2. **`TaoCollatz.ValuationTwoClass`** — the residue class `n ≡ 1 (mod 8)` has
   Syracuse valuation *exactly two*: `3(8t+1)+1 = 4(6t+1)` with `6t+1` odd, so
   `syrValuation (8t+1) = 2`.
3. **`TaoCollatz.PositiveDensity`** — a periodic predicate with `>= 1` hit per
   period is **not** negligible (positive natural density); instantiated to show
   the good-step class `n ≡ 1 (mod 4)` has positive density.
4. **`TaoCollatz.DisjointDensity`** — exact additivity of counting for disjoint
   predicates: `count (p||q) N = count p N + count q N`.
5. **`TaoCollatz.ResidueClasses`** — the good-step class splits mod 8 into the
   disjoint period-8 classes `1 (mod 8)` and `5 (mod 8)`, whose union is exactly
   `res1mod4`; hence the exact density identity `1/4 = 1/8 + 1/8`.
6. **`TaoCollatz.IteratedDescent`** — the iteration-shift lemma
   `iter (S k) f x = f (iter k f x)` and iterated non-increase: if every
   Syracuse step of an orbit is non-increasing, no iterate exceeds the start;
   concrete bounded orbit of the fixed point `1`.
7. **`TaoCollatz.ValuationDistribution`** — bridges the residue *predicate* to
   the *exact* valuation: `res1mod8 n = True ==> syrValuation n = 2`, giving a
   density-`1/8` set on which the valuation is exactly two.
8. **`TaoCollatz.DescentSetPositive`** — capstone: `PositiveDensityDescentSet`,
   a positive-density set of odd starts each with a genuine one-step
   first-passage witness, realised by the good-step class `n ≡ 1 (mod 4)`.

## What this buys, honestly

Together with the previous round this gives a rigorous, checked account of the
*elementary* first-passage story with real density content: the exact 2-adic
valuation on prescribed residue classes (the first values `1, 2` of the
geometric Syracuse-valuation distribution), the additivity and *positivity* of
natural density on those classes (the descent set is provably not density zero),
the finer mod-8 decomposition with the exact `1/4 = 1/8 + 1/8` identity, and
iterated orbit descent. The remaining gap to `SyracuseDensityControl` is the
genuinely hard analytic step: upgrading these positive-density "good step"
statements to density-**one** first passage below an arbitrary threshold.
