# Generalizations that subsume large chunks of the elementary lemmas

This round looked for *general* lemmas that collapse many of the bespoke,
special-case proofs in the descent / valuation / density infrastructure into a
single reusable statement. Two general facts do most of the work; the previous
special cases become one-line instances, and every higher case (all valuations
`k`, all residue classes / periods `m`) comes for free.

Everything below is `%default total`, with **no** `believe_me` / `postulate` /
`assert_*` / `%foreign` / `idris_crash` / axioms / holes. The whole package
(`idris2 --build taocollatz.ipkg`, 48 modules) builds from scratch.

## 1. The exact 2-adic valuation (`TaoCollatz.ValuationExact`)

The single generalization

```idris
dropTimePowOdd : (k : Nat) -> (m : Nat) -> isEven m = False ->
                 oddPartDropTime (mult (pow2 k) m) = k
```

says the 2-adic valuation of `2^k * m` is exactly `k` for every `k` and every
**odd** `m`. It is proved once by a peeling induction on `k`. From it:

| Was proved bespoke | Now a one-line instance |
|---|---|
| `DropTimeExact.dropTimeZeroOfOdd` (`= 0`) | `dropTimeZeroGen` |
| `DropTimeExact.dropTimeExactlyOne` (`= 1`) | `dropTimeOneGen` |
| `DropTimeExact.dropTimeExactlyTwo` (`= 2`) | `dropTimeTwoGen` |
| every higher exact valuation `= 3, 4, ...` | free |

A companion **lower bound** with an arbitrary (not necessarily odd) cofactor,

```idris
dropTimePowGe : (k : Nat) -> (s : Nat) -> Leq (S Z) s ->
                Leq k (oddPartDropTime (mult (pow2 k) s))
```

subsumes the good-step valuation bounds (`GoodStep.dropTimeGeTwo`, etc.).

### Consequences for the Syracuse valuation and descent

* `syrValuationFromFactor` — read the exact Syracuse valuation off *any* 2-adic
  factorisation `3n+1 = 2^k * q` (`q` odd). This gobbles up the residue-class
  valuation computations: e.g. `ValuationTwoClass.valuationTwoOnClass1mod8` is
  now just this lemma applied to `3(8t+1)+1 = 2^2 * (6t+1)` (its earlier
  half/half chase and `dropTimeExactlyTwo` case split are gone).
* `descendsFromValuationGeTwo`, `descendsFromFactorGeTwo`,
  `descendsFromFactorPow2` — a single descent criterion: any `n` with
  `4 | (3n+1)` (equivalently valuation `>= 2`, or `3n+1 = 2^k * s` with `k >= 2`,
  `s >= 1`) satisfies `Syr(n) <= n`. Every descending-family lemma is an
  instance; e.g. `GoodStepDensity.familyDescends` (the class `n = 4t+1`) is now
  a one-liner via `descendsFromFactorPow2` instead of a bespoke parity/half
  argument.

## 2. General single-residue density (`TaoCollatz.PeriodicCount`)

```idris
singleHitDensity : (p : Nat -> Bool) -> (m : Nat) ->
  ((n : Nat) -> p (plus n m) = p n) ->   -- p has period m
  count p m = 1 ->                        -- exactly one member per period
  (q : Nat) -> count p (mult q m) = q     -- density 1/m
```

"A single residue class mod `m` has natural density `1/m`." Each concrete
residue-class density is now this lemma applied to a period and a one-line
per-period certificate:

| Was proved bespoke | Now a one-line instance |
|---|---|
| `GoodStepDensity.countGoodResidues` (`1 mod 4`, density `1/4`) | `singleHitDensity ... 4 ...` |
| `ResidueClasses.countRes1mod8` (`1 mod 8`, density `1/8`) | `singleHitDensity ... 8 ...` |
| `ResidueClasses.countRes5mod8` (`5 mod 8`, density `1/8`) | `singleHitDensity ... 8 ...` |

## Net effect

The elementary valuation ladder, the residue-class valuations, the good-step
descent family, and the residue-class densities — previously a spread of
separate, computation-heavy lemmas — are now consequences of **two** general
theorems (`dropTimePowOdd` + its lower-bound sibling, and `singleHitDensity`).
New cases (any valuation `k`, any period `m`, any factorisation of `3n+1`) no
longer need bespoke proofs, which is exactly the leverage needed to scale the
elementary infrastructure toward the geometric valuation distribution.
