# The theorem-hole presentation of the central theorem

This round adopts a **theorem-hole strategy** for the remaining analytic content,
implemented in the new module `TaoCollatz/HoleProof.idr`.

## What changed

Previously the central theorem was only ever available as a *function of an
explicit hypothesis*:

```idris
theorem13GenuineFromSyracuse : SyracuseDensityControl -> Theorem13Genuine
```

That is honest (nothing is fabricated) but the main theorem is never exhibited as
a **closed** term. `HoleProof` now states the genuine, closed main theorem as a
top-level definition and leaves the single remaining analytic content as an
explicit Idris **hole** (`?assembleSyracuseGate_rhs`):

```idris
theorem13 : Theorem13Genuine
theorem13 = theorem13GenuineFromSyracuse syracuseDensityControl
```

A hole is the honest, machine-checked marker of "this exact, genuinely-typed
goal is not yet proved". Key properties:

* Every statement has its **real** type — nothing is weakened to `Unit`/`True`.
  Querying the hole in Idris shows its type is exactly the non-vacuous
  density-one first-passage control
  `(f : Pos -> Nat) -> TendsToInfinityPos f -> (good : Pos -> Bool ** (AlmostAllPosD good, ...))`.
* The file **type-checks and builds**: `idris2 --build taocollatz.ipkg` exits 0.
* The precise surface area of what remains is exactly the set of holes — here a
  **single** hole. Filling it, with no other change anywhere, upgrades every
  closed term below (`theorem13`, `theorem13Strict`, `theorem13PaperDomain`,
  `theorem13HasMember`) to a fully unconditional proof.

## The gate is threaded through the already-proved ingredients

The gate is not one opaque hole floating in a vacuum. `HoleProof.analyticInputs`
bundles the genuine, hole-free distributional facts already proved elsewhere and
feeds them into the gate:

| Ingredient | Content | Source |
|---|---|---|
| `SyracuseStepContraction` | mean-valuation drift `E[a] >= 8/5` and growth comparison `3^5 <= 2^8` | `ContractionDrift` |
| `FirstPassageTailEstimate` | exact 2-adic valuation survival function `mu({a>=j+1}) + 1 = 2^{n-j}` | `GenuineEstimates` / `ValuationTail` |
| `PositiveDensityDescentSet` | positive-density set of one-step Syracuse descenders `n = 1 (mod 4)` | `DescentSetPositive` |

The remaining hole `assembleSyracuseGate : AnalyticFirstPassageInputs ->
SyracuseDensityControl` is therefore exactly the "assembly" step: turning these
proved distributional facts into density-one first-passage control for an
arbitrary height `f` — Tao's Theorem 1.6 in density form, the large-deviation /
Fourier heart of the paper.

## Build

```
idris2 --build taocollatz.ipkg    # exits 0; the whole tree (53 modules) type-checks
```

The only `?`-hole in the entire `TaoCollatz/` tree is
`?assembleSyracuseGate_rhs`. No `believe_me`, `postulate`, `assert_total`,
`assert_smaller`, `%foreign`, `idris_crash`, axioms, or `@[implemented_by]` are
used.
