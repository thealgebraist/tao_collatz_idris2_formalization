# The minimal proof DAG of the central theorem

This document records the **dependency DAG that actually constitutes the proof of
the central theorem** (`TaoCollatz.HoleProof.theorem13`, the genuine
natural-density form of Tao's Theorem 1.3), and the ongoing work of reducing it
to a set of **non-overlapping** lemmas (a minimal DAG: no lemma re-proves what
another already establishes).

It is generated from, and kept consistent with, the source tree
(`idris2 --build taocollatz.ipkg` builds all 53 modules; the closed main theorem
depends on exactly 31 of them).

## 1. The top-level spine

```
theorem13                         (HoleProof)          -- closed main theorem
  = theorem13GenuineFromSyracuse syracuseDensityControl (MinimalProof)
        |                                   |
        |                                   +-- syracuseDensityControl = assembleSyracuseGate analyticInputs
        |                                                                   |               |
        |                                                                   |               +-- analyticInputs  (hole-free ingredients)
        |                                                                   +-- step8 . step7 . ... . step1   (the 8-step gate)
        +-- colBelowFromSyrBelow  = simulationTransfersEventuallyBelow provenOddPartOrbitSimulation
                                                                          (OddPart / Core)
```

The reduction `SyracuseDensityControl -> Theorem13Genuine` is **fully proved**
(the odd-part orbit simulation transfers Syracuse first-passage to Collatz
first-passage). The only remaining content is the gate `assembleSyracuseGate`,
now split into eight steps (§3).

## 2. The module-level DAG (31 on-path modules, layered)

Each module lists the on-path modules it imports. Layer `[k]` = longest import
path to a leaf; a module only depends on strictly lower layers, so the graph is
acyclic and this is a valid topological order.

```
[0] Core            (leaf)
[0] Dual            (leaf)
[1] Density              <- Core
[1] Dynamics             <- Core
[2] DensityProperties    <- Core, Density
[2] FinMeasure           <- Core, Density
[2] Large                <- Core, Dual, Dynamics
[2] PeriodicCount        <- Core, Density
[2] TwoAdic              <- Core, Dynamics
[3] DensityExtra         <- Core, Density, DensityProperties
[3] DropTimeExact        <- Core, Density, Dynamics, TwoAdic
[3] GeometricValuation   <- Core, FinMeasure, TwoAdic
[3] PaperInterfaces      <- Core, Dynamics, Large
[3] SyracuseStructure    <- Core, Dynamics, TwoAdic
[3] TailBound            <- Core, Density, DensityProperties, FinMeasure
[4] CarrierDensity       <- Core, Density, DensityExtra, Dynamics
[4] OddPart              <- Core, Dynamics, TwoAdic, SyracuseStructure, PaperInterfaces
[4] SyracuseDescent      <- Core, Density, Dynamics, SyracuseStructure, TwoAdic
[4] ValuationBounds      <- Core, Density, Dynamics, SyracuseStructure, TwoAdic
[4] ValuationMoment      <- Core, Density, DensityProperties, FinMeasure, GeometricValuation, TwoAdic
[5] ContractionDrift     <- Core, Density, FinMeasure, GeometricValuation, TwoAdic, ValuationMoment
[5] FirstPassageDescent  <- Core, Dynamics, SyracuseDescent, SyracuseStructure, TwoAdic
[5] MinimalProof         <- CarrierDensity, Core, Density, DensityProperties, Dynamics, Large, OddPart, PaperInterfaces
[5] ValuationTail        <- Core, Density, DensityProperties, FinMeasure, GeometricValuation, TailBound, TwoAdic, ValuationMoment
[6] GenuineEstimates     <- Core, FinMeasure, GeometricValuation, PaperInterfaces, TailBound, TwoAdic, ValuationTail
[6] GoodStep             <- Core, Density, Dynamics, FirstPassageDescent, SyracuseDescent, SyracuseStructure, TwoAdic
[7] ValuationExact       <- Core, Density, DropTimeExact, Dynamics, FirstPassageDescent, GoodStep, SyracuseDescent, SyracuseStructure, TwoAdic, ValuationBounds
[8] GoodStepDensity      <- Core, Density, Dynamics, GoodStep, PeriodicCount, SyracuseDescent, SyracuseStructure, TwoAdic, ValuationExact
[9] PositiveDensity      <- Core, Density, Dynamics, GoodStepDensity, PeriodicCount, TwoAdic
[10] DescentSetPositive  <- Core, Density, Dynamics, GoodStepDensity, PositiveDensity
[11] HoleProof           <- CarrierDensity, ContractionDrift, Core, Density, DescentSetPositive, Dynamics, GenuineEstimates, Large, MinimalProof, PaperInterfaces, SyracuseStructure, TwoAdic
```

Three functional sub-DAGs feed `HoleProof`:

* **Density model** `Core -> Density -> {DensityProperties, DensityExtra,
  PeriodicCount} -> CarrierDensity` -- the genuine natural-density "almost all".
* **Dynamics / odd-part** `Core -> Dynamics -> {TwoAdic, SyracuseStructure} ->
  OddPart` (+ `Large`, `PaperInterfaces`) -- the Collatz/Syracuse maps and the
  odd-part orbit simulation used by `MinimalProof`.
* **Valuation / descent ingredients** `... -> GeometricValuation ->
  ValuationMoment -> {ContractionDrift, ValuationTail} -> GenuineEstimates` and
  `... -> GoodStep -> ValuationExact -> GoodStepDensity -> PositiveDensity ->
  DescentSetPositive` -- the three hole-free inputs bundled as `analyticInputs`.

## 3. The frontier: the gate split into eight steps

`assembleSyracuseGate = step8 . step7 . ... . step1` (in `HoleProof`). Each step
has a genuine, non-vacuous type; **`step1` is proved**, `step2 .. step8` are
explicit holes (the only holes in the whole tree).

| Step | Statement | Status |
|---|---|---|
| 1 | `StrictContraction` -- drift `E[a] >= 8/5` and strict `3^5 < 2^8` | **proved** |
| 2 | `IteratedGrowth` -- `3^{5k} <= 2^{8k}` | hole `?step2_rhs` |
| 3 | `ExactAffineDynamics` -- `2^{S_n(x)}·Syr^n(x) = 3^n·x + c` | hole `?step3_rhs` |
| 4 | `ValuationLowerBoundDensity` -- a.e. `y`, late `n` with `S_n(y) >= (8/5)n` | hole `?step4_rhs` |
| 5 | `ContractionDominatesDensity` -- a.e. `y`, eventually `3^n·f(y) <= 2^{S_n(y)}` | hole `?step5_rhs` |
| 6 | `TypicalDescentDensity` -- density-one descent below the start | hole `?step6_rhs` |
| 7 | `OddDensityControl` -- odd-domain first passage below `f -> infinity` | hole `?step7_rhs` |
| 8 | `SyracuseDensityControl` -- transfer along odd-part to the `Pos` gate | hole `?step8_rhs` |

Filling `step2 .. step8`, with no other change, upgrades the closed terms
`theorem13`, `theorem13Strict`, `theorem13PaperDomain`, `theorem13HasMember` to a
fully unconditional proof.

## 4. Off-path modules (not part of the main-theorem DAG)

22 modules build but are **not** reachable from `HoleProof.theorem13`. They are
either an alternative presentation of the same reduction chain, or supporting
theory not yet wired into the closed term:

* **Alternative reduction chain / presentation:** `Dependencies`,
  `PaperStructure`, `StructuredProof`, `OddThreshold`, `PaperAssumptions`.
  (These carry `Theorem13` in the older opaque-largeness form; `HoleProof` uses
  the genuine-density `MinimalProof` route instead.)
* **Algebraic core (matrix / affine / parity):** `Matrix`, `Affine`, `Algebra`,
  `Parity`, `OddStepClosed`, `Determinant`, `MatrixDynamics`, `MatrixGrowth`,
  `DynamicsExtra`.
* **Analytic infrastructure not yet threaded in:** `Convolution`,
  `UnifiedAnalytic`, `DisjointDensity`, `DensityClosure`, `IteratedDescent`,
  `ResidueClasses`, `ValuationTwoClass`, `ValuationDistribution`.

Reaching a *minimal* DAG for the theorem means either wiring the genuinely needed
parts of these in (e.g. when discharging steps 2--8) or leaving them as clearly
labelled auxiliary theory. They are retained (not deleted) because they contain
real, machine-checked mathematics that later steps may reuse.

## 5. Non-overlap: deduplication of common subproofs

Goal: **each lemma proved once**; specialisations are one-line instances of a
general lemma, and no two on-path modules re-prove the same fact.

### Already unified (this and earlier rounds)

| Fact | Single source | Former duplicates (now instances / removed) |
|---|---|---|
| Odd factor is odd (`isEven (oddFactor n) = False`) | `TwoAdic.oddFactorIsOdd` (fuelled induction, `Leq 1 n`) | `OddPart.oddFactorOdd` now delegates via `nonZeroToPos`; `OddPart.oddFactorFuelOdd`, `leqHalfFuel`, `halfNonZero`, `halfLtSelf` **removed** |
| One Syracuse step lands odd | `SyracuseStructure.syrValueOdd` (on `Nat`) | `OddPart.syrValueOdd` is now a thin `OddPos` wrapper delegating to it |
| `Leq (S n) n -> Void` | `DensityProperties.leqSuccAbsurd` | `TailBound.leqSuccAbsurd` **removed**; `TailBound`/`ValuationTail` reuse the single source |
| Exact 2-adic valuation `oddPartDropTime (2^k·m) = k` | `ValuationExact.dropTimePowOdd` | `DropTimeExact`'s three bespoke base cases are instances |
| Syracuse valuation from a factorisation; descent criterion | `ValuationExact.syrValuationFromFactor` / `descendsFromFactorPow2` | `ValuationTwoClass`, `GoodStepDensity` special cases are one-liners |
| Single-residue density `1/m` | `PeriodicCount.singleHitDensity` | `GoodStepDensity`, `ResidueClasses` counts are instances |

(See `GENERALIZATIONS.md` for the earlier "gobble" refactors.)

### Remaining overlap opportunities

* `plusSwapMid` is declared in both `PeriodicCount` (3-argument
  `x+(y+z)=y+(x+z)`) and `ValuationMoment` (4-argument
  `(a+b)+(c+d)=(a+c)+(b+d)`). These are **different** lemmas sharing a name (a
  naming collision, not a duplicated proof); the 4-argument form could be renamed
  or derived from the 3-argument one to remove the collision.
* `natPow` is defined in `HoleProof` (for the 8-step statements) and,
  independently, in the off-path `Determinant`; a shared low-level power on `Nat`
  would remove the duplication once the two DAGs are unified.
* Several arithmetic `Leq`/`plus` micro-lemmas recur across `Density`,
  `DensityProperties`, and the valuation modules; consolidating them into a
  single arithmetic prelude module is a further reduction.

## 6. How this file is kept honest

The DAG above is mechanically recoverable: transitive closure of the
`import TaoCollatz.*` edges from `HoleProof`. The overlap list is the set of
top-level names declared in more than one on-path module. Any refactor that
claims to remove an overlap is accompanied by a full `idris2 --build` that still
succeeds with no new holes (only `?step2_rhs .. ?step8_rhs` remain).
