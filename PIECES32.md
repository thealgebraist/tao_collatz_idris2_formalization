# The 32-piece orthogonal split of the four remaining holes

The central theorem's remaining analytic content previously lived in **four**
honest holes of `TaoCollatz/Pieces64.idr`:

* `piece34_driftPastMDensity` — large-deviation drift past a fixed time
  (heart of `step4`);
* `piece35_driftUniformFromFixed` — uniform diagonalisation to a growing
  height `f` (the `step4` uniformity);
* `piece50_descentTimePositive` — the typical descent taken at a *positive*
  time;
* `piece59_diagonalHeight` — renewal / first passage below a growing height
  (heart of `step7`).

These four holes are now **split into 32 orthogonal sub-pieces**, grouped
`subA1..subA8`, `subB1..subB8`, `subC1..subC8`, `subD1..subD8` (8 per parent).
Each sub-piece carries a genuine, non-vacuous, *true* type (nothing is weakened
to `Unit`/`True`), and the four parents are now **defined by composing** their
eight sub-pieces through a per-group assembler (`subA8`/`subB8`/`subC8`/`subD8`),
so filling the sub-holes — with no other change — upgrades the closed theorems
`theorem13`, `theorem13Strict`, `theorem13PaperDomain`, `theorem13HasMember`.

The whole package still builds (`idris2 --build taocollatz.ipkg`, exit 0,
63/63 modules), stays `%default total`, and uses no
`believe_me`/`postulate`/`assert_*`/`%foreign`/`idris_crash`/axioms.

## Layout

| Group | Parent | Sub-pieces | Theme |
|-------|--------|-----------|-------|
| A | `piece34` | `subA1..subA8` | drift past a fixed time on a density-one set |
| B | `piece35` | `subB1..subB8` | uniform diagonalisation to a growing height |
| C | `piece50` | `subC1..subC8` | positive-time typical descent |
| D | `piece59` | `subD1..subD8` | first passage below a growing height |

In each group `subX8` is the **assembler**: it takes the seven supporting
sub-pieces `subX1..subX7` and produces the parent's milestone type
(`DriftPastTy`, `DriftUniformTy`, `DescentPosTy`, `DiagonalHeightTy`). The
assembler holes carry the irreducible deep analytic content (large deviation,
diagonalisation, positive-time descent, renewal); the seven supporting
sub-pieces per group are genuine, true, mostly-elementary facts that a real
assembly draws on.

## Work completed: four sub-pieces proved outright

* **`subA1_valSumAdd`** (group A) — additivity of the partial valuation sum
  `S_{m+n}(x) = S_m(x) + S_n(Syr^m x)` (reuses `piece01_syrValSumAdd`).
* **`subB1_inflatedGrows`** (group B) — height inflation preserves tending to
  infinity: `\y => 243 (f y)^5` tends to infinity whenever `f` does (via
  `growthMonotone` and `fLeqG`).
* **`subC2_descentCompose`** (group C) — descent composition preserves the
  bound: descents at `n1` then `n2` compose to a descent at `n1 + n2` (via
  `piece09_iterSyrAdd` and `leqTrans`).
* **`subD1_descentToSyrBelow`** (group D) — a descent below the start yields a
  `SyrBelow` witness at the start's size (reuses `piece12_descentToSyrBelow`).

The remaining 28 sub-pieces are honest holes (`?subA2..?subA8`, `?subB2..?subB8`,
`?subC1`/`?subC3..?subC8`, `?subD2..?subD8`), each a genuine, true proposition.
