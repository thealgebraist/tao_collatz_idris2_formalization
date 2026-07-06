# Analysis of the four assembler holes `subA8`, `subB8`, `subC8`, `subD8`

This note records a focused investigation of the four remaining holes in
`TaoCollatz/Pieces64.idr`. They are the **only** holes in the project
(`grep` for `?ident` over `TaoCollatz/*.idr` returns exactly `?subA8`,
`?subB8`, `?subC8`, `?subD8`). The main theorem is fully reduced to these four.

The conclusion of this investigation is that each of the four is the genuine
**density-one analytic core** of Tao's Theorem 1.3, not a packaging step that
can be discharged by the density algebra already in the project. This matches
the in-source documentation and, for `subB8`, is *proved* inside the project.

## What each hole actually demands

All four are "assemblers": they receive seven supporting facts (all already in
scope and mostly proved) plus, in three cases, a black-box milestone
hypothesis, and must produce the milestone type.

The decisive observation is that **each assembler must be valid for _every_
input**, including the trivial inputs that are actually fed to it:

* `subA8 : ... -> DriftPastTy` is applied with `subA7_driftSomewhere`
  (`= piece32_driftSomewhereDensity`), whose only witness is `n = 0`.
  So `subA8` must produce, for every fixed `m`, a **density-one** set with a
  drift witness `n ≥ m` satisfying `8·n ≤ 5·Sₙ(y)` — i.e. it must prove the
  density-one large-deviation drift essentially from scratch.
* `subC8 : ... -> DescentPosTy` and `subD8 : ... -> DiagonalHeightTy` are
  applied with the trivial `TypicalDescentDensity` (`= piece49`), whose only
  witness is `n = 0` (`oddSize (iter 0 Syr y) = oddSize y`). Hence:
  * `subC8` must prove a **density-one** set on which descent occurs at a
    strictly **positive** time — the trivial `n = 0` reading is exactly what
    must be excluded, which needs the real dynamics.
  * `subD8` must, from "reaches below its own size", prove **density-one**
    first passage below a growing height `f` (with `f → ∞` only relative to
    `oddSize`, so `f y` may be far below `oddSize y`). This is the renewal /
    first-passage argument.
* `subB8 : ... -> DriftUniformTy` is the uniform diagonalisation:
  from a family of fixed-time drift sets (density one for each bound `m`),
  produce a single density-one set working past a growing height `f`.

`Density.Negligible` is genuine **natural-density-zero** (see
`TaoCollatz/Density.idr`), not merely cofinite, so these are the true analytic
statements and not weakened variants.

## `subB8`'s abstract form is provably impossible

`TaoCollatz/DiagonalizationLimit.idr` contains a completed proof,
`noUniformLateWitnessForPDiag`, that the abstract schema behind `subB8`
(`UniformLateWitness p` for an arbitrary predicate `p`) is **uninhabited**:
taking `p y n = (n < oddSize y)` and `f = oddSize`, every fixed bound is met on
a density-one set yet no density-one set can admit a witness past `f`. Therefore
any honest proof of `subB8` must use the specific arithmetic of the Syracuse
valuation sums (the equidistribution / large-deviation content of the paper),
not the density algebra alone.

## What is already genuinely proved toward these holes

* `TaoCollatz/OrbitValuationDrift.driftPastOnClass` discharges the group-A drift
  inequality on the explicit residue class `y = 2^{2k+1}·n + 1` (density
  `2^{-(2k+1)}`), where the exact orbit result gives `Sₖ(y) = 2k`, so
  `8k ≤ 5·(2k)`. This is a real, non-vacuous, positive-time witness — but only
  on a class of density `2^{-(2k+1)}`, not density one.
* Supporting analytic machinery exists in isolation: Markov's inequality on
  finite distributions (`TailBound.markov`), valuation moments
  (`ValuationMoment`), residue-class densities (`ResidueClasses`,
  `PeriodicCount.periodicCount`/`singleHitDensity`), and exact k-step orbit
  landing (`OrbitValuationExactOrbit`, `OrbitValuationKStep`).

## Why the holes cannot be closed here, honestly

Upgrading the class-level facts above to **density one** requires the
concentration / law-of-large-numbers step for the Syracuse valuation sums,
built on the equidistribution of the orbit modulo `2^N` and a variance/renewal
estimate. That theory (the analytic heart of Tao 2019) is present in Mathlib
neither, and is not assembled in this project. Formalising it is a large,
multi-part development.

In this environment the theorem-proving automation targets Lean, not Idris2, so
every Idris2 proof term must be written and checked by hand against a rebuilt
Idris2 toolchain. Producing the full density-one theory by hand within a single
session is not feasible, and the project's soundness discipline
(`%default total`; no `believe_me`/`postulate`/`assert_*`/`%foreign`/
`idris_crash`/axioms/holes beyond the four) rules out any shortcut that would
fake the missing content.

Accordingly, the four holes were **left exactly as they were** — honestly
marked, with the complete reduction of the main theorem to them intact — rather
than closed with vacuous or unsound witnesses. This document records the precise
mathematical status so the remaining work is clearly scoped: the missing
ingredient is the density-one valuation-concentration + renewal estimate, from
which all four assemblers follow.
