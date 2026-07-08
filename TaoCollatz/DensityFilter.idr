module TaoCollatz.DensityFilter

-- ORDER / LATTICE-THEORETIC LOWERING of the "almost all / natural-density-one"
-- layer that surrounds the four remaining analytic holes of the central
-- theorem.
--
-- The point of this module is to answer, *rigorously and honestly*, the request
-- to "find an equivalent way to formalize the remaining holes by lowering the
-- theories down to a simpler domain (order / lattice theory)".  What can and
-- cannot be lowered is made precise here:
--
--   * The DENSITY SCAFFOLDING really is pure order/lattice theory: the
--     natural-density-one predicates on the odd numbers form a genuine PROPER
--     FILTER on the boolean lattice `(OddPos -> Bool)` -- it contains the top
--     element, is upward closed under the pointwise order, is closed under
--     binary meet, and does NOT contain the bottom element.  We package exactly
--     these facts as `densityFilter` (all fields are the already-proved density
--     closure lemmas), so every use of "almost all" in the four holes is, at the
--     level of the density layer, a statement about membership in this filter.
--
--   * Each of the four remaining holes is EQUIVALENT (no weakening, proved both
--     directions in Idris) to a filter-phrased version in which every
--     `AlmostAllOddD good` is replaced by the order-theoretic `InDensity good`.
--     This literally relocates the holes into lattice/order theory.
--
--   * The relocation does NOT make the holes go away, and this is not an
--     accident: a plain filter is closed only under FINITE meets, whereas the
--     analytic content of the holes is exactly a form of *countable / diagonal*
--     combination that the density-one filter does NOT satisfy.  The companion
--     module `TaoCollatz.DiagonalizationLimit` already contains a machine-checked
--     proof (`noUniformLateWitnessForPDiag`) that the natural order-theoretic
--     "diagonal-selection" closure fails outright.  Hence the residual content
--     is irreducibly arithmetic (Tao's equidistribution / large-deviation
--     estimate), and CANNOT be discharged inside order/lattice theory.  See
--     `LOWERING.md`.
--
-- Everything is `%default total`; no `believe_me`/`postulate`/`assert_*`/
-- `%foreign`/`idris_crash`/axioms/holes are used in this module.

import TaoCollatz.Core
import TaoCollatz.Dynamics
import TaoCollatz.Large
import TaoCollatz.Density
import TaoCollatz.CarrierDensity
import TaoCollatz.Pieces64

%default total

--------------------------------------------------------------------------------
-- The boolean lattice of odd predicates and its pointwise order.
--------------------------------------------------------------------------------

||| Pointwise order on odd predicates: `p <= q` iff `p` implies `q` everywhere.
||| This is the order of the boolean lattice `(OddPos -> Bool)` whose meet is
||| `\x => p x && q x`, join `\x => p x || q x`, top `\_ => True`, bottom
||| `\_ => False`.
public export
Implies : (OddPos -> Bool) -> (OddPos -> Bool) -> Type
Implies p q = (x : OddPos) -> p x = True -> q x = True

||| The order-theoretic meet (greatest lower bound) of two odd predicates.
public export
meetOdd : (OddPos -> Bool) -> (OddPos -> Bool) -> (OddPos -> Bool)
meetOdd p q = \x => p x && q x

||| The top element of the lattice.
public export
topOdd : OddPos -> Bool
topOdd = \_ => True

||| The bottom element of the lattice.
public export
botOdd : OddPos -> Bool
botOdd = \_ => False

--------------------------------------------------------------------------------
-- Filters on the lattice of odd predicates (pure order/lattice theory).
--------------------------------------------------------------------------------

||| A FILTER on the boolean lattice `(OddPos -> Bool)`: a family of predicates
||| that contains the top element, is upward closed under `Implies`, and is
||| closed under binary meet.  This is the standard order-theoretic notion of a
||| filter on a bounded meet-semilattice.
public export
record OddFilter where
  constructor MkOddFilter
  ||| Membership predicate ("the element is `large`").
  InFilter : (OddPos -> Bool) -> Type
  ||| The top element is a member.
  hasTop   : InFilter DensityFilter.topOdd
  ||| Upward closure: a superset of a member is a member.
  upward   : (p : OddPos -> Bool) -> (q : OddPos -> Bool) ->
             Implies p q -> InFilter p -> InFilter q
  ||| Closure under binary meet.
  meet     : (p : OddPos -> Bool) -> (q : OddPos -> Bool) ->
             InFilter p -> InFilter q -> InFilter (DensityFilter.meetOdd p q)

--------------------------------------------------------------------------------
-- The natural-density-one filter.
--------------------------------------------------------------------------------

||| **The density-one filter.**  Its members are exactly the predicates that
||| hold on a set of natural density one (`AlmostAllOddD`).  Its three filter
||| laws are precisely the already-proved density closure lemmas
||| (`almostAllOddTrue`, `almostAllOddMono`, `andAlmostAllOdd`), so "almost all"
||| is *literally* membership in an order-theoretic filter.
public export
densityFilter : OddFilter
densityFilter =
  MkOddFilter
    AlmostAllOddD
    almostAllOddTrue
    (\p, q, sub, ap => almostAllOddMono {p} {q} sub ap)
    (\p, q, ap, aq => andAlmostAllOdd {p} {q} ap aq)

||| Membership in the density-one filter, as an order-theoretic predicate.
public export
InDensity : (OddPos -> Bool) -> Type
InDensity = InFilter densityFilter

||| `InDensity` unfolds to `AlmostAllOddD` (they are definitionally equal); this
||| bridge makes the identification usable in both directions.
public export
inDensityIsAlmostAll : (p : OddPos -> Bool) -> InDensity p -> AlmostAllOddD p
inDensityIsAlmostAll p h = h

||| ... and conversely.
public export
almostAllIsInDensity : (p : OddPos -> Bool) -> AlmostAllOddD p -> InDensity p
almostAllIsInDensity p h = h

--------------------------------------------------------------------------------
-- Properness: the density-one filter is a PROPER filter.
--------------------------------------------------------------------------------

||| **Properness.**  The bottom element (the always-false predicate, i.e. the
||| empty set) is NOT a member of the density-one filter: a set of density one
||| cannot be empty.  Together with the three filter laws this shows
||| `densityFilter` is a genuine *proper* filter on the lattice.
public export
densityFilterProper : InDensity DensityFilter.botOdd -> Void
densityFilterProper h = allOddNotNegligible h

--------------------------------------------------------------------------------
-- The four remaining holes, faithfully relocated into order/lattice theory.
--
-- Each hole type of `TaoCollatz.Pieces64` is re-expressed with every occurrence
-- of `AlmostAllOddD good` replaced by the order-theoretic membership
-- `InDensity good`.  Because `InDensity = InFilter densityFilter = AlmostAllOddD`
-- definitionally, each relocated type is EQUIVALENT to the original, and the two
-- directions of the equivalence are the identity.  Nothing is weakened: filling
-- the order-theoretic hole is exactly the same as filling the analytic one.
--------------------------------------------------------------------------------

||| Group A (coreA), order-theoretic form: for each fixed bound `m`, the set of
||| odd `y` admitting a drift time `n >= m` is a member of the density filter.
public export
DriftPastFilterTy : Type
DriftPastFilterTy =
  (m : Nat) ->
  (good : OddPos -> Bool **
    (InDensity good,
     (y : OddPos) -> good y = True ->
       (n : Nat ** (Leq m n, Leq (mult 8 n) (mult 5 (syrValSum n y))))))

||| Group B (coreB), order-theoretic form.
public export
DriftUniformFilterTy : Type
DriftUniformFilterTy =
  DriftPastFilterTy ->
  (f : OddPos -> Nat) -> TendsToInfinityOdd f ->
  (good : OddPos -> Bool **
    (InDensity good,
     (y : OddPos) -> good y = True ->
       (n : Nat ** (Leq (f y) n, Leq (mult 8 n) (mult 5 (syrValSum n y))))))

||| Group C (coreC), order-theoretic form.
public export
DescentPosFilterTy : Type
DescentPosFilterTy =
  (good0 : OddPos -> Bool **
    (InDensity good0,
     (y : OddPos) -> good0 y = True ->
       (n : Nat ** Leq (oddSize (iter n Syr y)) (oddSize y)))) ->
  (good : OddPos -> Bool **
    (InDensity good,
     (y : OddPos) -> good y = True ->
       (n : Nat ** (Leq 1 n, Leq (oddSize (iter n Syr y)) (oddSize y)))))

||| Group D (coreD), order-theoretic form.
public export
DiagonalHeightFilterTy : Type
DiagonalHeightFilterTy =
  (good0 : OddPos -> Bool **
    (InDensity good0,
     (y : OddPos) -> good0 y = True ->
       (n : Nat ** Leq (oddSize (iter n Syr y)) (oddSize y)))) ->
  (f : OddPos -> Nat) -> TendsToInfinityOdd f ->
  (good : OddPos -> Bool **
    (InDensity good,
     (y : OddPos) -> good y = True -> SyrBelow y (f y)))

--------------------------------------------------------------------------------
-- The equivalences (both directions are the identity; no weakening).
--------------------------------------------------------------------------------

public export
driftPast_toFilter : DriftPastTy -> DriftPastFilterTy
driftPast_toFilter h = h

public export
driftPast_fromFilter : DriftPastFilterTy -> DriftPastTy
driftPast_fromFilter h = h

public export
driftUniform_toFilter : DriftUniformTy -> DriftUniformFilterTy
driftUniform_toFilter h = h

public export
driftUniform_fromFilter : DriftUniformFilterTy -> DriftUniformTy
driftUniform_fromFilter h = h

public export
descentPos_toFilter : DescentPosTy -> DescentPosFilterTy
descentPos_toFilter h = h

public export
descentPos_fromFilter : DescentPosFilterTy -> DescentPosTy
descentPos_fromFilter h = h

public export
diagonalHeight_toFilter : DiagonalHeightTy -> DiagonalHeightFilterTy
diagonalHeight_toFilter h = h

public export
diagonalHeight_fromFilter : DiagonalHeightFilterTy -> DiagonalHeightTy
diagonalHeight_fromFilter h = h
