module TaoCollatz.FinMeasure

-- A single unified, inductive model for the paper's analytic "domains".
--
-- The research-scale analytic machinery behind Tao's theorem (2-adic measure
-- theory, tail/large-deviation bounds, characteristic-function / Fourier decay,
-- renewal theory) is, at its algebraic core, the study of a *finitely supported
-- measure* on the natural numbers and how it behaves under summation of
-- independent increments.  This module introduces that one carrier -- an honest
-- inductive algebraic datatype `FinDist` -- and the elementary measure-theoretic
-- functionals on it.  The companion modules `TaoCollatz.Convolution` (renewal /
-- characteristic functions) and `TaoCollatz.TailBound` (tail / large-deviation
-- estimates) build the four "domains" as *instances* of this single theory.
--
-- Everything here is real, total mathematics: `%default total`, no
-- placeholders, no `believe_me`, no axioms, no holes.

import Data.Nat
import TaoCollatz.Core
import TaoCollatz.Density

%default total

--------------------------------------------------------------------------------
-- The carrier: a finitely supported measure on `Nat`.
--
-- `FinDist` is the free `Nat`-weighted collection of points of `Nat`.  A term
-- `Atom v w rest` records mass `w` sitting at the value `v`, on top of `rest`.
-- This is exactly a finitely supported measure `mu : Nat -> Nat` presented by a
-- (multiset) list of "value, weight" atoms; it is the discrete, fully
-- constructive stand-in for a probability/measure space (item C1) and for the
-- Syracuse valuation random variables (item C2).
--------------------------------------------------------------------------------

public export
data FinDist : Type where
  Empty : FinDist
  Atom  : (value : Nat) -> (weight : Nat) -> FinDist -> FinDist

||| Concatenation of two measures (the disjoint sum of measures, i.e. `mu + nu`).
public export
mix : FinDist -> FinDist -> FinDist
mix Empty e = e
mix (Atom v w r) e = Atom v w (mix r e)

--------------------------------------------------------------------------------
-- The basic measure functionals.
--------------------------------------------------------------------------------

||| Total mass `mu(Nat)` of the measure.
public export
mass : FinDist -> Nat
mass Empty = Z
mass (Atom _ w r) = plus w (mass r)

||| The first moment `sum_v v * mu(v)` (an unnormalised expectation).
public export
weightedSum : FinDist -> Nat
weightedSum Empty = Z
weightedSum (Atom v w r) = plus (mult v w) (weightedSum r)

||| The Dirac measure: unit mass at `v`.
public export
dirac : Nat -> FinDist
dirac v = Atom v (S Z) Empty

||| Scale every weight by `c` (multiplication of the measure by a scalar).
public export
scale : Nat -> FinDist -> FinDist
scale c Empty = Empty
scale c (Atom v w r) = Atom v (mult c w) (scale c r)

--------------------------------------------------------------------------------
-- Additivity of the functionals over `mix`.
--------------------------------------------------------------------------------

public export
massMix : (d : FinDist) -> (e : FinDist) -> mass (mix d e) = plus (mass d) (mass e)
massMix Empty e = Refl
massMix (Atom v w r) e =
  rewrite massMix r e in plusAssociative w (mass r) (mass e)

public export
weightedSumMix :
  (d : FinDist) -> (e : FinDist) ->
  weightedSum (mix d e) = plus (weightedSum d) (weightedSum e)
weightedSumMix Empty e = Refl
weightedSumMix (Atom v w r) e =
  rewrite weightedSumMix r e in
  plusAssociative (mult v w) (weightedSum r) (weightedSum e)

--------------------------------------------------------------------------------
-- Scaling laws.
--------------------------------------------------------------------------------

public export
massScale : (c : Nat) -> (d : FinDist) -> mass (scale c d) = mult c (mass d)
massScale c Empty = sym (multZeroRightZero c)
massScale c (Atom v w r) =
  rewrite massScale c r in sym (multDistributesOverPlusRight c w (mass r))

public export
weightedSumScale :
  (c : Nat) -> (d : FinDist) ->
  weightedSum (scale c d) = mult c (weightedSum d)
weightedSumScale c Empty = sym (multZeroRightZero c)
weightedSumScale c (Atom v w r) =
  rewrite weightedSumScale c r in
  rewrite multAssociative v c w in
  rewrite multCommutative v c in
  rewrite sym (multAssociative c v w) in
  sym (multDistributesOverPlusRight c (mult v w) (weightedSum r))

--------------------------------------------------------------------------------
-- Dirac facts (sanity: a point mass has mass one and first moment its point).
--------------------------------------------------------------------------------

public export
massDirac : (v : Nat) -> mass (dirac v) = S Z
massDirac v = Refl

public export
weightedSumDirac : (v : Nat) -> weightedSum (dirac v) = v
weightedSumDirac v =
  rewrite multOneRightNeutral v in plusZeroRightNeutral v

--------------------------------------------------------------------------------
-- Decidable comparison producing a usable `Leq` proof, and the tail functional.
--------------------------------------------------------------------------------

||| Decision procedure returning an actual `Leq` proof either way.  Used to
||| define, and reason about, the tail functional below.
public export
data LeqDec : Nat -> Nat -> Type where
  IsLeq : Leq a b -> LeqDec a b
  IsGt  : Leq (S b) a -> LeqDec a b

public export
decLeq : (a : Nat) -> (b : Nat) -> LeqDec a b
decLeq Z b = IsLeq LeqZ
decLeq (S a) Z = IsGt (LeqS LeqZ)
decLeq (S a) (S b) = case decLeq a b of
  IsLeq p => IsLeq (LeqS p)
  IsGt p => IsGt (LeqS p)

||| The upper tail `mu({ x : x >= t })`: total mass sitting at values `>= t`.
||| This is the fundamental object of every large-deviation / tail estimate.
public export
massGe : Nat -> FinDist -> Nat
massGe t Empty = Z
massGe t (Atom v w r) = case decLeq t v of
  IsLeq _ => plus w (massGe t r)
  IsGt _ => massGe t r

||| At threshold zero the tail is the whole mass.
public export
massGeZero : (d : FinDist) -> massGe Z d = mass d
massGeZero Empty = Refl
massGeZero (Atom v w r) = rewrite massGeZero r in Refl

||| The tail never exceeds the total mass.
public export
massGeLeMass : (t : Nat) -> (d : FinDist) -> Leq (massGe t d) (mass d)
massGeLeMass t Empty = LeqZ
massGeLeMass t (Atom v w r) with (decLeq t v)
  _ | IsLeq _ = leqAdd (leqRefl w) (massGeLeMass t r)
  _ | IsGt _ = leqTrans (massGeLeMass t r) (leqPlusExtraLeft w (mass r))
