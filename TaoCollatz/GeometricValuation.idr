module TaoCollatz.GeometricValuation

-- The 2-adic valuation distribution, as a concrete instance of the unified
-- `FinDist` carrier.
--
-- The random variable at the heart of the paper is the 2-adic valuation of the
-- Syracuse step: on the `2^K` residues mod `2^K`, exactly `2^{K-j}` of them have
-- valuation `j` (`j = 1..K`), i.e. the valuation is (truncated) geometric with
-- `P(a = j) ~ 2^{-j}`.  `geoValuation K` is precisely this finitely supported
-- measure, built on the shared carrier, and we prove its **total mass is
-- `2^K - 1`** -- the exact geometric normalisation.  Combined with the generic
-- `TaoCollatz.TailBound.markov`, this turns the abstract tail machinery into a
-- genuine statement about the actual valuation distribution.
--
-- Everything here is real, total mathematics: `%default total`, no
-- placeholders, no `believe_me`, no axioms, no holes.

import Data.Nat
import TaoCollatz.Core
import TaoCollatz.TwoAdic
import TaoCollatz.FinMeasure

%default total

--------------------------------------------------------------------------------
-- Shifting all point-values up by one (preserving mass).
--------------------------------------------------------------------------------

public export
shift1 : FinDist -> FinDist
shift1 Empty = Empty
shift1 (Atom v w r) = Atom (S v) w (shift1 r)

public export
massShift1 : (d : FinDist) -> mass (shift1 d) = mass d
massShift1 Empty = Refl
massShift1 (Atom v w r) = cong (plus w) (massShift1 r)

--------------------------------------------------------------------------------
-- The (truncated) geometric valuation measure.
--
-- `geoValuation (S k)` places mass `2^k` at valuation `1`, and on top of it a
-- copy of `geoValuation k` with every valuation shifted up by one -- so value
-- `j` carries weight `2^{K-j}`, exactly the count of residues of valuation `j`.
--------------------------------------------------------------------------------

public export
geoValuation : Nat -> FinDist
geoValuation Z = Empty
geoValuation (S k) = Atom (S Z) (pow2 k) (shift1 (geoValuation k))

--------------------------------------------------------------------------------
-- Exact geometric normalisation: total mass = 2^K - 1.
--------------------------------------------------------------------------------

||| The total mass of the valuation measure over `K` scales is `2^K - 1`, stated
||| additively as `mass + 1 = 2^K` to stay within `Nat`.
public export
massGeoValuationPlusOne :
  (n : Nat) -> plus (mass (geoValuation n)) (S Z) = pow2 n
massGeoValuationPlusOne Z = Refl
massGeoValuationPlusOne (S k) =
  rewrite massShift1 (geoValuation k) in
  rewrite sym (plusAssociative (pow2 k) (mass (geoValuation k)) (S Z)) in
  rewrite massGeoValuationPlusOne k in
  Refl

--------------------------------------------------------------------------------
-- Concrete sanity checks.
--------------------------------------------------------------------------------

||| Over three scales the measure is `{1|->4, 2|->2, 3|->1}` with total mass 7.
public export
massGeoValuationThree : mass (geoValuation 3) = 7
massGeoValuationThree = Refl

public export
geoValuationThreeForm :
  geoValuation 3
    = Atom 1 4 (Atom 2 2 (Atom 3 1 Empty))
geoValuationThreeForm = Refl
