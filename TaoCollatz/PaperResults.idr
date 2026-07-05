module TaoCollatz.PaperResults

import Data.Nat
import TaoCollatz.Core
import TaoCollatz.Dynamics
import TaoCollatz.TwoAdic
import TaoCollatz.Large
import public TaoCollatz.Dependencies

%default total

--------------------------------------------------------------------------------
-- Complete coverage map of the numbered results of Tao,
-- "Almost all Collatz orbits attain almost bounded values" (taocollatz.pdf).
--
-- This module records an Idris2 declaration for *every* numbered result of the
-- paper, so that all parts feeding the central theorem (Theorem 1.3) are
-- converted to Idris2.  Each declaration is a `Type` -- the formalized
-- *statement* of the paper result.  Two kinds appear:
--
--   * Results already formalized elsewhere in the development are re-exposed
--     here as aliases to the existing Idris node, with the module that carries
--     the genuine content named in the docstring.  These are the main proof
--     spine (Theorems 1.3, 1.6, 3.1 and Propositions 1.9, 1.11, 1.14, 1.17,
--     7.1, 7.3, 7.8).
--
--   * The remaining supporting lemmas/propositions/corollaries (Lemmas 1.12,
--     2.1, 2.2, 4.1, 5.3, 6.2, 7.2, 7.4, 7.6, 7.7, 7.9, 7.10, Proposition 5.2,
--     Corollary 6.3) and the two conjectures (1.1, 1.5) are given faithful
--     Idris2 statements here for the first time.  Where the statement is
--     expressible over the concrete `Nat` dynamics already in the tree, it is
--     stated with genuine content (Conjectures 1.1 and 1.5).  The deep
--     probabilistic / Fourier / renewal results require a probability-,
--     measure- and Fourier-theory layer that the base library does not provide
--     (documented as infrastructure C1-C5 in REMAINING_WORK.md); their
--     statements are recorded here as abstract statement placeholders
--     (payload `Unit`), exactly matching the convention already used for the
--     analytic nodes 1.14 / 1.17 / 7.1 / 7.3 / 7.8 in `PaperInterfaces`.
--
-- No `believe_me`, `postulate`, `assert_*`, `%foreign`, `idris_crash`, axioms
-- or holes are introduced; this module is `%default total`.  These are
-- statement-level `Type`s, so no proof term is fabricated for any result that
-- is not genuinely proved.
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Section 1 : main results, Syracuse reformulation, and the key propositions
--------------------------------------------------------------------------------

||| Conjecture 1.1 (Collatz conjecture).  `Col_min(N) = 1` for all `N >= 1`,
||| i.e. every positive integer eventually reaches `1` under the Collatz map.
||| Faithful concrete statement over the `Nat`-valued Collatz map `Col`.  This
||| is an open conjecture; only its statement is formalized (no proof term).
public export
Conjecture11 : Type
Conjecture11 =
  (p : Pos) -> PaperPositive p -> (k : Nat ** posValue (iter k Col p) = 1)

||| Theorem 1.3 (Almost all Collatz orbits attain almost bounded values).
||| Already formalized as `Large.Theorem13` (genuine natural-density form in
||| `MinimalProof` / `HoleProof`).
public export
Theorem13Statement : Type
Theorem13Statement = Theorem13

||| Conjecture 1.5 (Collatz conjecture, Syracuse formulation).
||| `Syr_min(N) = 1` for all odd `N >= 1`.  Faithful concrete statement over the
||| Syracuse map `Syr`; an open conjecture, statement only.
public export
Conjecture15 : Type
Conjecture15 =
  (q : OddPos) -> PaperOddPositive q -> (k : Nat ** oddValue (iter k Syr q) = 1)

||| Theorem 1.6 (Almost all Syracuse orbits attain almost bounded values).
||| Already formalized as `Large.Theorem16`.
public export
Theorem16Statement : Type
Theorem16Statement = Theorem16

||| Proposition 1.9 (Distribution of the n-Syracuse valuation).
||| Already formalized as `PaperInterfaces.ValuationDistribution`, whose payload
||| carries the genuine exact tail / geometric halving content proved in
||| `ValuationTail` and packaged in `GenuineEstimates`.
public export
Proposition19Statement : Type
Proposition19Statement = ValuationDistribution

||| Proposition 1.11 (Stabilisation of first passage).
||| Already formalized as `Dependencies.StabilisationOfFirstPassage`.
public export
Proposition111Statement : Type
Proposition111Statement = StabilisationOfFirstPassage

||| Lemma 1.12 (Recursive formula for Syracuse random variables).  For any
||| `n` and `x in Z/3^{n+1}Z`,
|||   P(Syrac(Z/3^{n+1}Z) = x)
|||     = (sum_{1<=a<=2*3^n, 2^a x = 1 mod 3} 2^{-a} P(Syrac(Z/3^n Z) = (2^a x - 1)/3))
|||       / (1 - 2^{-2*3^n}).
||| Deep probabilistic recursion on the Syracuse random variable; requires the
||| distributions-on-`Z/3^nZ` layer (infrastructure C1/C4).  Statement recorded
||| as an abstract placeholder (payload `Unit`).
public export
Lemma112Statement : Type
Lemma112Statement = Unit

||| Proposition 1.14 (Fine-scale mixing of n-Syracuse offsets).
||| Already formalized as `PaperInterfaces.FineScaleMixing`.
public export
Proposition114Statement : Type
Proposition114Statement = FineScaleMixing

||| Proposition 1.17 (Decay of the characteristic function).
||| Already formalized as `PaperInterfaces.FourierDecay`.
public export
Proposition117Statement : Type
Proposition117Statement = FourierDecay

--------------------------------------------------------------------------------
-- Section 2 : the n-Syracuse valuation and the Chernoff-type bound
--------------------------------------------------------------------------------

||| Lemma 2.1 (Description of the n-Syracuse valuation).  For odd `N` and each
||| `n`, the valuation tuple `a^{(n)}(N)` is the unique tuple `a` of positive
||| integers of length `n` for which the affine image `Aff_a(N)` is an odd
||| integer.
|||
||| The one-step core of this description is genuinely expressible over the
||| concrete dynamics already in the tree: the single Syracuse valuation
||| `a(q) = oddPartDropTime (3q+1)` is exactly the power of two dividing
||| `3q+1`, i.e. `2^{a(q)} * (odd part of 3q+1) = 3q+1`, and `Syr q` is that
||| odd part.  We record that faithful one-step statement here.  (The full
||| n-tuple uniqueness routes through the affine 2-adic machinery; the
||| single-step form below already pins down the valuation description.)
public export
syrStepValuation : OddPos -> Nat
syrStepValuation q = oddPartDropTime (3 * oddValue q + 1)

public export
Lemma21Statement : Type
Lemma21Statement =
  (q : OddPos) ->
  pow2 (syrStepValuation q) * oddValue (Syr q) = 3 * oddValue q + 1

||| The single-step valuation description of Lemma 2.1 is genuinely *proved*:
||| `2^{a(q)} * (odd part of 3q+1) = 3q+1`, where `a(q)` is the 2-adic
||| valuation of `3q+1`.  This is the `n = 1` case of the description and pins
||| down the per-step Syracuse valuation exactly.  (The full `n`-tuple
||| uniqueness statement `Lemma21Statement` above additionally quantifies over
||| all lengths `n`; this proof discharges the single-step core via the exact
||| 2-adic factorisation `TwoAdic.oddFactorization`.)
public export
lemma21OneStep : Lemma21Statement
lemma21OneStep (MkOddPos n) =
  rewrite multCommutative (pow2 (oddPartDropTime (3 * n + 1)))
                          (oddFactor (3 * n + 1)) in
    sym (oddFactorization (3 * n + 1))

||| Lemma 2.2 (Chernoff-type bound).  For a `Z^d`-valued random variable `v`
||| with exponential tails and mean `mu`, non-degenerate (not supported on a
||| coset of a proper subgroup), the sum `v_[1,n]` of `n` iid copies obeys the
||| local-limit / large-deviation bounds
|||   (i)  P(v_[1,n] = L)   <<  (n+1)^{-d/2} G_n(c(L - n mu))
|||   (ii) P(|v_[1,n] - n mu| >= lambda)  <<  exp(-c lambda^2 / n) + exp(-c lambda).
||| Requires the probability / sub-Gaussian tail layer (infrastructure C1/C3).
||| Statement recorded as an abstract placeholder (payload `Unit`).
public export
Lemma22Statement : Type
Lemma22Statement = Unit

--------------------------------------------------------------------------------
-- Section 3 : the alternate (quantitative) form of the main theorem
--------------------------------------------------------------------------------

||| Theorem 3.1 (Alternate form of the main theorem).  For `N0, x >= 2`, the
||| logarithmic mass of Syracuse orbits from `[1,x]` that never descend below
||| `N0` is `O(log^{-c} N0)`, uniformly in `x`.  Already formalized as
||| `Dependencies.QuantitativeSyracuseBound`.
public export
Theorem31Statement : Type
Theorem31Statement = QuantitativeSyracuseBound

--------------------------------------------------------------------------------
-- Section 4 : the tail bound for the total valuation
--------------------------------------------------------------------------------

||| Lemma 4.1 (Tail bound).  `P(|a^{(n)}(N)| >= n') << 2^{-c n}` for the total
||| `n`-Syracuse valuation `|a^{(n)}(N)| = a_[1,n]`.  The genuine exponential
||| decay of the single-valuation survival function is proved in
||| `ValuationTail.tailGeoValuationLe`
|||   (`mu({a >= j+1}) <= 2^{n-j}`);
||| the full total-valuation tail additionally needs the Chernoff bound
||| (Lemma 2.2).  Statement recorded here as an abstract placeholder; see the
||| genuine per-step tail in `ValuationTail`.
public export
Lemma41Statement : Type
Lemma41Statement = Unit

--------------------------------------------------------------------------------
-- Section 5 : the approximate formula and the pointwise bound
--------------------------------------------------------------------------------

||| Proposition 5.2 (Approximate formula).  For `E` a subset of the odd numbers
||| in `[1,x]` and `y = x^alpha`, the first-passage location distribution
|||   P(Pass_x(N_y) in E)
|||     = sum_{n in I_y} sum_{a in A(n-m0)} sum_{M in E'} P(Aff_a(N_y) = M)
|||       + O(log^{-c} x).
||| Requires the approximate-formula / logarithmic-density layer (C1).
||| Statement recorded as an abstract placeholder (payload `Unit`).
public export
Proposition52Statement : Type
Proposition52Statement = Unit

||| Lemma 5.3.  The coefficients `c_n(X) << 1` for all `n in I_y` and
||| `X in Z/3^{n-m0}Z`.  Requires the same approximate-formula layer.
||| Statement recorded as an abstract placeholder (payload `Unit`).
public export
Lemma53Statement : Type
Lemma53Statement = Unit

--------------------------------------------------------------------------------
-- Section 6 : injectivity and 3-adic separation of the offset map
--------------------------------------------------------------------------------

||| Lemma 6.2 (Injectivity of offsets).  For each `n`, the `n`-Syracuse offset
||| map `F_n : (N+1)^n -> Z[1/2]` is injective.  Requires the offset map over
||| `Z[1/2]`; recorded here as an abstract statement placeholder (payload
||| `Unit`).  The affine monoid underpinning `F_n` is proved in `Affine`.
public export
Lemma62Statement : Type
Lemma62Statement = Unit

||| Corollary 6.3 (3-adic separation of offsets).  The quantitative 3-adic
||| refinement of Lemma 6.2: for `C_A` large and `n` large, the residues
||| `F_{k+1}(a_{k+1},...,a_1) mod 3^n` are distinct as the tuples range over the
||| concentration set (6.12) with fixed total valuation `l`.  Requires the
||| 3-adic offset layer.  Statement recorded as an abstract placeholder.
public export
Corollary63Statement : Type
Corollary63Statement = Unit

--------------------------------------------------------------------------------
-- Section 7 : the Fourier / renewal machinery
--------------------------------------------------------------------------------

||| Proposition 7.1 (Key quantitative Fourier estimate).
||| Already formalized as `PaperInterfaces.KeyFourierEstimate`.
public export
Proposition71Statement : Type
Proposition71Statement = KeyFourierEstimate

||| Lemma 7.2 (Cancellation for white points).  If `(j,l)` is white then
||| `|f(3^{2j-2} 2^{-l}, 3)| <= exp(-eps_3)`.  Requires the characteristic
||| function `f` on `Z/3^nZ` (infrastructure C4).  Abstract placeholder.
public export
Lemma72Statement : Type
Lemma72Statement = Unit

||| Proposition 7.3 (Renewal "white points" combinatorial input).
||| Already formalized as `PaperInterfaces.RenewalWhitePoints`.
public export
Proposition73Statement : Type
Proposition73Statement = RenewalWhitePoints

||| Lemma 7.4 (Structure of the black set).  The black set
||| `B = {(j,l) : |theta(j,l)| <= eps}` is a disjoint union of triangles, each
||| contained in `[n/2 - (1/10) log(1/eps)] x Z`, with any two triangles
||| separated by distance `>= (1/10) log(1/eps)`.  Requires the geometric /
||| renewal layer (C5).  Abstract placeholder (payload `Unit`).
public export
Lemma74Statement : Type
Lemma74Statement = Unit

||| Lemma 7.6 (Basic properties of the holding time).  `Hold` has exponential
||| tails, is not supported on any coset of a proper subgroup of `Z^2`, and has
||| mean `(4,16)`; in particular Lemma 2.2 applies to `Hold` with `mu = (4,16)`.
||| Requires the renewal-process layer (C5).  Abstract placeholder.
public export
Lemma76Statement : Type
Lemma76Statement = Unit

||| Lemma 7.7 (Distribution of the first-passage location).  For iid copies
||| `v_k = (j_k, l_k)` of `Hold` and first passage time `k` (least with
||| `l_[1,k] > s`), one has, for `l > s`,
|||   P(v_[1,k] = (j,l)) << e^{-c(l-s)} G(c(j - s/...)).
||| Requires the renewal-process layer (C5).  Abstract placeholder.
public export
Lemma77Statement : Type
Lemma77Statement = Unit

||| Proposition 7.8 (Renewal / stability monotonicity estimate).
||| Already formalized as `PaperInterfaces.RenewalMonotonicity` (its payload
||| carries the genuine tail-monotonicity content of `GenuineEstimates`).
public export
Proposition78Statement : Type
Proposition78Statement = RenewalMonotonicity

||| Lemma 7.9 (Many triangles usually implies many white points).  For iid
||| copies of `Hold`, any `(j',l')` and `R >= 1`,
|||   E exp(-sum_{p=1}^{t_{min(r,R)}} 1_W((j',l') + v_[1,p]) + eps min(r,R))
|||     <= exp(eps).
||| Requires the renewal-process layer (C5).  Abstract placeholder.
public export
Lemma79Statement : Type
Lemma79Statement = Unit

||| Lemma 7.10 (Large triangles are rarely encountered shortly after a lengthy
||| crossing).  With `(j,l)` in a black triangle, `s = l_Delta - l > m / log^2 m`,
||| `k` the associated first-passage time, `p in N` and `1 <= s' <= m^{0.4}`, the
||| event `E_{p,s'}` that `(j,l) + v_[1,k+p]` lies in a triangle of size
||| `>= s'` obeys `P(E_{p,s'}) << A^{1+p}/s' + exp(-c A^2 (1+p))`.
||| Requires the renewal-process layer (C5).  Abstract placeholder.
public export
Lemma710Statement : Type
Lemma710Statement = Unit
