module TaoCollatz.TailBound

-- Tail / large-deviation estimates as one theory on the unified carrier
-- `FinDist`.
--
-- Every tail estimate in the paper (the 2-adic valuation tail of Prop. 1.9, the
-- exponential/sub-Gaussian bounds of the first-passage analysis) is a statement
-- about the upper tail `mu({x >= t})` of a measure.  This module proves the
-- structural backbone shared by all of them:
--
--   * additivity of the tail over disjoint measures (`massGeMix`);
--   * monotonicity of the tail in the threshold (`massGeMonoThreshold`);
--   * **Markov's inequality** (`markov`): `t * mu({x >= t}) <= E[x]`,
--     the elementary large-deviation bound from which the quantitative tail
--     estimates are bootstrapped.
--
-- Everything here is real, total mathematics: `%default total`, no
-- placeholders, no `believe_me`, no axioms, no holes.

import Data.Nat
import TaoCollatz.Core
import TaoCollatz.Density
import TaoCollatz.FinMeasure

%default total

--------------------------------------------------------------------------------
-- Small `Leq` contradiction helpers.
--------------------------------------------------------------------------------

public export
leqSuccAbsurd : (n : Nat) -> Leq (S n) n -> Void
leqSuccAbsurd (S n) (LeqS h) = leqSuccAbsurd n h

--------------------------------------------------------------------------------
-- Tail is additive over the disjoint sum of measures.
--------------------------------------------------------------------------------

public export
massGeMix :
  (t : Nat) -> (d : FinDist) -> (e : FinDist) ->
  massGe t (mix d e) = plus (massGe t d) (massGe t e)
massGeMix t Empty e = Refl
massGeMix t (Atom v w r) e with (decLeq t v)
  _ | IsLeq _ =
    rewrite massGeMix t r e in plusAssociative w (massGe t r) (massGe t e)
  _ | IsGt _ = massGeMix t r e

--------------------------------------------------------------------------------
-- Tail is monotone (decreasing) in the threshold.
--------------------------------------------------------------------------------

public export
massGeMonoThreshold :
  (t1 : Nat) -> (t2 : Nat) -> Leq t2 t1 ->
  (d : FinDist) -> Leq (massGe t1 d) (massGe t2 d)
massGeMonoThreshold t1 t2 le Empty = LeqZ
massGeMonoThreshold t1 t2 le (Atom v w r) with (decLeq t1 v) | (decLeq t2 v)
  _ | IsLeq _ | IsLeq _ = leqAdd (leqRefl w) (massGeMonoThreshold t1 t2 le r)
  _ | IsLeq p1 | IsGt p2 =
    void (leqSuccAbsurd v (leqTrans p2 (leqTrans le p1)))
  _ | IsGt _ | IsLeq _ =
    leqTrans (massGeMonoThreshold t1 t2 le r)
             (leqPlusExtraLeft w (massGe t2 r))
  _ | IsGt _ | IsGt _ = massGeMonoThreshold t1 t2 le r

--------------------------------------------------------------------------------
-- Markov's inequality: `t * mu({x >= t}) <= E[x]`.
--------------------------------------------------------------------------------

public export
markov :
  (t : Nat) -> (d : FinDist) ->
  Leq (mult t (massGe t d)) (weightedSum d)
markov t Empty = rewrite multZeroRightZero t in LeqZ
markov t (Atom v w r) with (decLeq t v)
  _ | IsLeq tLeV =
    -- massGe t (Atom v w r) = w + massGe t r ; weightedSum = v*w + weightedSum r
    let step1 : Leq (mult t (plus w (massGe t r)))
                    (plus (mult t w) (mult t (massGe t r)))
        step1 = leqCastR (leqRefl _)
                  (multDistributesOverPlusRight t w (massGe t r))
        twLeVw : Leq (mult t w) (mult v w)
        twLeVw = leqMultRight tLeV w
        tailLe : Leq (mult t (massGe t r)) (weightedSum r)
        tailLe = markov t r
    in leqTrans step1 (leqAdd twLeVw tailLe)
  _ | IsGt _ =
    -- tail drops this atom; compare against `weightedSum r` and pad with v*w
    leqTrans (markov t r) (leqPlusExtraLeft (mult v w) (weightedSum r))

--------------------------------------------------------------------------------
-- A concrete instance: Markov gives a genuine numeric tail bound.
--------------------------------------------------------------------------------

||| Sanity check: for the two-point measure `{0 |-> 1, 4 |-> 1}` the tail at
||| threshold `3` has mass `1`, and Markov certifies `3 * 1 <= 4`.
public export
markovExample :
  Leq (mult 3 (massGe 3 (Atom 0 1 (Atom 4 1 Empty))))
      (weightedSum (Atom 0 1 (Atom 4 1 Empty)))
markovExample = markov 3 (Atom 0 1 (Atom 4 1 Empty))
