module TaoCollatz.OddThreshold

import TaoCollatz.Core
import TaoCollatz.Dynamics
import TaoCollatz.Large
import TaoCollatz.OddPart
import TaoCollatz.Dependencies

%default total

--------------------------------------------------------------------------------
-- Genuine construction of the growth-compatible odd-threshold system.
--
-- Earlier runs took the odd-threshold system (the choice of Syracuse thresholds
-- underlying the density transfer Theorem 1.6 => Theorem 1.3) as an *explicit
-- hypothesis*, because it cannot be defined as a total function of `f` alone:
-- the true choice is the infimum of `f` over each odd fibre {2^k * q}, which is
-- not computable from `f`.
--
-- The key observation exploited here is that the transfer only ever needs the
-- threshold together with `f`'s *growth witness* `w : TendsToInfinityPos f`
-- (which the theorem already has in hand).  From that witness the threshold is
-- constructed *constructively and totally*:
--
--   oddThresholdOf w q = the largest target t <= q with (thresholdFor w t) <= q.
--
-- This satisfies both requirements the paper needs:
--   * compatibility:  oddThresholdOf w (oddPart pos) <= f pos   (Prop. below),
--   * growth:         f -> infinity  ==>  oddThresholdOf w -> infinity.
--
-- Consequently the density transfer, and hence the whole central theorem, no
-- longer needs the odd-threshold system as a hypothesis: `theorem16ToTheorem13`
-- becomes an *unconditional* reduction `Theorem16 -> Theorem13`.
--------------------------------------------------------------------------------

-- Decidable comparison producing a usable proof either way.
public export
decLeq : (a, b : Nat) -> Either (Leq a b) (Leq (S b) a)
decLeq Z b = Left LeqZ
decLeq (S a) Z = Right (LeqS LeqZ)
decLeq (S a) (S b) = case decLeq a b of
  Left le => Left (LeqS le)
  Right gt => Right (LeqS gt)

public export
leqSuccAbsurd : Leq (S n) n -> Void
leqSuccAbsurd (LeqS le) = leqSuccAbsurd le

public export
leqEqOrLess : {k, b : Nat} -> Leq k b -> Either (k = b) (Leq (S k) b)
leqEqOrLess {k=Z} {b=Z} LeqZ = Left Refl
leqEqOrLess {k=Z} {b=S b'} LeqZ = Right (LeqS LeqZ)
leqEqOrLess (LeqS le) = case leqEqOrLess le of
  Left eq => Left (cong S eq)
  Right l => Right (LeqS l)

-- The odd factor never exceeds its argument (dropping factors of 2 shrinks).
public export
oddFactorFuelLe : (fuel : Nat) -> (n : Nat) -> Leq (oddFactorFuel fuel n) n
oddFactorFuelLe Z n = leqRefl n
oddFactorFuelLe (S f) n with (isEven n)
  _ | False = leqRefl n
  _ | True = leqTrans (oddFactorFuelLe f (half n)) (halfLe n)

public export
oddFactorLe : (n : Nat) -> Leq (oddFactor n) n
oddFactorLe n = oddFactorFuelLe n n

public export
oddPartSizeLe : (pos : Pos) -> Leq (oddSize (oddPart pos)) (posSize pos)
oddPartSizeLe (MkPos n) = oddFactorLe n

-- A small `max` with the two obvious inequalities.
public export
maxNat : Nat -> Nat -> Nat
maxNat Z b = b
maxNat (S a) Z = S a
maxNat (S a) (S b) = S (maxNat a b)

public export
leqMaxL : (a, b : Nat) -> Leq a (maxNat a b)
leqMaxL Z b = LeqZ
leqMaxL (S a) Z = leqRefl (S a)
leqMaxL (S a) (S b) = LeqS (leqMaxL a b)

public export
leqMaxR : (a, b : Nat) -> Leq b (maxNat a b)
leqMaxR Z b = leqRefl b
leqMaxR (S a) Z = LeqZ
leqMaxR (S a) (S b) = LeqS (leqMaxR a b)

--------------------------------------------------------------------------------
-- The threshold search.
--------------------------------------------------------------------------------

-- `findBest thr q t` = the largest target t' in {0,...,t} whose modulus
-- `thr t'` is at most `q` (defaulting to 0).
public export
findBest : (thr : Nat -> Nat) -> (q : Nat) -> (t : Nat) -> Nat
findBest thr q Z = Z
findBest thr q (S t) = case decLeq (thr (S t)) q of
  Left _ => S t
  Right _ => findBest thr q t

-- Compatibility core: whatever `findBest` returns is bounded by `f x`, provided
-- `q <= posSize x`.  (If it returns 0 the bound is trivial; otherwise its
-- modulus is <= q <= posSize x, so `f`'s growth witness yields the bound.)
public export
findBestCompat :
  {f : Pos -> Nat} ->
  (w : TendsToInfinityPos f) ->
  (t, q : Nat) -> (x : Pos) ->
  Leq q (posSize x) ->
  Leq (findBest (thresholdFor w) q t) (f x)
findBestCompat w Z q x hq = LeqZ
findBestCompat w (S t) q x hq with (decLeq (thresholdFor w (S t)) q)
  _ | Left le =
        growsPast w (S t) x (leqTrans le hq)
  _ | Right _ = findBestCompat w t q x hq

-- Growth core: if `t0 <= t` and its modulus is <= q, then `findBest` returns
-- at least `t0`.
public export
findBestGe :
  (thr : Nat -> Nat) -> (q, t, t0 : Nat) ->
  Leq t0 t -> Leq (thr t0) q ->
  Leq t0 (findBest thr q t)
findBestGe thr q Z t0 le0 hthr = le0
findBestGe thr q (S t) t0 le0 hthr with (decLeq (thr (S t)) q)
  _ | Left _ = le0
  _ | Right gt = case leqEqOrLess le0 of
        Left eq =>
          void (leqSuccAbsurd
                  (leqTrans gt (rewrite sym eq in hthr)))
        Right l =>
          findBestGe thr q t t0 (leqPredFromSuccLeq l) hthr

--------------------------------------------------------------------------------
-- The constructed threshold and its two properties.
--------------------------------------------------------------------------------

public export
oddThresholdOf : {f : Pos -> Nat} -> TendsToInfinityPos f -> OddPos -> Nat
oddThresholdOf w odd = findBest (thresholdFor w) (oddSize odd) (oddSize odd)

-- Compatibility: the constructed threshold at the odd part of any positive
-- integer is bounded by `f` there.
public export
oddThresholdOfCompatible :
  {f : Pos -> Nat} ->
  (w : TendsToInfinityPos f) ->
  (pos : Pos) ->
  Leq (oddThresholdOf w (oddPart pos)) (f pos)
oddThresholdOfCompatible w pos =
  findBestCompat w
    (oddSize (oddPart pos))
    (oddSize (oddPart pos))
    pos
    (oddPartSizeLe pos)

-- Growth: as the odd argument grows, so does the constructed threshold.
public export
oddThresholdOfGrows :
  {f : Pos -> Nat} ->
  (w : TendsToInfinityPos f) ->
  TendsToInfinityOdd (oddThresholdOf w)
oddThresholdOfGrows w =
  MkTendsToInfinityOn
    (\target => maxNat target (thresholdFor w target))
    (\target, odd, large =>
      findBestGe (thresholdFor w) (oddSize odd) (oddSize odd) target
        (leqTrans (leqMaxL target (thresholdFor w target)) large)
        (leqTrans (leqMaxR target (thresholdFor w target)) large))

--------------------------------------------------------------------------------
-- The unconditional density transfer and central theorem.
--------------------------------------------------------------------------------

-- Lift a Syracuse "almost all below the threshold" conclusion to a Collatz
-- "almost all below f" conclusion, using compatibility and the proven odd-part
-- orbit transfer.
public export
liftSyracuseToCollatz :
  {f : Pos -> Nat} ->
  (w : TendsToInfinityPos f) ->
  AlmostAllOdd (\odd => SyrBelow odd (oddThresholdOf w odd)) ->
  AlmostAllPos (\pos => ColBelow pos (f pos))
liftSyracuseToCollatz w oddControl =
  controlMap Pos
    (controlPullback TaoCollatz.Dynamics.oddPart oddControl)
    (\pos, syrBelowThr =>
       oddPartOrbitTransfer f pos
         (eventuallyMonotoneBound
            syrBelowThr
            (oddThresholdOfCompatible w pos)))

||| The Syracuse => Collatz density transfer, now **unconditional**: the
||| odd-threshold system is constructed from the growth witness rather than
||| assumed.  This is Theorem 1.6 => Theorem 1.3 with no side hypothesis.
public export
theorem16ToTheorem13Constructive : Theorem16 -> Theorem13
theorem16ToTheorem13Constructive syr f fGrows =
  liftSyracuseToCollatz fGrows
    (syr (oddThresholdOf fGrows) (oddThresholdOfGrows fGrows))

||| The full reduction chain assembled without any odd-threshold hypothesis:
||| given the (placeholder) first-passage analytic input, Theorem 1.3 follows.
public export
centralTheoremConstructive : FirstPassageAnalyticInput -> Theorem13
centralTheoremConstructive analytic =
  theorem16ToTheorem13Constructive
    (theorem31ToTheorem16FromPrinciple
      (proposition11ToTheorem31FromIteration
        (analyticInputToStabilisation analytic)))

||| The central theorem with the odd-threshold hypothesis eliminated: only the
||| deep analytic input (Props. 1.9 / 7.8, still a placeholder) remains as an
||| ingredient, and it is the one supplied in `TaoCollatz.Dependencies`.
public export
centralTheoremUnconditional : Theorem13
centralTheoremUnconditional =
  centralTheoremConstructive firstPassageAnalyticInput
