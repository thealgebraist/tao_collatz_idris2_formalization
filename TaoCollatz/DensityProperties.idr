module TaoCollatz.DensityProperties

-- Further genuine content for the natural-density model of "almost all"
-- (`TaoCollatz.Density`).  The point of this module is to give the density
-- notion real *teeth*: a density-zero set is not merely closed under the paper's
-- set operations, it is genuinely *small* — its complement is cofinal.
--
-- Everything here is real mathematics: no placeholders, no `believe_me`, no
-- axioms; every definition is total and every lemma is proved from first
-- principles (a bounded search plus the elementary counting arithmetic already
-- developed in `TaoCollatz.Density`).
--
-- Main results:
--
--   * `negligibleCofalse`   — if `p` has natural density zero then for every
--       bound `bN` there is `n >= bN` with `p n = False`; i.e. a negligible set
--       cannot cofinitely fill the naturals.  The witness is *constructed* by a
--       bounded search whose success is guaranteed by a counting contradiction.
--   * `almostAllCofinal`    — dually, if `AlmostAll p` then the good set
--       `{ n : p n = True }` is cofinal (hence infinite): for every `bN` there
--       is `n >= bN` with `p n = True`.
--   * `negligibleNotAll` / `almostAllExistsMember` — immediate corollaries.

import Data.Nat
import TaoCollatz.Core
import TaoCollatz.Density

%default total

--------------------------------------------------------------------------------
-- A few elementary `Leq` facts not already in `Density`.
--------------------------------------------------------------------------------

public export
leqPred : {a : Nat} -> {b : Nat} -> Leq (S a) (S b) -> Leq a b
leqPred (LeqS h) = h

public export
leqSuccAbsurd : {n : Nat} -> Leq (S n) n -> Void
leqSuccAbsurd {n = Z} h impossible
leqSuccAbsurd {n = S k} (LeqS h) = leqSuccAbsurd h

public export
leqCancelLeft : (c : Nat) -> Leq (plus c a) (plus c b) -> Leq a b
leqCancelLeft Z h = h
leqCancelLeft (S c) (LeqS h) = leqCancelLeft c h

-- Split `a <= b` into the strict case `S a <= b` or equality `a = b`.
public export
leqSplit : {a : Nat} -> {b : Nat} -> Leq a b -> Either (Leq (S a) b) (a = b)
leqSplit {a = Z} {b = Z} LeqZ = Right Refl
leqSplit {a = Z} {b = S b'} LeqZ = Left (LeqS LeqZ)
leqSplit {a = S a'} {b = S b'} (LeqS h) =
  case leqSplit h of
    Left l => Left (LeqS l)
    Right eq => Right (cong S eq)

public export
multTwo : (d : Nat) -> mult d (S (S Z)) = plus d d
multTwo d =
  rewrite multCommutative d (S (S Z)) in
  rewrite plusZeroRightNeutral d in
  Refl

--------------------------------------------------------------------------------
-- Counting: unfolding a successor and a lower bound over an "all true" range.
--------------------------------------------------------------------------------

public export
countSuccEq :
  (p : Nat -> Bool) -> (k : Nat) ->
  count p (S k) = plus (indicator (p k)) (count p k)
countSuccEq p k = Refl

public export
countSuccTrue :
  (p : Nat -> Bool) -> (k : Nat) -> p k = True ->
  count p (S k) = S (count p k)
countSuccTrue p k prf =
  trans (countSuccEq p k) (cong (\b => plus (indicator b) (count p k)) prf)

-- If `p` is `True` on the whole range `[bN, bN + d)`, then it has at least `d`
-- members below `bN + d`.
public export
countAllTrueLower :
  (p : Nat -> Bool) -> (bN : Nat) -> (d : Nat) ->
  ((i : Nat) -> Leq bN i -> Leq (S i) (plus bN d) -> p i = True) ->
  Leq d (count p (plus bN d))
countAllTrueLower p bN Z allTrue = LeqZ
countAllTrueLower p bN (S d') allTrue =
  let pTrue : (p (plus bN d') = True)
      pTrue =
        allTrue (plus bN d')
          (leqPlusExtraRight bN d')
          (leqCastR (leqRefl (S (plus bN d'))) (plusSuccRightSucc bN d'))
      ih : Leq d' (count p (plus bN d'))
      ih =
        countAllTrueLower p bN d'
          (\i, lo, hi =>
             allTrue i lo (leqTrans hi (addLeftMono bN (leqSuccRight d'))))
      goalEq : count p (plus bN (S d')) = S (count p (plus bN d'))
      goalEq =
        trans (cong (count p) (sym (plusSuccRightSucc bN d')))
              (countSuccTrue p (plus bN d') pTrue)
  in leqCastR (LeqS ih) (sym goalEq)

--------------------------------------------------------------------------------
-- A bounded search that either finds a `False` point of `p` in `[base, base+len)`
-- or certifies that `p` is `True` throughout it.  This is what lets us extract a
-- *concrete* witness from the (otherwise classical) counting contradiction.
--------------------------------------------------------------------------------

public export
scanRange :
  (p : Nat -> Bool) -> (base : Nat) -> (len : Nat) ->
  Either
    (n : Nat ** (Leq base n, Leq (S n) (plus base len), p n = False))
    ((i : Nat) -> Leq base i -> Leq (S i) (plus base len) -> p i = True)
scanRange p base Z =
  Right (\i, lo, hi =>
    absurd (leqSuccAbsurd
      (leqTrans (leqCastR hi (plusZeroRightNeutral base)) lo)))
scanRange p base (S len') with (p (plus base len')) proof eqj
  scanRange p base (S len') | False =
    Left (plus base len' **
      ( leqPlusExtraRight base len'
      , leqCastR (leqRefl (S (plus base len'))) (plusSuccRightSucc base len')
      , eqj))
  scanRange p base (S len') | True =
    case scanRange p base len' of
      Left (n ** (lo, hi, isF)) =>
        Left (n **
          ( lo
          , leqTrans hi (addLeftMono base (leqSuccRight len'))
          , isF))
      Right allTrue' =>
        Right (\i, lo, hi =>
          let iLeJ : Leq i (plus base len')
              iLeJ = leqPred (leqCastR hi (sym (plusSuccRightSucc base len')))
          in case leqSplit iLeJ of
               Left iLtJ => allTrue' i lo iLtJ
               Right ieqJ => trans (cong p ieqJ) eqj)

--------------------------------------------------------------------------------
-- The teeth: a negligible set has a `False` point beyond every bound.
--------------------------------------------------------------------------------

public export
negligibleCofalse :
  {p : Nat -> Bool} -> Negligible p -> (bN : Nat) ->
  (n : Nat ** (Leq bN n, p n = False))
negligibleCofalse {p} neg bN =
  let (n0 ** pf) = neg (S Z)
      d : Nat
      d = maxN (S bN) n0
      dGtN : Leq (S bN) d
      dGtN = leqMaxL (S bN) n0
      bigNgeN0 : Leq n0 (plus bN d)
      bigNgeN0 = leqTrans (leqMaxR (S bN) n0) (leqPlusExtraLeft bN d)
  in case scanRange p bN d of
       Left (n ** (lo, _, isF)) => (n ** (lo, isF))
       Right allTrue =>
         let lower : Leq d (count p (plus bN d))
             lower = countAllTrueLower p bN d allTrue
             bound : Leq (mult (count p (plus bN d)) (S (S Z))) (plus bN d)
             bound = pf (plus bN d) bigNgeN0
             ddLe : Leq (mult d (S (S Z))) (plus bN d)
             ddLe = leqTrans (leqMultRight lower (S (S Z))) bound
             ddLe2 : Leq (plus d d) (plus bN d)
             ddLe2 = leqCastL (sym (multTwo d)) ddLe
             ddLe3 : Leq (plus d d) (plus d bN)
             ddLe3 = leqCastR ddLe2 (plusCommutative bN d)
             dLeN : Leq d bN
             dLeN = leqCancelLeft d ddLe3
         in absurd (leqSuccAbsurd (leqTrans dGtN dLeN))

--------------------------------------------------------------------------------
-- Dual statements for "almost all".
--------------------------------------------------------------------------------

public export
notFalseTrue : (b : Bool) -> not b = False -> b = True
notFalseTrue True _ = Refl
notFalseTrue False prf = absurd prf

-- The good set of an "almost all" predicate is cofinal (hence infinite).
public export
almostAllCofinal :
  {p : Nat -> Bool} -> AlmostAll p -> (bN : Nat) ->
  (n : Nat ** (Leq bN n, p n = True))
almostAllCofinal {p} ap bN =
  let (n ** (lo, isFalse)) = negligibleCofalse ap bN
  in (n ** (lo, notFalseTrue (p n) isFalse))

-- A negligible set is not all of the naturals.
public export
negligibleNotAll :
  {p : Nat -> Bool} -> Negligible p -> ((i : Nat) -> p i = True) -> Void
negligibleNotAll neg allTrue =
  let (n ** (_, isFalse)) = negligibleCofalse neg Z
  in absurd (trans (sym (allTrue n)) isFalse)

-- An "almost all" set has (in fact infinitely many) members.
public export
almostAllExistsMember :
  {p : Nat -> Bool} -> AlmostAll p -> (n : Nat ** p n = True)
almostAllExistsMember ap =
  let (n ** (_, isTrue)) = almostAllCofinal ap Z
  in (n ** isTrue)
