module TaoCollatz.PeriodicResidue

-- Genuine, fully-proved density of an *arbitrary* single residue class.
--
-- The existing residue-density lemmas (`GoodStepDensity.res1mod4`,
-- `ValuationOneClass.res3mod4`, ...) all hand-unroll a *fixed* period (4).  The
-- density analysis of the Syracuse valuation needs, for every `k`, a residue
-- class of period `2^k`; those cannot be hand-unrolled uniformly in `k`.
--
-- This module builds, once and for all, a computable residue-class indicator
-- `atRes p r` of period `P = S p` (any period `>= 1`) and proves, from first
-- principles:
--
--   * it is periodic:            `atRes p r (n + P) = atRes p r n`   (`atResPeriodic`);
--   * it has exactly one member per period, for any residue `r < P`
--     (`countAtResPerPeriod`);
--   * hence it has natural density exactly `1/P`:  over `q` full periods it has
--     exactly `q` members (`atResDensity`), via `PeriodicCount.singleHitDensity`.
--
-- This is the general "a single residue class mod `P` has density `1/P`" fact,
-- valid for every period, feeding the geometric Syracuse-valuation density in
-- `TaoCollatz.ValuationGeometric` (items C1/C2 of `REMAINING_WORK.md`).
--
-- Everything here is real mathematics: `%default total`, no placeholders, no
-- `believe_me`, no axioms, no holes.

import TaoCollatz.Core
import TaoCollatz.Density
import TaoCollatz.PeriodicCount
import Data.Nat

%default total

--------------------------------------------------------------------------------
-- Boolean equality on `Nat` with the lemmas we need.
--------------------------------------------------------------------------------

||| Boolean equality on naturals (own definition, for clean equations).
public export
natBeq : Nat -> Nat -> Bool
natBeq Z Z = True
natBeq Z (S _) = False
natBeq (S _) Z = False
natBeq (S a) (S b) = natBeq a b

public export
natBeqRefl : (n : Nat) -> natBeq n n = True
natBeqRefl Z = Refl
natBeqRefl (S n) = natBeqRefl n

||| If `a < b` then `natBeq a b = False`.
public export
natBeqFalseLt : (a : Nat) -> (b : Nat) -> Leq (S a) b -> natBeq a b = False
natBeqFalseLt Z (S b') _ = Refl
natBeqFalseLt (S a') (S b') (LeqS h) = natBeqFalseLt a' b' h

||| If `b < a` then `natBeq a b = False`.
public export
natBeqFalseGt : (a : Nat) -> (b : Nat) -> Leq (S b) a -> natBeq a b = False
natBeqFalseGt (S a') Z _ = Refl
natBeqFalseGt (S a') (S b') (LeqS h) = natBeqFalseGt a' b' h

--------------------------------------------------------------------------------
-- One "tick" of the mod-`(S p)` counter, and its iteration.
--------------------------------------------------------------------------------

||| Successor modulo `P = S p`: `p |-> 0`, otherwise `x |-> S x`.
public export
nextMod : (p : Nat) -> Nat -> Nat
nextMod p x = if natBeq x p then Z else S x

||| Below the top of the period the tick is an honest successor.
public export
nextModLt : (p : Nat) -> (x : Nat) -> Leq (S x) p -> nextMod p x = S x
nextModLt p x h = rewrite natBeqFalseLt x p h in Refl

||| At the top of the period the tick wraps to zero.
public export
nextModTop : (p : Nat) -> nextMod p p = Z
nextModTop p = rewrite natBeqRefl p in Refl

||| Iterate the tick `m` times.
public export
applyNout : (p : Nat) -> Nat -> Nat -> Nat
applyNout p Z x = x
applyNout p (S m) x = nextMod p (applyNout p m x)

||| Iteration is additive in the number of ticks.
public export
applyNoutPlus :
  (p : Nat) -> (a : Nat) -> (b : Nat) -> (x : Nat) ->
  applyNout p (plus a b) x = applyNout p a (applyNout p b x)
applyNoutPlus p Z b x = Refl
applyNoutPlus p (S a') b x =
  cong (nextMod p) (applyNoutPlus p a' b x)

||| Ticking `d` times from `base`, while staying within the period, is honest
||| addition: `applyNout p d base = base + d` whenever `base + d <= p`.
public export
reachP :
  (p : Nat) -> (base : Nat) -> (d : Nat) ->
  Leq (plus base d) p -> applyNout p d base = plus base d
reachP p base Z h = sym (plusZeroRightNeutral base)
reachP p base (S d') h =
  let hEq : (plus base (S d') = S (plus base d'))
      hEq = sym (plusSuccRightSucc base d')
      hLt : Leq (S (plus base d')) p
      hLt = leqCastL (sym hEq) h
      hLe : Leq (plus base d') p
      hLe = leqTrans (leqSuccRight (plus base d')) hLt
      ih : applyNout p d' base = plus base d'
      ih = reachP p base d' hLe
  in rewrite ih in
     rewrite natBeqFalseLt (plus base d') p hLt in
     sym hEq

--------------------------------------------------------------------------------
-- The phase (`n mod P`) and its cyclic return.
--------------------------------------------------------------------------------

||| The phase of `n` modulo `P = S p`: `phase p n = n mod (S p)`.
public export
phase : (p : Nat) -> Nat -> Nat
phase p n = applyNout p n Z

||| Below the period, the phase is the identity: `phase p i = i` for `i <= p`.
public export
phaseSmall : (p : Nat) -> (i : Nat) -> Leq i p -> phase p i = i
phaseSmall p i h = reachP p Z i h

||| A full period of `P = S p` ticks returns to the start (for any start
||| `x <= p`).
public export
cycleReturn :
  (p : Nat) -> (x : Nat) -> Leq x p -> applyNout p (S p) x = x
cycleReturn p x hx =
  case leqExists hx of      -- p = plus x d
    (d ** peq) =>
      let spEq : (S p = plus x (S d))
          spEq = trans (cong S peq) (plusSuccRightSucc x d)
          -- applyNout p d x = plus x d = p
          reach : (applyNout p d x = p)
          reach = trans (reachP p x d (leqCastL (sym peq) (leqRefl p))) (sym peq)
          -- one more tick from p wraps to 0
          wrap : (applyNout p (S d) x = Z)
          wrap = trans (cong (nextMod p) reach) (nextModTop p)
          -- then x ticks from 0 return to x
          back : (applyNout p x Z = x)
          back = reachP p Z x hx
          proofPlus : (applyNout p (plus x (S d)) x = x)
          proofPlus = trans (applyNoutPlus p x (S d) x)
                        (trans (cong (applyNout p x) wrap) back)
      in trans (cong (\m => applyNout p m x) spEq) proofPlus

--------------------------------------------------------------------------------
-- The residue-class indicator and its periodicity.
--------------------------------------------------------------------------------

||| Indicator of the residue class `n ≡ r (mod (S p))`.
public export
atRes : (p : Nat) -> (r : Nat) -> Nat -> Bool
atRes p r n = natBeq (phase p n) r

||| The residue-class indicator has period `P = S p`.
public export
atResPeriodic :
  (p : Nat) -> (r : Nat) -> (n : Nat) ->
  atRes p r (plus n (S p)) = atRes p r n
atResPeriodic p r n =
  cong (\z => natBeq z r) $
    trans (applyNoutPlus p n (S p) Z)
          (cong (applyNout p n) (cycleReturn p Z LeqZ))

--------------------------------------------------------------------------------
-- Exactly one member of the class per period.
--------------------------------------------------------------------------------

||| A bounded extensionality for `count`: if `p` and `q` agree on every index
||| below `bigN`, their counts below `bigN` coincide.
public export
countExtBelow :
  (p : Nat -> Bool) -> (q : Nat -> Bool) -> (bigN : Nat) ->
  ((i : Nat) -> Leq (S i) bigN -> p i = q i) ->
  count p bigN = count q bigN
countExtBelow p q Z h = Refl
countExtBelow p q (S k) h =
  rewrite h k (leqRefl (S k)) in
  rewrite countExtBelow p q k (\i, hi => h i (leqTrans hi (leqSuccRight k))) in
  Refl

||| If `p i = False` for every index below `bigN`, the count is zero.
public export
countAllFalse :
  (p : Nat -> Bool) -> (bigN : Nat) ->
  ((i : Nat) -> Leq (S i) bigN -> p i = False) ->
  count p bigN = 0
countAllFalse p Z h = Refl
countAllFalse p (S k) h =
  rewrite h k (leqRefl (S k)) in
  countAllFalse p k (\i, hi => h i (leqTrans hi (leqSuccRight k)))

||| The singleton indicator `== r` has count exactly one below `S r`.
public export
countSingletonAtR :
  (r : Nat) -> count (\i => natBeq i r) (S r) = 1
countSingletonAtR r =
  rewrite natBeqRefl r in
  rewrite countAllFalse (\i => natBeq i r) r
            (\i, hi => natBeqFalseLt i r hi) in
  Refl

||| The singleton indicator `== r` has count exactly one over any range strictly
||| above `r`: `count (\i => natBeq i r) (S r + d) = 1`.
public export
countSingletonExact :
  (r : Nat) -> (d : Nat) ->
  count (\i => natBeq i r) (plus (S r) d) = 1
countSingletonExact r d =
  rewrite countPlus (\i => natBeq i r) (S r) d in
  rewrite countSingletonAtR r in
  rewrite countAllFalse (\i => natBeq (plus (S r) i) r) d
            (\i, _ => natBeqFalseGt (plus (S r) i) r (leqPlusExtraRight (S r) i)) in
  Refl

||| Exactly one member of the residue class `r < S p` in one period.
public export
countAtResPerPeriod :
  (p : Nat) -> (r : Nat) -> Leq (S r) (S p) ->
  count (\i => atRes p r i) (S p) = 1
countAtResPerPeriod p r hr =
  let agree : (i : Nat) -> Leq (S i) (S p) -> atRes p r i = natBeq i r
      agree i hi =
        cong (\z => natBeq z r)
          (phaseSmall p i (leqPredFromSuccLeq hi))
  in trans (countExtBelow (\i => atRes p r i) (\i => natBeq i r) (S p) agree)
       (case leqExists hr of
          (d ** deq) =>
            trans (cong (count (\i => natBeq i r)) deq)
                  (countSingletonExact r d))

--------------------------------------------------------------------------------
-- The density of the residue class: `1/P` over full periods.
--------------------------------------------------------------------------------

||| A single residue class of period `P = S p` has natural density exactly
||| `1/P`: over `q` full periods it has exactly `q` members.
public export
atResDensity :
  (p : Nat) -> (r : Nat) -> Leq (S r) (S p) ->
  (q : Nat) -> count (\i => atRes p r i) (mult q (S p)) = q
atResDensity p r hr q =
  singleHitDensity (\i => atRes p r i) (S p)
    (\n => atResPeriodic p r n)
    (countAtResPerPeriod p r hr) q
