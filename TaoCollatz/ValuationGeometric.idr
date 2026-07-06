module TaoCollatz.ValuationGeometric

-- Genuine, fully-proved *arithmetic realisation* of the geometric
-- Syracuse-valuation survival law, for **every** `k`.
--
-- The abstract measure `GeometricValuation.geoValuation` models the valuation
-- random variable's law `P(a = j) = 2^{-j}` on the finite carrier.  The
-- residue-class modules `ValuationOneClass` / `ValuationTwoClass` pin its base
-- atoms `a = 1` / `a = 2` onto the actual arithmetic (hand-unrolled at the fixed
-- periods 4, 8).  This module does the same *uniformly in `k`*:
--
--   * `tailResidue k` exhibits, for every `k`, a residue `r_k < 2^k` together
--     with the 2-adic factorisation `3 r_k + 1 = 2^k * s_k` (`s_k >= 1`) — the
--     obstruction that forces valuation `>= k` on the whole class `n ≡ r_k`.
--   * `valuationGeOnTailClass` proves that **every** `n` in the residue class
--     `n ≡ r_k (mod 2^k)` has `syrValuation n >= k` (the survival event
--     `a >= k`).
--   * `tailClassDensity` proves the class has natural density exactly `2^{-k}`
--     (over `q` full periods it has exactly `q` members), via the general
--     `PeriodicResidue.atResDensity`.
--
-- Together: for every `k` there is a residue class of density exactly `2^{-k}`
-- on which the actual Syracuse valuation is `>= k` — the exact survival function
-- `P(a >= k) = 2^{-k}` of the geometric law, realised arithmetically (items
-- C1/C2 of `REMAINING_WORK.md`).  This subsumes the `a = 1` / `a = 2` atoms.
--
-- Everything here is real mathematics: `%default total`, no placeholders, no
-- `believe_me`, no axioms, no holes.

import TaoCollatz.Core
import TaoCollatz.Dynamics
import TaoCollatz.TwoAdic
import TaoCollatz.SyracuseStructure
import TaoCollatz.ValuationBounds
import TaoCollatz.ValuationExact
import TaoCollatz.Density
import TaoCollatz.PeriodicResidue
import Data.Nat
import Decidable.Equality

%default total

--------------------------------------------------------------------------------
-- Valuation lower bound from a 2-adic factorisation (odd cofactor not needed).
--------------------------------------------------------------------------------

||| If `3n+1 = 2^k * s` with `s >= 1` then `syrValuation n >= k`.  (Only the
||| divisibility `2^k | (3n+1)` matters; the cofactor need not be odd.)
public export
valuationGeFromFactor :
  (n : Nat) -> (k : Nat) -> (s : Nat) ->
  Leq (S Z) s ->
  plus (mult 3 n) 1 = mult (pow2 k) s ->
  Leq k (syrValuation n)
valuationGeFromFactor n k s spos heq =
  leqCastR (dropTimePowGe k s spos) (cong oddPartDropTime (sym heq))

--------------------------------------------------------------------------------
-- The residue `r_k < 2^k` with `3 r_k + 1 = 2^k * s_k` (`s_k >= 1`).
--------------------------------------------------------------------------------

||| `1 <= s + 3` for any `s`.
public export
posPlus3 : (s : Nat) -> Leq (S Z) (plus s 3)
posPlus3 s = leqTrans (LeqS LeqZ) (leqPlusExtraLeft s 3)

||| `isEven s = False` implies `isEven (s + 3) = True`.
public export
evenPlus3OfOdd : (s : Nat) -> isEven s = False -> isEven (plus s 3) = True
evenPlus3OfOdd s sodd =
  trans (cong isEven (plusCommutative s 3))
        (trans (isEvenSuccNot s) (cong not sodd))

||| **The tail residue.**  For every `k` there is a residue `r < 2^k` and a
||| cofactor `s >= 1` with `3 r + 1 = 2^k * s`.  Proved by induction on `k`,
||| peeling one power of two per step (halving the cofactor, correcting the
||| residue by `2^k` when the cofactor is odd).
public export
tailResidue :
  (k : Nat) ->
  (r : Nat ** (s : Nat ** (Leq (S Z) s, Leq (S r) (pow2 k),
                           plus (mult 3 r) 1 = mult (pow2 k) s)))
tailResidue Z = (0 ** (1 ** (leqRefl 1, leqRefl 1, Refl)))
tailResidue (S k) with (tailResidue k)
  _ | (r ** (s ** (spos, rlt, heq))) with (isEven s) proof ev
    _ | True =
      let s' : Nat
          s' = half s
          s'pos : Leq (S Z) s'
          s'pos = evenHalfPos s spos ev
          -- s = s' + s'
          seq : (s = plus s' s')
          seq = sym (evenHalf s ev)
          -- 3r+1 = 2^(S k) * s'
          factEq : (plus (mult 3 r) 1 = mult (pow2 (S k)) s')
          factEq =
            trans heq
              (trans (cong (mult (pow2 k)) seq)
                (trans (multDistributesOverPlusRight (pow2 k) s' s')
                       (sym (pow2SuccMult k s'))))
          rlt' : Leq (S r) (pow2 (S k))
          rlt' = leqTrans rlt (leqPlusExtraRight (pow2 k) (pow2 k))
      in (r ** (s' ** (s'pos, rlt', factEq)))
    _ | False =
      let r' : Nat
          r' = plus r (pow2 k)
          s'' : Nat
          s'' = half (plus s 3)
          evOdd : isEven (plus s 3) = True
          evOdd = evenPlus3OfOdd s ev
          s''pos : Leq (S Z) s''
          s''pos = evenHalfPos (plus s 3) (posPlus3 s) evOdd
          -- s + 3 = s'' + s''
          seq3 : (plus s 3 = plus s'' s'')
          seq3 = sym (evenHalf (plus s 3) evOdd)
          -- 3 r' + 1 = 2^k * (s + 3)
          stepA : (plus (mult 3 r') 1 = mult (pow2 k) (plus s 3))
          stepA =
            trans (cong (\z => plus z 1)
                    (multDistributesOverPlusRight 3 r (pow2 k)))
              (trans (sym (plusAssociative (mult 3 r) (mult 3 (pow2 k)) 1))
                (trans (cong (plus (mult 3 r)) (plusCommutative (mult 3 (pow2 k)) 1))
                  (trans (plusAssociative (mult 3 r) 1 (mult 3 (pow2 k)))
                    (trans (cong (\z => plus z (mult 3 (pow2 k))) heq)
                      (trans (cong (plus (mult (pow2 k) s))
                                (multCommutative 3 (pow2 k)))
                             (sym (multDistributesOverPlusRight (pow2 k) s 3)))))))
          -- 3 r' + 1 = 2^(S k) * s''
          factEq : (plus (mult 3 r') 1 = mult (pow2 (S k)) s'')
          factEq =
            trans stepA
              (trans (cong (mult (pow2 k)) seq3)
                (trans (multDistributesOverPlusRight (pow2 k) s'' s'')
                       (sym (pow2SuccMult k s''))))
          -- r' < 2^(S k)
          rlt' : Leq (S r') (pow2 (S k))
          rlt' = leqAdd rlt (leqRefl (pow2 k))
      in (r' ** (s'' ** (s''pos, rlt', factEq)))

--------------------------------------------------------------------------------
-- Decomposing `n` by its phase modulo the period.
--------------------------------------------------------------------------------

||| `natBeq a b = True` implies `a = b`.
public export
natBeqTrue : (a : Nat) -> (b : Nat) -> natBeq a b = True -> a = b
natBeqTrue Z Z _ = Refl
natBeqTrue Z (S b') h = absurd h
natBeqTrue (S a') Z h = absurd h
natBeqTrue (S a') (S b') h = cong S (natBeqTrue a' b' h)

||| `a /= b` implies `natBeq a b = False`.
public export
natBeqFalseOfNe : (a : Nat) -> (b : Nat) -> (a = b -> Void) -> natBeq a b = False
natBeqFalseOfNe a b ne with (natBeq a b) proof pb
  _ | True = absurd (ne (natBeqTrue a b pb))
  _ | False = Refl

||| In the wrap case the phase of the successor is zero.
public export
phZeroSucc :
  (p : Nat) -> (m : Nat) -> natBeq (phase p m) p = True ->
  phase p (S m) = Z
phZeroSucc p m h = rewrite h in Refl

||| In the non-wrap case the phase of the successor is a successor.
public export
phSuccStep :
  (p : Nat) -> (m : Nat) -> natBeq (phase p m) p = False ->
  phase p (S m) = S (phase p m)
phSuccStep p m h = rewrite h in Refl

||| Every `n` decomposes as `n = q * P + (phase p n)` for `P = S p`.
public export
phaseDecomp :
  (p : Nat) -> (n : Nat) ->
  (q : Nat ** n = plus (mult q (S p)) (phase p n))
phaseDecomp p Z = (Z ** Refl)
phaseDecomp p (S n') =
  case phaseDecomp p n' of
    (q ** eq) =>
      case decEq (phase p n') p of
        Yes yeq =>
          -- phase p n' = p, so phase p (S n') = 0 and S n' = (S q)*P
          let phEqTrue : (natBeq (phase p n') p = True)
              phEqTrue = trans (cong (\z => natBeq z p) yeq) (natBeqRefl p)
              phSucc : (phase p (S n') = Z)
              phSucc = phZeroSucc p n' phEqTrue
              lhs : (S n' = plus (mult q (S p)) (S p))
              lhs = trans (cong S eq)
                      (trans (cong (\z => S (plus (mult q (S p)) z)) yeq)
                             (plusSuccRightSucc (mult q (S p)) p))
              rhs : (plus (mult (S q) (S p)) (phase p (S n')) = plus (mult q (S p)) (S p))
              rhs = trans (cong (plus (mult (S q) (S p))) phSucc)
                      (trans (plusZeroRightNeutral (mult (S q) (S p)))
                             (plusCommutative (S p) (mult q (S p))))
          in (S q ** trans lhs (sym rhs))
        No nno =>
          -- phase p (S n') = S (phase p n')
          let phEqFalse : (natBeq (phase p n') p = False)
              phEqFalse = natBeqFalseOfNe (phase p n') p nno
              phSucc : (phase p (S n') = S (phase p n'))
              phSucc = phSuccStep p n' phEqFalse
          in (q ** trans (cong S eq)
                     (trans (plusSuccRightSucc (mult q (S p)) (phase p n'))
                            (cong (plus (mult q (S p))) (sym phSucc))))

--------------------------------------------------------------------------------
-- The residue class of valuation `>= k`, and its density `2^{-k}`.
--------------------------------------------------------------------------------

||| `pow2 k` as a successor: `pow2 k = S (pow2Pred k)`.
public export
pow2Pred : (k : Nat) -> (p : Nat ** pow2 k = S p)
pow2Pred k = case leqExists (pow2Positive k) of (d ** eq) => (d ** eq)

||| **Survival law, arithmetic form.**  For every `k`, the residue class
||| `n ≡ r_k (mod 2^k)` (with `r_k` the tail residue) consists entirely of `n`
||| with `syrValuation n >= k`, and it has natural density exactly `2^{-k}`.
|||
||| Concretely: `atRes p r` is the indicator of the class of period `S p = 2^k`;
|||   * membership forces valuation `>= k` (`valGe`);
|||   * over `q` full periods it has exactly `q` members (`density`).
public export
tailClass :
  (k : Nat) ->
  (p : Nat ** (r : Nat **
    ( pow2 k = S p
    , ((n : Nat) -> atRes p r n = True -> Leq k (syrValuation n))
    , ((q : Nat) -> count (\i => atRes p r i) (mult q (S p)) = q))))
tailClass k =
  case pow2Pred k of
    (p ** ppeq) =>
      case tailResidue k of
        (r ** (s ** (spos, rlt, heq))) =>
          let -- r < S p  (i.e. r < pow2 k)
              rltp : Leq (S r) (S p)
              rltp = leqCastR rlt ppeq
              valGe : (n : Nat) -> atRes p r n = True -> Leq k (syrValuation n)
              valGe n hn =
                case phaseDecomp p n of
                  (q ** deq) =>
                    let -- phase p n = r
                        pheq : (phase p n = r)
                        pheq = natBeqTrue (phase p n) r hn
                        -- n = q*(S p) + r
                        neq : (n = plus (mult q (S p)) r)
                        neq = trans deq (cong (plus (mult q (S p))) pheq)
                        -- 3n+1 = 2^k * (3q + s)
                        factEq : (plus (mult 3 n) 1 = mult (pow2 k) (plus (mult 3 q) s))
                        factEq = threeNPlusOneFactor k p s q r ppeq heq neq
                        cofPos : Leq (S Z) (plus (mult 3 q) s)
                        cofPos = leqTrans spos (leqPlusExtraLeft (mult 3 q) s)
                    in valuationGeFromFactor n k (plus (mult 3 q) s) cofPos factEq
              density : (q : Nat) -> count (\i => atRes p r i) (mult q (S p)) = q
              density q = atResDensity p r rltp q
          in (p ** (r ** (ppeq, valGe, density)))
  where
    ||| The key algebraic step: from `pow2 k = S p`, `3r+1 = 2^k s`, and
    ||| `n = q*(S p) + r`, derive `3n+1 = 2^k * (3q + s)`.
    threeNPlusOneFactor :
      (k : Nat) -> (p : Nat) -> (s : Nat) -> (q : Nat) -> (r : Nat) ->
      pow2 k = S p ->
      plus (mult 3 r) 1 = mult (pow2 k) s ->
      n = plus (mult q (S p)) r ->
      plus (mult 3 n) 1 = mult (pow2 k) (plus (mult 3 q) s)
    threeNPlusOneFactor k p s q r ppeq heq neq =
      -- 3n+1 = 3(q*(S p) + r) + 1 = 3*q*(S p) + (3r+1)
      --      = (3q)*2^k + 2^k*s = 2^k*(3q) + 2^k*s = 2^k*(3q + s)
      rewrite neq in
      rewrite multDistributesOverPlusRight 3 (mult q (S p)) r in
      rewrite sym (plusAssociative (mult 3 (mult q (S p))) (mult 3 r) 1) in
      rewrite heq in
      rewrite sym ppeq in
      rewrite multAssociative 3 q (pow2 k) in
      rewrite multCommutative (mult 3 q) (pow2 k) in
      sym (multDistributesOverPlusRight (pow2 k) (mult 3 q) s)

--------------------------------------------------------------------------------
-- Concrete sanity checks: the atoms `a >= 1` and `a >= 2`.
--------------------------------------------------------------------------------

||| `k = 1`: every odd number has valuation `>= 1` on the density-`1/2` class.
public export
tailClassOne :
  (p : Nat ** (r : Nat **
    ( pow2 1 = S p
    , ((n : Nat) -> atRes p r n = True -> Leq 1 (syrValuation n))
    , ((q : Nat) -> count (\i => atRes p r i) (mult q (S p)) = q))))
tailClassOne = tailClass 1

||| `k = 2`: valuation `>= 2` on a density-`1/4` residue class.
public export
tailClassTwo :
  (p : Nat ** (r : Nat **
    ( pow2 2 = S p
    , ((n : Nat) -> atRes p r n = True -> Leq 2 (syrValuation n))
    , ((q : Nat) -> count (\i => atRes p r i) (mult q (S p)) = q))))
tailClassTwo = tailClass 2
