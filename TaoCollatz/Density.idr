module TaoCollatz.Density

-- A genuine, self-contained development of *natural density zero* subsets of
-- the natural numbers and the associated "almost all" notion, together with
-- the closure lemmas that a measure-of-smallness must satisfy.
--
-- This module is real mathematics: no placeholders, no `believe_me`, no
-- axioms; every definition is total and every lemma is proved from first
-- principles (the underlying counting function and elementary arithmetic).
--
-- Concretely, a set `S` of naturals is modelled by its indicator
-- `p : Nat -> Bool`, and
--
--   * `count p N` counts the members of `S` below `N`;
--   * `Negligible p` says the density of `S` is zero: for every precision
--     `1/(k+1)` there is a cutoff beyond which `count p N * (k+1) <= N`;
--   * `AlmostAll p` says the *complement* of `S` is negligible.
--
-- The results below (`negligibleMono`, `boundedNegligible`, `orNegligible`,
-- `almostAllMono`, `andAlmostAll`, ...) are exactly the closure properties the
-- paper's abstract "almost all" (`TaoCollatz.Large.AlmostAllOn`) is required to
-- have; this module realises them by a genuine density, giving §5 of the
-- tracking matrix concrete content.

import Data.Nat
import TaoCollatz.Core

%default total

--------------------------------------------------------------------------------
-- Elementary arithmetic on the project's `Leq`.
--------------------------------------------------------------------------------

public export
leqCastL : {a : Nat} -> {b : Nat} -> {c : Nat} -> a = b -> Leq b c -> Leq a c
leqCastL Refl h = h

public export
leqCastR : {a : Nat} -> {b : Nat} -> {c : Nat} -> Leq a b -> b = c -> Leq a c
leqCastR h Refl = h

public export
leqToLTE : {a : Nat} -> {b : Nat} -> Leq a b -> LTE a b
leqToLTE LeqZ = LTEZero
leqToLTE (LeqS h) = LTESucc (leqToLTE h)

public export
lteToLeq : {a : Nat} -> {b : Nat} -> LTE a b -> Leq a b
lteToLeq LTEZero = LeqZ
lteToLeq (LTESucc h) = LeqS (lteToLeq h)

public export
leqSuccRight : (n : Nat) -> Leq n (S n)
leqSuccRight Z = LeqZ
leqSuccRight (S n) = LeqS (leqSuccRight n)

public export
addLeftMono : (c : Nat) -> Leq x y -> Leq (plus c x) (plus c y)
addLeftMono Z h = h
addLeftMono (S c) h = LeqS (addLeftMono c h)

public export
leqPlusExtraLeft : (n : Nat) -> (c : Nat) -> Leq c (plus n c)
leqPlusExtraLeft Z c = leqRefl c
leqPlusExtraLeft (S n) c = leqTrans (leqPlusExtraLeft n c) (leqSuccRight (plus n c))

public export
leqPlusExtraRight : (a : Nat) -> (d : Nat) -> Leq a (plus a d)
leqPlusExtraRight Z d = LeqZ
leqPlusExtraRight (S a) d = LeqS (leqPlusExtraRight a d)

public export
leqAdd : {a : Nat} -> {b : Nat} -> {c : Nat} -> {d : Nat} ->
         Leq a b -> Leq c d -> Leq (plus a c) (plus b d)
leqAdd ab cd = lteToLeq (plusLteMonotone (leqToLTE ab) (leqToLTE cd))

public export
leqMultRight : Leq a b -> (c : Nat) -> Leq (mult a c) (mult b c)
leqMultRight LeqZ c = LeqZ
leqMultRight (LeqS ab) c = addLeftMono c (leqMultRight ab c)

-- A + B rearrangement used to split a "doubled" bound.
public export
plusRearrange :
  (a : Nat) -> (b : Nat) -> (c : Nat) -> (d : Nat) ->
  plus (plus a b) (plus c d) = plus (plus a c) (plus b d)
plusRearrange a b c d =
  rewrite plusAssociative (plus a b) c d in
  rewrite sym (plusAssociative a b c) in
  rewrite plusCommutative b c in
  rewrite plusAssociative a c b in
  rewrite sym (plusAssociative (plus a c) b d) in
  Refl

-- A cheap "double" that reduces nicely, letting us cancel a factor of two.
public export
dbl : Nat -> Nat
dbl Z = Z
dbl (S n) = S (S (dbl n))

public export
twoSk : (k : Nat) -> plus (S k) (S k) = S (S (plus k k))
twoSk k = cong S (sym (plusSuccRightSucc k k))

public export
dblEq : (n : Nat) -> dbl n = plus n n
dblEq Z = Refl
dblEq (S n) = rewrite dblEq n in sym (twoSk n)

public export
leqHalfDbl : {m : Nat} -> {n : Nat} -> Leq (dbl m) (dbl n) -> Leq m n
leqHalfDbl {m = Z} _ = LeqZ
leqHalfDbl {m = S _} {n = Z} h impossible
leqHalfDbl {m = S m'} {n = S n'} (LeqS (LeqS h)) = LeqS (leqHalfDbl h)

public export
leqHalf : {m : Nat} -> {n : Nat} -> Leq (plus m m) (plus n n) -> Leq m n
leqHalf {m} {n} h = leqHalfDbl (rewrite dblEq m in rewrite dblEq n in h)

public export
combineHalves :
  {x : Nat} -> {y : Nat} -> {bigN : Nat} ->
  Leq (plus x x) bigN -> Leq (plus y y) bigN -> Leq (plus x y) bigN
combineHalves {x} {y} hx hy =
  leqHalf (rewrite sym (plusRearrange x x y y) in leqAdd hx hy)

public export
leqSelfMult : (b : Nat) -> (k : Nat) -> Leq b (mult b (S k))
leqSelfMult Z k = LeqZ
leqSelfMult (S b) k =
  LeqS (leqTrans (leqSelfMult b k) (leqPlusExtraLeft k (mult b (S k))))

public export
leqExists : {a : Nat} -> {c : Nat} -> Leq a c -> (d : Nat ** c = plus a d)
leqExists {a = Z} {c} LeqZ = (c ** Refl)
leqExists {a = S a'} {c = S c'} (LeqS h) =
  let (d ** eq) = leqExists h in (d ** cong S eq)

public export
maxN : Nat -> Nat -> Nat
maxN Z b = b
maxN (S a) Z = S a
maxN (S a) (S b) = S (maxN a b)

public export
leqMaxL : (a : Nat) -> (b : Nat) -> Leq a (maxN a b)
leqMaxL Z b = LeqZ
leqMaxL (S a) Z = leqRefl (S a)
leqMaxL (S a) (S b) = LeqS (leqMaxL a b)

public export
leqMaxR : (a : Nat) -> (b : Nat) -> Leq b (maxN a b)
leqMaxR Z b = leqRefl b
leqMaxR (S a) Z = LeqZ
leqMaxR (S a) (S b) = LeqS (leqMaxR a b)

--------------------------------------------------------------------------------
-- Counting membership below a bound.
--------------------------------------------------------------------------------

public export
indicator : Bool -> Nat
indicator True = S Z
indicator False = Z

||| `count p N` = number of `n < N` with `p n = True`.
public export
count : (Nat -> Bool) -> Nat -> Nat
count p Z = Z
count p (S k) = plus (indicator (p k)) (count p k)

public export
indicatorMono :
  (b1 : Bool) -> (b2 : Bool) ->
  (b1 = True -> b2 = True) ->
  Leq (indicator b1) (indicator b2)
indicatorMono False _ _ = LeqZ
indicatorMono True True _ = LeqS LeqZ
indicatorMono True False sub = absurd (sub Refl)

public export
indicatorOr :
  (b1 : Bool) -> (b2 : Bool) ->
  Leq (indicator (b1 || b2)) (plus (indicator b1) (indicator b2))
indicatorOr True b2 = LeqS LeqZ
indicatorOr False b2 = leqRefl (indicator b2)

public export
countMono :
  {p : Nat -> Bool} -> {q : Nat -> Bool} ->
  ((n : Nat) -> p n = True -> q n = True) ->
  (bigN : Nat) ->
  Leq (count p bigN) (count q bigN)
countMono sub Z = LeqZ
countMono {p} {q} sub (S k) =
  leqAdd (indicatorMono (p k) (q k) (sub k)) (countMono sub k)

public export
countLeN : (p : Nat -> Bool) -> (bigN : Nat) -> Leq (count p bigN) bigN
countLeN p Z = LeqZ
countLeN p (S k) with (p k)
  _ | True = LeqS (countLeN p k)
  _ | False = leqTrans (countLeN p k) (leqSuccRight k)

public export
countOrLe :
  (p : Nat -> Bool) -> (q : Nat -> Bool) -> (bigN : Nat) ->
  Leq (count (\n => p n || q n) bigN) (plus (count p bigN) (count q bigN))
countOrLe p q Z = LeqZ
countOrLe p q (S k) =
  leqCastR
    (leqAdd (indicatorOr (p k) (q k)) (countOrLe p q k))
    (plusRearrange (indicator (p k)) (indicator (q k))
                   (count p k) (count q k))

-- `count` is unchanged once we pass the last index at which `p` is true.
public export
countBeyond :
  (p : Nat -> Bool) -> (b : Nat) ->
  ((n : Nat) -> Leq b n -> p n = False) ->
  (d : Nat) ->
  count p (plus b d) = count p b
countBeyond p b hFalse Z = rewrite plusZeroRightNeutral b in Refl
countBeyond p b hFalse (S d) =
  rewrite sym (plusSuccRightSucc b d) in
  rewrite hFalse (plus b d) (leqPlusExtraRight b d) in
  countBeyond p b hFalse d

-- The scaling factor `c * (S(S(2j)))` splits as `c*(Sj) + c*(Sj)`.
public export
factorDouble :
  (c : Nat) -> (j : Nat) ->
  mult c (S (S (plus j j))) = plus (mult c (S j)) (mult c (S j))
factorDouble c j =
  rewrite sym (twoSk j) in multDistributesOverPlusRight c (S j) (S j)

--------------------------------------------------------------------------------
-- Natural density zero, and the derived "almost all".
--------------------------------------------------------------------------------

||| `Negligible p`: the set with indicator `p` has natural density zero.  For
||| every precision index `k` there is a cutoff `n0` beyond which the count of
||| members below `N`, scaled by `k+1`, is at most `N` — i.e. the density is
||| below `1/(k+1)` for every `k`.
public export
Negligible : (Nat -> Bool) -> Type
Negligible p =
  (k : Nat) ->
  (n0 : Nat **
    ((bigN : Nat) -> Leq n0 bigN -> Leq (mult (count p bigN) (S k)) bigN))

public export
negligibleMono :
  {p : Nat -> Bool} -> {q : Nat -> Bool} ->
  ((n : Nat) -> q n = True -> p n = True) ->
  Negligible p -> Negligible q
negligibleMono sub negP k =
  let (n0 ** prf) = negP k in
  (n0 ** \bigN, big =>
    leqTrans (leqMultRight (countMono sub bigN) (S k)) (prf bigN big))

-- A bounded (hence finite) set is negligible.
public export
boundedNegligible :
  (p : Nat -> Bool) -> (b : Nat) ->
  ((n : Nat) -> Leq b n -> p n = False) ->
  Negligible p
boundedNegligible p b hFalse k =
  (mult b (S k) ** \bigN, big =>
    let bLeBig = leqTrans (leqSelfMult b k) big in
    case leqExists bLeBig of
      (d ** eq) =>
        let stable : (count p bigN = count p b)
            stable = trans (cong (count p) eq) (countBeyond p b hFalse d)
            cntLeB : Leq (count p bigN) b
            cntLeB = leqCastL stable (countLeN p b)
        in leqTrans (leqMultRight cntLeB (S k)) big)

public export
negligibleFalse : Negligible (\_ => False)
negligibleFalse = boundedNegligible (\_ => False) Z (\n, _ => Refl)

-- Density zero, doubled: from `Negligible p` extract the sharper cutoff giving
-- `2 * (count * (k+1)) <= N`, in the split form `X + X <= N`.
public export
negDouble :
  {p : Nat -> Bool} -> Negligible p -> (k : Nat) ->
  (n0 : Nat **
    ((bigN : Nat) -> Leq n0 bigN ->
      Leq (plus (mult (count p bigN) (S k)) (mult (count p bigN) (S k))) bigN))
negDouble {p} neg k =
  let (n0 ** pf) = neg (S (plus k k)) in
  (n0 ** \bigN, big =>
    leqCastL (sym (factorDouble (count p bigN) k)) (pf bigN big))

-- The union of two negligible sets is negligible.
public export
orNegligible :
  {p : Nat -> Bool} -> {q : Nat -> Bool} ->
  Negligible p -> Negligible q -> Negligible (\n => p n || q n)
orNegligible {p} {q} negP negQ k =
  let (np ** pf) = negDouble negP k
      (nq ** qf) = negDouble negQ k
  in (maxN np nq ** \bigN, big =>
       let hp = pf bigN (leqTrans (leqMaxL np nq) big)
           hq = qf bigN (leqTrans (leqMaxR np nq) big)
           half : Leq (plus (mult (count p bigN) (S k)) (mult (count q bigN) (S k))) bigN
           half = combineHalves hp hq
           step1 :
             Leq (mult (count (\n => p n || q n) bigN) (S k))
                 (mult (plus (count p bigN) (count q bigN)) (S k))
           step1 = leqMultRight (countOrLe p q bigN) (S k)
           step2 : Leq (mult (plus (count p bigN) (count q bigN)) (S k)) bigN
           step2 =
             leqCastL
               (multDistributesOverPlusLeft (count p bigN) (count q bigN) (S k))
               half
       in leqTrans step1 step2)

--------------------------------------------------------------------------------
-- "Almost all": the complement is negligible.
--------------------------------------------------------------------------------

public export
AlmostAll : (Nat -> Bool) -> Type
AlmostAll p = Negligible (\n => not (p n))

public export
notSubset :
  (b1 : Bool) -> (b2 : Bool) ->
  (b1 = True -> b2 = True) ->
  (not b2 = True -> not b1 = True)
notSubset False b2 _ _ = Refl
notSubset True True _ nb = nb
notSubset True False sub _ = absurd (sub Refl)

-- Almost-all is closed under passing to a larger (superset) predicate.
public export
almostAllMono :
  {p : Nat -> Bool} -> {q : Nat -> Bool} ->
  ((n : Nat) -> p n = True -> q n = True) ->
  AlmostAll p -> AlmostAll q
almostAllMono {p} {q} sub ap =
  negligibleMono (\n => notSubset (p n) (q n) (sub n)) ap

public export
almostAllTrue : AlmostAll (\_ => True)
almostAllTrue = negligibleFalse

public export
deMorganAnd : (a : Bool) -> (b : Bool) -> not (a && b) = (not a || not b)
deMorganAnd True b = Refl
deMorganAnd False b = Refl

-- Almost-all is closed under (finite) intersection.
public export
andAlmostAll :
  {p : Nat -> Bool} -> {q : Nat -> Bool} ->
  AlmostAll p -> AlmostAll q -> AlmostAll (\n => p n && q n)
andAlmostAll {p} {q} ap aq =
  negligibleMono
    (\n, h => trans (sym (deMorganAnd (p n) (q n))) h)
    (orNegligible ap aq)
