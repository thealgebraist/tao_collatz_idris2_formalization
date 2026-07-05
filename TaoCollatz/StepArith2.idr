module TaoCollatz.StepArith2

-- Further elementary `Nat` arithmetic, used to discharge the *arithmetic
-- domination* reduction (Step 5 of `HoleProof`): from the drift
-- `8 * n <= 5 * S_n(y)` (the running valuation sum reaching rate `8/5`) and a
-- large enough time `n`, the contraction beats the growth,
-- `3^n * f(y) <= 2^{S_n(y)}`.
--
-- The mathematical crux is a Bernoulli-type inequality that turns the *strict*
-- single-block gap `3^5 = 243 < 256 = 2^8` into an eventually-dominating
-- exponential ratio: for every `c`, once `n >= 243 * c` we have
-- `243^n * c <= 256^n`.  Everything here is ordinary, total `Nat` arithmetic on
-- the project's `Leq`; there are no holes and no placeholders.

import TaoCollatz.Core
import TaoCollatz.TwoAdic
import TaoCollatz.Density
import TaoCollatz.StepArith
import Data.Nat

%default total

--------------------------------------------------------------------------------
-- Rearrangements and power laws.
--------------------------------------------------------------------------------

||| Rearrange a product of four factors.
public export
mult4Rearrange :
  (a : Nat) -> (b : Nat) -> (x : Nat) -> (y : Nat) ->
  mult (mult a b) (mult x y) = mult (mult a x) (mult b y)
mult4Rearrange a b x y =
  trans (sym (multAssociative a b (mult x y)))
    (trans (cong (mult a) (mulSwapMid b x y))
           (multAssociative a x (mult b y)))

||| `(a * b)^k = a^k * b^k`.
public export
natPowMulDist :
  (a : Nat) -> (b : Nat) -> (k : Nat) ->
  natPow (mult a b) k = mult (natPow a k) (natPow b k)
natPowMulDist a b Z = Refl
natPowMulDist a b (S k) =
  rewrite natPowMulDist a b k in
  mult4Rearrange a b (natPow a k) (natPow b k)

--------------------------------------------------------------------------------
-- Positivity facts.
--------------------------------------------------------------------------------

||| A power of a positive base is positive.
public export
natPowPosBase : (a' : Nat) -> (k : Nat) -> Leq (S Z) (natPow (S a') k)
natPowPosBase a' Z = LeqS LeqZ
natPowPosBase a' (S j) =
  leqTrans (natPowPosBase a' j)
           (leqPlusExtraRight (natPow (S a') j) (mult a' (natPow (S a') j)))

||| `a <= a^5`.
public export
leqBaseNatPow5 : (a : Nat) -> Leq a (natPow a 5)
leqBaseNatPow5 Z = LeqZ
leqBaseNatPow5 (S a') =
  leqCastL (sym (multOneRightNeutral (S a')))
           (leqMultLeft (S a') (natPowPosBase a' 4))

||| `x <= 243 * x` (a convenient concrete instance).
public export
leqSelf243 : (x : Nat) -> Leq x (mult 243 x)
leqSelf243 x = leqPlusExtraRight x (mult 242 x)

||| `x <= 243 * x^5`.
public export
fLeqG : (x : Nat) -> Leq x (mult 243 (natPow x 5))
fLeqG x = leqTrans (leqBaseNatPow5 x) (leqSelf243 (natPow x 5))

--------------------------------------------------------------------------------
-- Monotonicity of `pow2` in the exponent.
--------------------------------------------------------------------------------

public export
pow2ExpMono : {a : Nat} -> {b : Nat} -> Leq a b -> Leq (pow2 a) (pow2 b)
pow2ExpMono {a} {b} h =
  let (d ** eq) = leqExists h in
  rewrite eq in
  rewrite pow2AddLocal a d in
  leqCastL (sym (multOneRightNeutral (pow2 a)))
           (leqMultLeft (pow2 a) (pow2Positive d))

--------------------------------------------------------------------------------
-- Comparison, cancellation and strict power monotonicity.
--------------------------------------------------------------------------------

public export
notLeqSelfSucc : (x : Nat) -> Leq (S x) x -> Void
notLeqSelfSucc Z prf impossible
notLeqSelfSucc (S x) (LeqS p) = notLeqSelfSucc x p

public export
cmpNat : (a : Nat) -> (b : Nat) -> Either (Leq a b) (Leq (S b) a)
cmpNat Z b = Left LeqZ
cmpNat (S a) Z = Right (LeqS LeqZ)
cmpNat (S a) (S b) = case cmpNat a b of
  Left le => Left (LeqS le)
  Right gt => Right (LeqS gt)

public export
leqMultLeftCancel :
  (m : Nat) -> {x : Nat} -> {y : Nat} ->
  Leq (mult (S m) x) (mult (S m) y) -> Leq x y
leqMultLeftCancel m {x} {y} hyp =
  case cmpNat x y of
    Left le => le
    Right gt =>
      let h1 : Leq (mult (S m) (S y)) (mult (S m) x)
          h1 = leqMultLeft (S m) gt
          h2 : Leq (mult (S m) (S y)) (mult (S m) y)
          h2 = leqTrans h1 hyp
          h3 : Leq (plus (S m) (mult (S m) y)) (mult (S m) y)
          h3 = leqCastL (sym (multRightSuccPlus (S m) y)) h2
          h4 : Leq (S (mult (S m) y)) (plus (S m) (mult (S m) y))
          h4 = LeqS (leqPlusExtraLeft m (mult (S m) y))
          h5 : Leq (S (mult (S m) y)) (mult (S m) y)
          h5 = leqTrans h4 h3
      in void (notLeqSelfSucc (mult (S m) y) h5)

public export
strictPowMono :
  (k : Nat) -> {a : Nat} -> {b : Nat} ->
  Leq (S b) a -> Leq (S (natPow b (S k))) (natPow a (S k))
strictPowMono Z {a} {b} gt =
  rewrite multOneRightNeutral b in
  rewrite multOneRightNeutral a in
  gt
strictPowMono (S j) {a} {b} gt =
  let ih : Leq (S (natPow b (S j))) (natPow a (S j))
      ih = strictPowMono j gt
      y : Nat
      y = natPow b (S j)
      aLe : Leq (S Z) a
      aLe = leqTrans (LeqS LeqZ) gt
      bLeA : Leq b a
      bLeA = leqTrans (leqSuccRight b) gt
      hAY : Leq (mult b y) (mult a y)
      hAY = leqMultRight bLeA y
      plusStep : Leq (S (mult b y)) (plus a (mult a y))
      plusStep =
        leqTrans (LeqS hAY)
                 (leqAdd aLe (leqRefl (mult a y)))
      geStep : Leq (plus a (mult a y)) (mult a (natPow a (S j)))
      geStep =
        leqCastL (sym (multRightSuccPlus a y)) (leqMultLeft a ih)
  in leqTrans plusStep geStep

public export
powCancel :
  (k : Nat) -> {a : Nat} -> {b : Nat} ->
  Leq (natPow a (S k)) (natPow b (S k)) -> Leq a b
powCancel k {a} {b} hyp =
  case cmpNat a b of
    Left le => le
    Right gt =>
      let s : Leq (S (natPow b (S k))) (natPow b (S k))
          s = leqTrans (strictPowMono k gt) hyp
      in void (notLeqSelfSucc (natPow b (S k)) s)

--------------------------------------------------------------------------------
-- The Bernoulli-type exponential gap.
--------------------------------------------------------------------------------

-- Rearrangement of a sum of four atoms.
plusSwap4 :
  (a1 : Nat) -> (a2 : Nat) -> (a3 : Nat) -> (a4 : Nat) ->
  plus (plus a1 a2) (plus a3 a4) = plus (plus a1 (plus a3 a2)) a4
plusSwap4 a1 a2 a3 a4 =
  let innerEq : (plus a2 (plus a3 a4) = plus a3 (plus a2 a4))
      innerEq =
        trans (plusAssociative a2 a3 a4)
          (trans (cong (\z => plus z a4) (plusCommutative a2 a3))
                 (sym (plusAssociative a3 a2 a4)))
  in trans (sym (plusAssociative a1 a2 (plus a3 a4)))
       (trans (cong (plus a1) innerEq)
         (trans (cong (plus a1) (plusAssociative a3 a2 a4))
                (plusAssociative a1 (plus a3 a2) a4)))

-- The core one-step polynomial identity: `(a+d)(a+nd) = a(a+(n+1)d) + n d^2`.
coreEq :
  (a : Nat) -> (d : Nat) -> (n : Nat) ->
  mult (plus a d) (plus a (mult n d))
    = plus (mult a (plus a (mult (S n) d))) (mult n (mult d d))
coreEq a d n =
  let dsq : (mult d (mult n d) = mult n (mult d d))
      dsq =
        trans (multAssociative d n d)
          (trans (cong (\z => mult z d) (multCommutative d n))
                 (sym (multAssociative n d d)))
      mAY : (mult a (plus a (mult n d))
              = plus (mult a a) (mult a (mult n d)))
      mAY = multDistributesOverPlusRight a a (mult n d)
      mDY : (mult d (plus a (mult n d)) = plus (mult a d) (mult n (mult d d)))
      mDY =
        trans (multDistributesOverPlusRight d a (mult n d))
              (cong2 plus (multCommutative d a) dsq)
      rhsEq : (mult a (plus a (mult (S n) d))
                = plus (mult a a) (plus (mult a d) (mult a (mult n d))))
      rhsEq =
        trans (multDistributesOverPlusRight a a (mult (S n) d))
              (cong (plus (mult a a))
                    (multDistributesOverPlusRight a d (mult n d)))
  in trans (multDistributesOverPlusLeft a d (plus a (mult n d)))
       (trans (cong2 plus mAY mDY)
         (trans (plusSwap4 (mult a a) (mult a (mult n d))
                           (mult a d) (mult n (mult d d)))
                (cong (\z => plus z (mult n (mult d d))) (sym rhsEq))))

-- `a^n * (a + n d) <= a * (a + d)^n`.
bernoulli :
  (a : Nat) -> (d : Nat) -> (n : Nat) ->
  Leq (mult (natPow a n) (plus a (mult n d)))
      (mult a (natPow (plus a d) n))
bernoulli a d Z =
  rewrite plusZeroRightNeutral (plus a Z) in
  rewrite plusZeroRightNeutral a in
  rewrite multOneRightNeutral a in
  leqRefl a
bernoulli a d (S n) =
  let p : Nat
      p = natPow a n
      b : Nat
      b = plus a d
      q : Nat
      q = natPow b n
      x : Nat
      x = plus a (mult (S n) d)
      y : Nat
      y = plus a (mult n d)
      ih : Leq (mult p y) (mult a q)
      ih = bernoulli a d n
      coreIneq : Leq (mult a x) (mult b y)
      coreIneq =
        leqCastR (leqPlusExtraRight (mult a x) (mult n (mult d d)))
                 (sym (coreEq a d n))
      lhsEq : (mult (mult a p) x = mult p (mult a x))
      lhsEq = trans (sym (multAssociative a p x)) (mulSwapMid a p x)
      s1 : Leq (mult (mult a p) x) (mult p (mult b y))
      s1 = leqCastL lhsEq (leqMultLeft p coreIneq)
      s2 : Leq (mult p (mult b y)) (mult a (mult b q))
      s2 = leqCastL (mulSwapMid p b y)
             (leqCastR (leqMultLeft b ih) (mulSwapMid b a q))
  in leqTrans s1 s2

||| **Bernoulli gap (concrete).**  Once `n >= 243 * c`, the growth budget
||| `256^n` dominates `243^n * c`.
public export
bigPow243 :
  (c : Nat) -> (n : Nat) ->
  Leq (mult 243 c) n -> Leq (mult (natPow 243 n) c) (natPow 256 n)
bigPow243 c n hle =
  let h1 : Leq (mult 243 c) (plus 243 (mult n 13))
      h1 = leqTrans hle
             (leqTrans (leqSelfMult n 12)
                       (leqPlusExtraLeft 243 (mult n 13)))
      h2 : Leq (mult (natPow 243 n) (mult 243 c))
               (mult (natPow 243 n) (plus 243 (mult n 13)))
      h2 = leqMultLeft (natPow 243 n) h1
      h3 : Leq (mult (natPow 243 n) (plus 243 (mult n 13)))
               (mult 243 (natPow 256 n))
      h3 = bernoulli 243 13 n
      combined : Leq (mult (natPow 243 n) (mult 243 c))
                     (mult 243 (natPow 256 n))
      combined = leqTrans h2 h3
      rearr : (mult (natPow 243 n) (mult 243 c)
                = mult 243 (mult (natPow 243 n) c))
      rearr = mulSwapMid (natPow 243 n) 243 c
      cancelReady : Leq (mult 243 (mult (natPow 243 n) c))
                        (mult 243 (natPow 256 n))
      cancelReady = leqCastL (sym rearr) combined
  in leqMultLeftCancel 242 cancelReady

--------------------------------------------------------------------------------
-- The arithmetic domination lemma driving Step 5.
--------------------------------------------------------------------------------

||| **Step 5, arithmetic core.**  If `n >= 243 * f^5` and the running valuation
||| sum satisfies the drift `8 n <= 5 * sn`, then the contraction dominates the
||| growth: `3^n * f <= 2^{sn}`.
public export
contractionArith :
  (n : Nat) -> (fy : Nat) -> (sn : Nat) ->
  Leq (mult 243 (natPow fy 5)) n ->
  Leq (mult 8 n) (mult 5 sn) ->
  Leq (mult (natPow 3 n) fy) (pow2 sn)
contractionArith n fy sn hbig hdrift =
  let powEq : (natPow (natPow 3 n) 5 = natPow 243 n)
      powEq =
        trans (sym (powMulLaw 3 n 5))
          (trans (cong (natPow 3) (multCommutative n 5))
                 (powMulLaw 3 5 n))
      c1 : (natPow (mult (natPow 3 n) fy) 5
             = mult (natPow 243 n) (natPow fy 5))
      c1 =
        trans (natPowMulDist (natPow 3 n) fy 5)
              (cong (\z => mult z (natPow fy 5)) powEq)
      lhsLe : Leq (mult (natPow 243 n) (natPow fy 5)) (natPow 256 n)
      lhsLe = bigPow243 (natPow fy 5) n hbig
      stepPow256 : Leq (natPow (mult (natPow 3 n) fy) 5) (natPow 256 n)
      stepPow256 = leqCastL c1 lhsLe
      c256 : (natPow 256 n = pow2 (mult 8 n))
      c256 = sym (pow2MulLaw 8 n)
      stepPow8 : Leq (natPow (mult (natPow 3 n) fy) 5) (pow2 (mult 8 n))
      stepPow8 = leqCastR stepPow256 c256
      stepPow5sn : Leq (pow2 (mult 8 n)) (pow2 (mult 5 sn))
      stepPow5sn = pow2ExpMono hdrift
      c5sn : (pow2 (mult 5 sn) = natPow (pow2 sn) 5)
      c5sn = trans (cong pow2 (multCommutative 5 sn)) (pow2MulLaw sn 5)
      stepFinal : Leq (natPow (mult (natPow 3 n) fy) 5)
                      (natPow (pow2 sn) 5)
      stepFinal = leqCastR (leqTrans stepPow8 stepPow5sn) c5sn
  in powCancel 4 stepFinal
