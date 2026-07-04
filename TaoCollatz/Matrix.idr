module TaoCollatz.Matrix

import Data.Nat
import TaoCollatz.Core

%default total

--------------------------------------------------------------------------------
-- Iteration 1 (safe algebraic domain: 2x2 matrices over Nat).
--
-- The Collatz/Syracuse acceleration steps are affine maps `x |-> a*x + b`, and
-- the composition of affine maps is *exactly* multiplication of the upper
-- triangular matrices `[[a,b],[0,1]]`.  This module builds that carrier ---
-- honest, fully explicit 2x2 matrices over `Nat` --- and proves it is a monoid
-- (associative multiplication with a two-sided identity) plus a monoid action on
-- column vectors.  Everything is a total term over `Nat`; there is no
-- `believe_me`, no `Integer` primitive black boxes, and no axioms, so the
-- algebra is as "safe" and explicit as possible.
--
-- Note on the identity element: Idris2 does not delta-reduce nullary top-level
-- definitions during conversion checking, so the neutral laws are stated with
-- the literal constructor `MkMat2 1 0 0 1` (which reduces under `matMul`); the
-- named value `idMat` is provided for readability at the value level.
--------------------------------------------------------------------------------

public export
record Mat2 where
  constructor MkMat2
  m11, m12, m21, m22 : Nat

public export
idMat : Mat2
idMat = MkMat2 1 0 0 1

public export
matMul : Mat2 -> Mat2 -> Mat2
matMul (MkMat2 a11 a12 a21 a22) (MkMat2 b11 b12 b21 b22) =
  MkMat2
    (a11*b11 + a12*b21) (a11*b12 + a12*b22)
    (a21*b11 + a22*b21) (a21*b12 + a22*b22)

--------------------------------------------------------------------------------
-- Entrywise congruence and the two purely additive/multiplicative helpers that
-- carry all of the ring bookkeeping.
--------------------------------------------------------------------------------

public export
mat2Eq :
  {e11,e12,e21,e22,f11,f12,f21,f22 : Nat} ->
  e11 = f11 -> e12 = f12 -> e21 = f21 -> e22 = f22 ->
  MkMat2 e11 e12 e21 e22 = MkMat2 f11 f12 f21 f22
mat2Eq Refl Refl Refl Refl = Refl

-- (a + b) + (c + d) = (a + c) + (b + d): the additive rearrangement behind
-- every entry of the associativity law.
public export
plusRearrange : (a,b,c,d : Nat) -> (a + b) + (c + d) = (a + c) + (b + d)
plusRearrange a b c d =
  rewrite sym (plusAssociative a b (c + d)) in
  rewrite plusAssociative b c d in
  rewrite plusCommutative b c in
  rewrite sym (plusAssociative c b d) in
  rewrite plusAssociative a c (b + d) in
  Refl

-- The single entrywise identity behind matrix-multiplication associativity:
-- the (i,j) entry of (A B) C equals the (i,j) entry of A (B C).
public export
genAssocEntry : (p,q,x,y,z,w,u,v : Nat) ->
  (p*x + q*y)*u + (p*z + q*w)*v = p*(x*u + z*v) + q*(y*u + w*v)
genAssocEntry p q x y z w u v =
  rewrite multDistributesOverPlusLeft (p*x) (q*y) u in
  rewrite multDistributesOverPlusLeft (p*z) (q*w) v in
  rewrite multDistributesOverPlusRight p (x*u) (z*v) in
  rewrite multDistributesOverPlusRight q (y*u) (w*v) in
  rewrite sym (multAssociative p x u) in
  rewrite sym (multAssociative q y u) in
  rewrite sym (multAssociative p z v) in
  rewrite sym (multAssociative q w v) in
  plusRearrange (p*(x*u)) (q*(y*u)) (p*(z*v)) (q*(w*v))

--------------------------------------------------------------------------------
-- Monoid laws.
--------------------------------------------------------------------------------

public export
matMulAssoc : (a,b,c : Mat2) -> matMul (matMul a b) c = matMul a (matMul b c)
matMulAssoc (MkMat2 a11 a12 a21 a22) (MkMat2 b11 b12 b21 b22) (MkMat2 c11 c12 c21 c22) =
  mat2Eq
    (genAssocEntry a11 a12 b11 b21 b12 b22 c11 c21)
    (genAssocEntry a11 a12 b11 b21 b12 b22 c12 c22)
    (genAssocEntry a21 a22 b11 b21 b12 b22 c11 c21)
    (genAssocEntry a21 a22 b11 b21 b12 b22 c12 c22)

idEntryA : (x,y : Nat) -> 1*x + 0*y = x
idEntryA x y = rewrite multOneLeftNeutral x in plusZeroRightNeutral x

idEntryB : (x,y : Nat) -> 0*x + 1*y = y
idEntryB x y = multOneLeftNeutral y

idEntryC : (x,y : Nat) -> x*1 + y*0 = x
idEntryC x y =
  rewrite multOneRightNeutral x in
  rewrite multZeroRightZero y in
  plusZeroRightNeutral x

idEntryD : (x,y : Nat) -> x*0 + y*1 = y
idEntryD x y = rewrite multZeroRightZero x in multOneRightNeutral y

public export
matMulIdLeft : (a : Mat2) -> matMul (MkMat2 1 0 0 1) a = a
matMulIdLeft (MkMat2 a11 a12 a21 a22) =
  mat2Eq (idEntryA a11 a21) (idEntryA a12 a22) (idEntryB a11 a21) (idEntryB a12 a22)

public export
matMulIdRight : (a : Mat2) -> matMul a (MkMat2 1 0 0 1) = a
matMulIdRight (MkMat2 a11 a12 a21 a22) =
  mat2Eq (idEntryC a11 a12) (idEntryD a11 a12) (idEntryC a21 a22) (idEntryD a21 a22)

--------------------------------------------------------------------------------
-- Standard-library interface instances, so the matrix carrier joins the shared
-- algebraic vocabulary (Semigroup/Monoid) used across the ecosystem.  The
-- verified laws above certify these instances really are a monoid.
--------------------------------------------------------------------------------

public export
Semigroup Mat2 where
  (<+>) = matMul

public export
Monoid Mat2 where
  neutral = idMat

--------------------------------------------------------------------------------
-- The monoid action on column vectors `(x, y)^T`, and the fact that it is an
-- action: applying a product is applying the factors in turn.  This is the
-- clean, subtraction-free way to see a matrix "act", and it is exactly what
-- turns matrix multiplication into function composition of affine maps.
--------------------------------------------------------------------------------

public export
applyMat : Mat2 -> (Nat, Nat) -> (Nat, Nat)
applyMat (MkMat2 a11 a12 a21 a22) (x, y) = (a11*x + a12*y, a21*x + a22*y)

public export
applyMatId : (v : (Nat, Nat)) -> applyMat (MkMat2 1 0 0 1) v = v
applyMatId (x, y) =
  rewrite multOneLeftNeutral x in
  rewrite multOneLeftNeutral y in
  rewrite plusZeroRightNeutral x in
  Refl

public export
applyMatMul : (a, b : Mat2) -> (v : (Nat, Nat)) ->
  applyMat (matMul a b) v = applyMat a (applyMat b v)
applyMatMul (MkMat2 a11 a12 a21 a22) (MkMat2 b11 b12 b21 b22) (x, y) =
  mkPairEq
    (genAssocEntry a11 a12 b11 b21 b12 b22 x y)
    (genAssocEntry a21 a22 b11 b21 b12 b22 x y)
  where
    mkPairEq : {p,q,r,s : Nat} -> p = r -> q = s -> (p, q) = (r, s)
    mkPairEq Refl Refl = Refl

--------------------------------------------------------------------------------
-- Machine-checked sanity examples.
--------------------------------------------------------------------------------

public export
matMulExample : matMul (MkMat2 3 1 0 1) (MkMat2 3 1 0 1) = MkMat2 9 4 0 1
matMulExample = Refl

public export
applyMatExample : applyMat (MkMat2 3 1 0 1) (5, 1) = (16, 1)
applyMatExample = Refl
