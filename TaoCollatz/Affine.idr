module TaoCollatz.Affine

import Data.Nat
import TaoCollatz.Core
import TaoCollatz.Matrix

%default total

--------------------------------------------------------------------------------
-- Iteration 2 (safe algebraic domain: the affine monoid, embedded in 2x2
-- matrices).
--
-- An affine map `x |-> a*x + b` over `Nat` is recorded as `MkAffine a b`.  The
-- monoid of affine maps under composition embeds into the matrix monoid of
-- `TaoCollatz.Matrix` via the upper triangular matrix `[[a,b],[0,1]]`, and the
-- k-fold *power* of an affine map (a single matrix multiplication repeated)
-- computes the k-fold *iterate* of the underlying function.  That last fact,
-- `powAffIterate`, is the bridge that lets the Collatz/Syracuse acceleration
-- steps be studied as explicit matrix algebra rather than opaque recursion.
--
-- As with `Matrix`, the identity element is written with the literal
-- constructor `MkAffine 1 0` in the neutral laws (Idris2 does not delta-reduce
-- the nullary alias `affId`).
--------------------------------------------------------------------------------

public export
record Affine where
  constructor MkAffine
  coef, offset : Nat

public export
affId : Affine
affId = MkAffine 1 0

-- `applyAff (MkAffine a b) x = a*x + b`.
public export
applyAff : Affine -> Nat -> Nat
applyAff (MkAffine a b) x = a*x + b

-- Composition of affine maps: `composeAff f g` is "apply g, then f".
public export
composeAff : Affine -> Affine -> Affine
composeAff (MkAffine a1 b1) (MkAffine a2 b2) = MkAffine (a1*a2) (a1*b2 + b1)

public export
affEq : {c1,o1,c2,o2 : Nat} -> c1 = c2 -> o1 = o2 ->
  MkAffine c1 o1 = MkAffine c2 o2
affEq Refl Refl = Refl

--------------------------------------------------------------------------------
-- Composition really is function composition, and it is a monoid.
--------------------------------------------------------------------------------

public export
applyComposeAff : (f, g : Affine) -> (x : Nat) ->
  applyAff (composeAff f g) x = applyAff f (applyAff g x)
applyComposeAff (MkAffine a1 b1) (MkAffine a2 b2) x =
  rewrite multDistributesOverPlusRight a1 (a2*x) b2 in
  rewrite multAssociative a1 a2 x in
  rewrite plusAssociative (a1*a2*x) (a1*b2) b1 in
  Refl

composeAffOffset : (a1,b1,a2,b2,b3 : Nat) ->
  (a1*a2)*b3 + (a1*b2 + b1) = a1*(a2*b3 + b2) + b1
composeAffOffset a1 b1 a2 b2 b3 =
  rewrite multDistributesOverPlusRight a1 (a2*b3) b2 in
  rewrite multAssociative a1 a2 b3 in
  rewrite plusAssociative (a1*a2*b3) (a1*b2) b1 in
  Refl

public export
composeAffAssoc : (f, g, h : Affine) ->
  composeAff (composeAff f g) h = composeAff f (composeAff g h)
composeAffAssoc (MkAffine a1 b1) (MkAffine a2 b2) (MkAffine a3 b3) =
  affEq (sym (multAssociative a1 a2 a3)) (composeAffOffset a1 b1 a2 b2 b3)

public export
composeAffIdLeft : (f : Affine) -> composeAff (MkAffine 1 0) f = f
composeAffIdLeft (MkAffine a b) =
  affEq (multOneLeftNeutral a) (rewrite multOneLeftNeutral b in plusZeroRightNeutral b)

public export
composeAffIdRight : (f : Affine) -> composeAff f (MkAffine 1 0) = f
composeAffIdRight (MkAffine a b) =
  affEq (multOneRightNeutral a) (rewrite multZeroRightZero a in Refl)

public export
Semigroup Affine where
  (<+>) = composeAff

public export
Monoid Affine where
  neutral = affId

--------------------------------------------------------------------------------
-- The affine monoid embeds into the 2x2 matrix monoid as upper triangular
-- matrices `[[a,b],[0,1]]`.  The embedding is a monoid homomorphism.
--------------------------------------------------------------------------------

public export
affToMat : Affine -> Mat2
affToMat (MkAffine a b) = MkMat2 a b 0 1

public export
affToMatHom : (f, g : Affine) ->
  affToMat (composeAff f g) = matMul (affToMat f) (affToMat g)
affToMatHom (MkAffine a1 b1) (MkAffine a2 b2) =
  mat2Eq
    (rewrite multZeroRightZero b1 in sym (plusZeroRightNeutral (a1*a2)))
    (rewrite multOneRightNeutral b1 in Refl)
    Refl
    Refl

public export
affToMatId : affToMat (MkAffine 1 0) = MkMat2 1 0 0 1
affToMatId = Refl

--------------------------------------------------------------------------------
-- Powers of an affine map, and the central bridge: the k-th power of an affine
-- map, applied to x, equals the k-fold iterate of the underlying function.
--------------------------------------------------------------------------------

public export
powAff : Nat -> Affine -> Affine
powAff Z _ = MkAffine 1 0
powAff (S k) f = composeAff (powAff k f) f

public export
powAffIterate : (k : Nat) -> (f : Affine) -> (x : Nat) ->
  applyAff (powAff k f) x = iter k (applyAff f) x
powAffIterate Z f x = rewrite plusZeroRightNeutral x in multOneLeftNeutral x
powAffIterate (S k) f x =
  rewrite applyComposeAff (powAff k f) f x in
  powAffIterate k f (applyAff f x)

-- The power embeds to the matrix power (matrix multiplication repeated).
public export
matPow : Nat -> Mat2 -> Mat2
matPow Z _ = MkMat2 1 0 0 1
matPow (S k) m = matMul (matPow k m) m

public export
affToMatPow : (k : Nat) -> (f : Affine) ->
  affToMat (powAff k f) = matPow k (affToMat f)
affToMatPow Z f = affToMatId
affToMatPow (S k) f =
  rewrite affToMatHom (powAff k f) f in
  rewrite affToMatPow k f in
  Refl

--------------------------------------------------------------------------------
-- The Collatz/Syracuse odd-branch step `x |-> 3*x + 1` as an explicit affine
-- map / matrix, and the iterate theorem specialised to it.
--------------------------------------------------------------------------------

public export
threeXPlusOne : Nat -> Nat
threeXPlusOne x = 3*x + 1

public export
oddStepAff : Affine
oddStepAff = MkAffine 3 1

public export
oddStepMatrix : Mat2
oddStepMatrix = MkMat2 3 1 0 1

public export
applyOddStepAff : (x : Nat) -> applyAff (MkAffine 3 1) x = threeXPlusOne x
applyOddStepAff x = Refl

-- The k-fold odd step is computed by the k-th power of the fixed matrix
-- [[3,1],[0,1]] acting on the column vector (x, 1).
-- A generic congruence: `iter` respects pointwise equality of the step map.
-- This is the funext-free way to swap one representation of a step for another.
public export
iterExt : (k : Nat) -> (f, g : a -> a) -> ((y : a) -> f y = g y) ->
  (x : a) -> iter k f x = iter k g x
iterExt Z f g h x = Refl
iterExt (S k) f g h x =
  rewrite h x in iterExt k f g h (g x)

public export
oddStepPowIterate : (k : Nat) -> (x : Nat) ->
  applyAff (powAff k (MkAffine 3 1)) x = iter k (applyAff (MkAffine 3 1)) x
oddStepPowIterate k x = powAffIterate k (MkAffine 3 1) x

-- The matrix [[3,1],[0,1]] realises one odd step on the vector (x,1).
public export
oddStepMatrixAction : (x : Nat) ->
  applyMat (MkMat2 3 1 0 1) (x, 1) = (threeXPlusOne x, 1)
oddStepMatrixAction x = Refl

--------------------------------------------------------------------------------
-- Machine-checked examples.
--------------------------------------------------------------------------------

public export
powAffThreeTwoExample : applyAff (powAff 2 (MkAffine 3 1)) 1 = 13
powAffThreeTwoExample = Refl

public export
matPowExample : matPow 2 (MkMat2 3 1 0 1) = MkMat2 9 4 0 1
matPowExample = Refl
