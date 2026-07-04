module TaoCollatz.Determinant

import Data.Nat
import TaoCollatz.Core
import TaoCollatz.Matrix
import TaoCollatz.Affine
import TaoCollatz.OddStepClosed
import TaoCollatz.Algebra

%default total

--------------------------------------------------------------------------------
-- Iteration 6 (the determinant homomorphism, and (Nat, *) as a monoid).
--
-- The affine maps of iteration 2 are exactly the upper triangular matrices
-- `[[a,b],[0,1]]`, whose determinant is `a` (no subtraction needed: `a*1 -
-- b*0 = a`).  The determinant is a *monoid homomorphism* from the affine
-- monoid to the multiplicative monoid `(Nat, *, 1)`, and on the odd step it
-- recovers the growth factor: `det([[3,1],[0,1]]^k) = 3^k`.  This packages the
-- multiplicative "size" of a Collatz acceleration as a clean group-theoretic
-- invariant, unified with the `MonoidStr` interface of iteration 4.
--------------------------------------------------------------------------------

-- Determinant of the affine matrix [[a,b],[0,1]].
public export
affDet : Affine -> Nat
affDet (MkAffine a b) = a

-- The (1,1) entry of the embedded matrix is the determinant.
public export
affDetIsMatEntry : (f : Affine) -> affDet f = m11 (affToMat f)
affDetIsMatEntry (MkAffine a b) = Refl

public export
affDetId : affDet (MkAffine 1 0) = 1
affDetId = Refl

-- Multiplicativity: det(f . g) = det f * det g.
public export
affDetHom : (f, g : Affine) -> affDet (composeAff f g) = affDet f * affDet g
affDetHom (MkAffine a1 b1) (MkAffine a2 b2) = Refl

--------------------------------------------------------------------------------
-- (Nat, *, 1) as an instance of the unified monoid interface.
--------------------------------------------------------------------------------

public export
natMultMonoid : MonoidStr Nat
natMultMonoid =
  MkMonoidStr (*) 1
    (\x, y, z => sym (multAssociative x y z))
    (\x => multOneLeftNeutral x)
    (\x => multOneRightNeutral x)

--------------------------------------------------------------------------------
-- Powers: det(f^k) = (det f)^k, and on the odd step this is 3^k.
--------------------------------------------------------------------------------

public export
natPow : Nat -> Nat -> Nat
natPow Z _ = 1
natPow (S k) b = natPow k b * b

public export
affDetPow : (k : Nat) -> (f : Affine) -> affDet (powAff k f) = natPow k (affDet f)
affDetPow Z f = Refl
affDetPow (S k) f =
  rewrite affDetHom (powAff k f) f in
  rewrite affDetPow k f in
  Refl

-- On the odd step the determinant is the growth factor 3^k (via the closed form
-- of iteration 5).
public export
oddStepDet : (k : Nat) -> affDet (powAff k (MkAffine 3 1)) = pow3 k
oddStepDet k = cong affDet (oddPowClosed k)

-- Consistency of the two power notions on the odd step: natPow k 3 = 3^k.
public export
natPowThreeIsPow3 : (k : Nat) -> natPow k 3 = pow3 k
natPowThreeIsPow3 k =
  trans (sym (affDetPow k (MkAffine 3 1))) (oddStepDet k)

--------------------------------------------------------------------------------
-- Machine-checked examples.
--------------------------------------------------------------------------------

public export
affDetExample : affDet (composeAff (MkAffine 3 1) (MkAffine 3 1)) = 9
affDetExample = Refl

public export
oddStepDetExample : affDet (powAff 4 (MkAffine 3 1)) = 81
oddStepDetExample = oddStepDet 4
