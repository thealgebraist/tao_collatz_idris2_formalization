module TaoCollatz.OddStepClosed

import Data.Nat
import TaoCollatz.Core
import TaoCollatz.Matrix
import TaoCollatz.Affine

%default total

--------------------------------------------------------------------------------
-- Iteration 5 (explicit closed form of the odd-step powers).
--
-- The odd Collatz/Syracuse step `x |-> 3*x + 1` is the affine map `MkAffine 3 1`
-- (matrix `[[3,1],[0,1]]`).  Here we compute its k-th power in *closed form*:
--
--     [[3,1],[0,1]]^k = [[3^k, g k],[0,1]],   g k = (3^k - 1)/2,
--
-- where `g` is the subtraction-free integer sequence `g 0 = 0`,
-- `g (k+1) = 3^k + g k` (equivalently `g (k+1) = 3 * g k + 1`).  Consequently
-- the k-fold iterate of `3*x+1` is exactly `3^k * x + g k`.  Everything is a
-- total `Nat` computation: explicit and safe.
--------------------------------------------------------------------------------

-- 3^k, defined without the general `power` so it reduces cleanly.
public export
pow3 : Nat -> Nat
pow3 Z = 1
pow3 (S k) = 3 * pow3 k

-- The geometric-series offset g k = (3^k - 1)/2, defined with a subtraction-free
-- recurrence that matches how `composeAff` accumulates the offset.
public export
geom : Nat -> Nat
geom Z = Z
geom (S k) = pow3 k + geom k

-- Closed form of the affine power.
public export
oddPowClosed : (k : Nat) ->
  powAff k (MkAffine 3 1) = MkAffine (pow3 k) (geom k)
oddPowClosed Z = Refl
oddPowClosed (S k) =
  rewrite oddPowClosed k in
  affEq (multCommutative (pow3 k) 3) (multOneRight (pow3 k) `plusCong` Refl)
  where
    multOneRight : (n : Nat) -> n * 1 = n
    multOneRight = multOneRightNeutral
    plusCong : {a,b,c,d : Nat} -> a = c -> b = d -> a + b = c + d
    plusCong Refl Refl = Refl

-- Closed form of the underlying function iterate: (3x+1) iterated k times.
public export
oddPowApply : (k : Nat) -> (x : Nat) ->
  applyAff (powAff k (MkAffine 3 1)) x = pow3 k * x + geom k
oddPowApply k x = rewrite oddPowClosed k in Refl

-- The k-fold iterate of the bare function `\x => 3*x + 1`.
public export
iterThreeXClosed : (k : Nat) -> (x : Nat) ->
  iter k (applyAff (MkAffine 3 1)) x = pow3 k * x + geom k
iterThreeXClosed k x =
  trans (sym (powAffIterate k (MkAffine 3 1) x)) (oddPowApply k x)

-- Closed form of the matrix power.
public export
oddPowMatClosed : (k : Nat) ->
  matPow k (MkMat2 3 1 0 1) = MkMat2 (pow3 k) (geom k) 0 1
oddPowMatClosed k =
  trans (sym (affToMatPow k (MkAffine 3 1)))
        (cong affToMat (oddPowClosed k))

--------------------------------------------------------------------------------
-- Machine-checked examples.
--------------------------------------------------------------------------------

public export
geomExamples : (geom 1 = 1, geom 2 = 4, geom 3 = 13)
geomExamples = (Refl, Refl, Refl)

public export
oddPowMatExample : matPow 3 (MkMat2 3 1 0 1) = MkMat2 27 13 0 1
oddPowMatExample = Refl

public export
iterThreeXExample : iter 3 (applyAff (MkAffine 3 1)) 1 = 40
iterThreeXExample = Refl
