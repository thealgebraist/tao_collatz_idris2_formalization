module TaoCollatz.MatrixDynamics

import TaoCollatz.Dynamics
import TaoCollatz.DynamicsExtra
import TaoCollatz.Parity
import TaoCollatz.Matrix
import TaoCollatz.Affine

%default total

--------------------------------------------------------------------------------
-- Iteration 7 (unifying the algebra with the concrete dynamics).
--
-- Iterations 1-6 built the matrix / affine / parity algebra abstractly.  This
-- module ties it back to the actual `Col` and `Syr` maps of the development:
--
--   * one odd Collatz step *is* the affine map `MkAffine 3 1` (matrix
--     `[[3,1],[0,1]]`) applied to the value;
--   * that step, on the column vector `(n, 1)`, *is* the matrix action
--     `applyMat [[3,1],[0,1]]`;
--   * the Syracuse step is the odd part of that same affine image.
--
-- The branch is selected by the parity *group element* `parityOf n`, so the
-- concrete dynamics is now expressed entirely through the safe algebraic layer.
--------------------------------------------------------------------------------

-- One odd Collatz step equals the affine action `x |-> 3*x + 1`.
public export
colOddAffine : (n : Nat) -> isEven n = False ->
  Col (MkPos n) = MkPos (applyAff (MkAffine 3 1) n)
colOddAffine n h = colOddStep n h

-- The same, selected by the parity group element.
public export
colOddAffineParity : (n : Nat) -> parityOf n = Odd ->
  Col (MkPos n) = MkPos (applyAff (MkAffine 3 1) n)
colOddAffineParity n h = colOddParity n h

-- The odd Collatz step realised as the 2x2 matrix action on the column vector
-- (n, 1): the first coordinate is the new value, the second stays 1.
public export
colOddMatrixAction : (n : Nat) -> parityOf n = Odd ->
  (posValue (Col (MkPos n)), 1) = applyMat (MkMat2 3 1 0 1) (n, 1)
colOddMatrixAction n h =
  rewrite colOddParity n h in
  sym (oddStepMatrixAction n)

-- The Syracuse step is the odd part of the affine image `3*n + 1`.
public export
syrIsOddPartOfAffine : (n : Nat) ->
  Syr (MkOddPos n) = MkOddPos (oddFactor (applyAff (MkAffine 3 1) n))
syrIsOddPartOfAffine n = Refl

-- An even Collatz step is the halving branch, selected by `parityOf n = Even`.
public export
colEvenHalf : (n : Nat) -> parityOf n = Even ->
  Col (MkPos n) = MkPos (half n)
colEvenHalf n h = colEvenParity n h

--------------------------------------------------------------------------------
-- Machine-checked examples tying concrete steps to the matrix action.
--------------------------------------------------------------------------------

-- 7 is odd, so Col 7 = 22 and the matrix action on (7,1) gives (22,1).
public export
colSevenMatrixExample :
  (posValue (Col (MkPos 7)), 1) = applyMat (MkMat2 3 1 0 1) (7, 1)
colSevenMatrixExample = Refl

-- Syr 7 = oddPart 22 = 11.
public export
syrSevenAffineExample :
  Syr (MkOddPos 7) = MkOddPos (oddFactor (applyAff (MkAffine 3 1) 7))
syrSevenAffineExample = Refl
