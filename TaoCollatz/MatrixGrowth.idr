module TaoCollatz.MatrixGrowth

import Data.Nat
import TaoCollatz.Core
import TaoCollatz.Affine
import TaoCollatz.OddStepClosed

%default total

--------------------------------------------------------------------------------
-- Iteration 8 (capstone: matrix growth in the height ordering).
--
-- The determinant of the odd-step matrix `[[3,1],[0,1]]` is 3 > 1, so its k-th
-- power scales by `3^k >= 1`.  This module cashes that out in the *height*
-- ordering `Core.Leq` used by `EventuallyBelow`: the pure odd (tripling)
-- iteration `x |-> 3*x + 1` is non-decreasing, and strictly increasing once a
-- step is taken.  Concretely, from the closed form
-- `iter k (3x+1) = 3^k * x + g k` (iteration 5) and `3^k >= 1`, the height
-- never drops.  This is the precise, matrix-certified reason the Collatz map
-- *needs* its halving steps to ever descend --- the algebraic content behind
-- the paper's first-passage analysis, stated in the safe `Nat`/`Leq` domain.
--------------------------------------------------------------------------------

public export
leqPlusRight : (x, m : Nat) -> Leq x (x + m)
leqPlusRight Z m = LeqZ
leqPlusRight (S x) m = LeqS (leqPlusRight x m)

public export
leqMulPosLeft : (c, x : Nat) -> Leq 1 c -> Leq x (c * x)
leqMulPosLeft Z x prf impossible
leqMulPosLeft (S c') x _ = leqPlusRight x (mult c' x)

public export
pow3Pos : (k : Nat) -> Leq 1 (pow3 k)
pow3Pos Z = LeqS LeqZ
pow3Pos (S k) = leqTrans (pow3Pos k) (leqMulPosLeft 3 (pow3 k) (LeqS LeqZ))

-- The pure odd (tripling) iteration never decreases the height.
public export
oddIterNonDecreasing : (k, x : Nat) ->
  Leq x (iter k (applyAff (MkAffine 3 1)) x)
oddIterNonDecreasing k x =
  rewrite iterThreeXClosed k x in
  leqTrans (leqMulPosLeft (pow3 k) x (pow3Pos k))
           (leqPlusRight (pow3 k * x) (geom k))

-- A single odd step strictly increases the height (for every x): x < 3*x + 1.
public export
oddStepStrictlyIncreases : (x : Nat) -> Leq (S x) (applyAff (MkAffine 3 1) x)
oddStepStrictlyIncreases x =
  rewrite plusCommutative (3 * x) 1 in
  LeqS (leqMulPosLeft 3 x (LeqS LeqZ))

--------------------------------------------------------------------------------
-- Machine-checked examples.
--------------------------------------------------------------------------------

-- Iterating 3x+1 five times from 1 reaches 364 >= 1.
public export
oddIterExample : Leq 1 (iter 5 (applyAff (MkAffine 3 1)) 1)
oddIterExample = oddIterNonDecreasing 5 1

public export
oddIterValueExample : iter 5 (applyAff (MkAffine 3 1)) 1 = 364
oddIterValueExample = Refl
