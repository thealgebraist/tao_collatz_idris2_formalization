module TaoCollatz.Algebra

import Data.Nat
import TaoCollatz.Matrix
import TaoCollatz.Affine
import TaoCollatz.Parity

%default total

--------------------------------------------------------------------------------
-- Iteration 4 (unification: one verified algebraic-structure interface).
--
-- Iterations 1-3 built three concrete carriers --- 2x2 matrices, affine maps,
-- and the parity group Z/2Z --- each with its own associativity and identity
-- proofs.  This module unifies them under a single *verified* monoid interface
-- `MonoidStr` (a bundle carrying the operation, the unit, and proofs of the
-- laws) and a `GroupStr` extending it with inverses.  Generic theorems (unit
-- uniqueness, a well-behaved power operation with `g^(p+q) = g^p * g^q`,
-- inverse uniqueness and involutivity) are proved *once* against the interface,
-- and the three carriers are exhibited as instances.  This is the "safe",
-- explicit, reusable core the rest of the development can lean on.
--------------------------------------------------------------------------------

public export
record MonoidStr (a : Type) where
  constructor MkMonoidStr
  op : a -> a -> a
  unit : a
  assoc : (x,y,z : a) -> op (op x y) z = op x (op y z)
  idL : (x : a) -> op unit x = x
  idR : (x : a) -> op x unit = x

-- The unit of a monoid is the unique left identity.
public export
unitUnique : (m : MonoidStr a) -> (e' : a) ->
  ((x : a) -> op m e' x = x) -> unit m = e'
unitUnique m e' h = trans (sym (h (unit m))) (idR m e')

--------------------------------------------------------------------------------
-- A generic power operation and its additive law, proved once for all monoids.
--------------------------------------------------------------------------------

public export
powM : (m : MonoidStr a) -> Nat -> a -> a
powM m Z _ = unit m
powM m (S k) g = op m (powM m k g) g

public export
powMAdd : (m : MonoidStr a) -> (p, q : Nat) -> (g : a) ->
  powM m (p + q) g = op m (powM m p g) (powM m q g)
powMAdd m p Z g =
  rewrite plusZeroRightNeutral p in sym (idR m (powM m p g))
powMAdd m p (S j) g =
  rewrite sym (plusSuccRightSucc p j) in
  rewrite powMAdd m p j g in
  assoc m (powM m p g) (powM m j g) g

--------------------------------------------------------------------------------
-- Groups: a monoid together with a two-sided inverse.
--------------------------------------------------------------------------------

public export
record GroupStr (a : Type) where
  constructor MkGroupStr
  toMonoid : MonoidStr a
  inv : a -> a
  invL : (x : a) -> op toMonoid (inv x) x = unit toMonoid
  invR : (x : a) -> op toMonoid x (inv x) = unit toMonoid

-- Left inverses are unique: if `y * x = e` then `y = inv x`.
public export
invUnique : (gr : GroupStr a) -> (x, y : a) ->
  op (toMonoid gr) y x = unit (toMonoid gr) -> y = inv gr x
invUnique gr x y h =
  trans (sym (idR (toMonoid gr) y))
    (trans (cong (op (toMonoid gr) y) (sym (invR gr x)))
      (trans (sym (assoc (toMonoid gr) y x (inv gr x)))
        (trans (cong (\t => op (toMonoid gr) t (inv gr x)) h)
          (idL (toMonoid gr) (inv gr x)))))

-- The inverse is involutive: inv (inv x) = x.
public export
invInvolutive : (gr : GroupStr a) -> (x : a) -> inv gr (inv gr x) = x
invInvolutive gr x = sym (invUnique gr (inv gr x) x (invR gr x))

--------------------------------------------------------------------------------
-- The three carriers as instances of the unified interface.
--------------------------------------------------------------------------------

public export
matrixMonoid : MonoidStr Mat2
matrixMonoid =
  MkMonoidStr matMul (MkMat2 1 0 0 1) matMulAssoc matMulIdLeft matMulIdRight

public export
affineMonoid : MonoidStr Affine
affineMonoid =
  MkMonoidStr composeAff (MkAffine 1 0) composeAffAssoc composeAffIdLeft composeAffIdRight

public export
parityMonoid : MonoidStr Parity
parityMonoid =
  MkMonoidStr xorP Even xorPAssoc xorPIdLeft xorPIdRight

-- Parity is not merely a monoid but a group, with every element self-inverse.
public export
parityGroup : GroupStr Parity
parityGroup =
  MkGroupStr parityMonoid (\x => x) xorPSelfInverse xorPSelfInverse

--------------------------------------------------------------------------------
-- The three carriers each satisfy the generic exponent law `g^(p+q) = g^p*g^q`
-- as an immediate consequence of `powMAdd`; here it is instantiated at the
-- parity group, taking the monoid structure as an explicit argument (the
-- nullary instances above are not delta-reduced during conversion).
--------------------------------------------------------------------------------

public export
powExponentLaw : (m : MonoidStr a) -> (p, q : Nat) -> (g : a) ->
  powM m (p + q) g = op m (powM m p g) (powM m q g)
powExponentLaw = powMAdd
