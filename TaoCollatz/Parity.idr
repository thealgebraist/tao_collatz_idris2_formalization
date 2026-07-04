module TaoCollatz.Parity

import TaoCollatz.Dynamics
import TaoCollatz.DynamicsExtra

%default total

--------------------------------------------------------------------------------
-- Iteration 3 (safe algebraic domain: the parity group Z/2Z).
--
-- The even/odd branching that drives the Collatz map is exactly the two-element
-- group `Z/2Z`.  This module gives that group an explicit, total encoding
-- (`Parity` with `xorP` as the group operation), proves it is an abelian group
-- with every element self-inverse, and establishes the fundamental
-- homomorphism `parityOf : (Nat, +) -> (Parity, xorP)`.  It then bridges to the
-- Boolean `isEven` used by the concrete dynamics, so the Collatz step can be
-- selected purely by the *group* element `parityOf n` rather than an opaque
-- Boolean test.
--------------------------------------------------------------------------------

public export
data Parity = Even | Odd

public export
flipP : Parity -> Parity
flipP Even = Odd
flipP Odd = Even

-- The group operation of Z/2Z (addition modulo 2 / exclusive or).
public export
xorP : Parity -> Parity -> Parity
xorP Even q = q
xorP Odd q = flipP q

public export
flipPInvol : (a : Parity) -> flipP (flipP a) = a
flipPInvol Even = Refl
flipPInvol Odd = Refl

--------------------------------------------------------------------------------
-- Abelian-group laws for (Parity, xorP, Even).
--------------------------------------------------------------------------------

public export
xorPAssoc : (a,b,c : Parity) -> xorP (xorP a b) c = xorP a (xorP b c)
xorPAssoc Even b c = Refl
xorPAssoc Odd Even c = Refl
xorPAssoc Odd Odd Even = Refl
xorPAssoc Odd Odd Odd = Refl

public export
xorPIdLeft : (a : Parity) -> xorP Even a = a
xorPIdLeft a = Refl

public export
xorPIdRight : (a : Parity) -> xorP a Even = a
xorPIdRight Even = Refl
xorPIdRight Odd = Refl

public export
xorPComm : (a,b : Parity) -> xorP a b = xorP b a
xorPComm Even Even = Refl
xorPComm Even Odd = Refl
xorPComm Odd Even = Refl
xorPComm Odd Odd = Refl

-- Every element is its own inverse: this is the defining feature of Z/2Z.
public export
xorPSelfInverse : (a : Parity) -> xorP a a = Even
xorPSelfInverse Even = Refl
xorPSelfInverse Odd = Refl

public export
Semigroup Parity where
  (<+>) = xorP

public export
Monoid Parity where
  neutral = Even

--------------------------------------------------------------------------------
-- The homomorphism parityOf : (Nat, +, 0) -> (Parity, xorP, Even).
--------------------------------------------------------------------------------

public export
parityOf : Nat -> Parity
parityOf Z = Even
parityOf (S n) = flipP (parityOf n)

flipXor : (a,b : Parity) -> flipP (xorP a b) = xorP (flipP a) b
flipXor Even b = Refl
flipXor Odd b = flipPInvol b

-- parityOf sends 0 to the identity and respects addition: it is a monoid
-- (indeed group) homomorphism.
public export
parityOfZero : parityOf 0 = Even
parityOfZero = Refl

public export
parityOfPlus : (m,n : Nat) -> parityOf (m + n) = xorP (parityOf m) (parityOf n)
parityOfPlus Z n = Refl
parityOfPlus (S k) n =
  rewrite parityOfPlus k n in
  flipXor (parityOf k) (parityOf n)

--------------------------------------------------------------------------------
-- Bridge to the Boolean `isEven` used by the concrete dynamics.
--------------------------------------------------------------------------------

evenNotOdd : Even = Odd -> Void
evenNotOdd Refl impossible

falseNotTrue : the Bool False = True -> Void
falseNotTrue Refl impossible

trueNotFalse : the Bool True = False -> Void
trueNotFalse Refl impossible

-- The bridge lemmas, proved by two-step induction matching `isEven`'s recursion.
public export
parityTrueIsEven : (n : Nat) -> isEven n = True -> parityOf n = Even
parityTrueIsEven Z e = Refl
parityTrueIsEven (S Z) e = void (falseNotTrue e)
parityTrueIsEven (S (S k)) e =
  trans (flipPInvol (parityOf k)) (parityTrueIsEven k e)

public export
parityFalseIsOdd : (n : Nat) -> isEven n = False -> parityOf n = Odd
parityFalseIsOdd Z e = void (trueNotFalse e)
parityFalseIsOdd (S Z) e = Refl
parityFalseIsOdd (S (S k)) e =
  trans (flipPInvol (parityOf k)) (parityFalseIsOdd k e)

parityEvenGivesIsEven : (n : Nat) -> parityOf n = Even -> isEven n = True
parityEvenGivesIsEven n h with (isEven n) proof e
  parityEvenGivesIsEven n h | True = Refl
  parityEvenGivesIsEven n h | False =
    void (evenNotOdd (trans (sym h) (parityFalseIsOdd n e)))

parityOddGivesIsOdd : (n : Nat) -> parityOf n = Odd -> isEven n = False
parityOddGivesIsOdd n h with (isEven n) proof e
  parityOddGivesIsOdd n h | False = Refl
  parityOddGivesIsOdd n h | True =
    void (evenNotOdd (trans (sym (parityTrueIsEven n e)) h))

--------------------------------------------------------------------------------
-- Collatz step selected by the group element parityOf n.
--------------------------------------------------------------------------------

public export
colEvenParity : (n : Nat) -> parityOf n = Even -> Col (MkPos n) = MkPos (half n)
colEvenParity n h = colEvenStep n (parityEvenGivesIsEven n h)

public export
colOddParity : (n : Nat) -> parityOf n = Odd -> Col (MkPos n) = MkPos (3 * n + 1)
colOddParity n h = colOddStep n (parityOddGivesIsOdd n h)

--------------------------------------------------------------------------------
-- Machine-checked examples.
--------------------------------------------------------------------------------

public export
parityFiveExample : parityOf 5 = Odd
parityFiveExample = Refl

public export
parityHomExample : parityOf (3 + 5) = xorP (parityOf 3) (parityOf 5)
parityHomExample = parityOfPlus 3 5
