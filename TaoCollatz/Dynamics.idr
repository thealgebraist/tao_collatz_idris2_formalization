module TaoCollatz.Dynamics

import TaoCollatz.Core

%default total

public export
record Pos where
  constructor MkPos
  posValue : Nat

public export
record OddPos where
  constructor MkOddPos
  oddValue : Nat

public export
PaperPositiveNat : Nat -> Type
PaperPositiveNat Z = Void
PaperPositiveNat (S n) = ()

public export
PaperOddPositiveNat : Nat -> Type
PaperOddPositiveNat Z = Void
PaperOddPositiveNat (S Z) = ()
PaperOddPositiveNat (S (S n)) = PaperOddPositiveNat n

public export
PaperPositive : Pos -> Type
PaperPositive (MkPos n) = PaperPositiveNat n

public export
PaperOddPositive : OddPos -> Type
PaperOddPositive (MkOddPos n) = PaperOddPositiveNat n

public export
isEven : Nat -> Bool
isEven Z = True
isEven (S Z) = False
isEven (S (S n)) = isEven n

public export
half : Nat -> Nat
half Z = Z
half (S Z) = Z
half (S (S n)) = S (half n)

public export
oddFactorFuel : Nat -> Nat -> Nat
oddFactorFuel Z n = n
oddFactorFuel (S fuel) n =
  if isEven n
    then oddFactorFuel fuel (half n)
    else n

public export
oddFactor : Nat -> Nat
oddFactor n = oddFactorFuel n n

public export
oddPartDropTimeFuel : Nat -> Nat -> Nat
oddPartDropTimeFuel Z n = Z
oddPartDropTimeFuel (S fuel) n =
  if isEven n
    then S (oddPartDropTimeFuel fuel (half n))
    else Z

public export
oddPartDropTime : Nat -> Nat
oddPartDropTime n = oddPartDropTimeFuel n n

public export
Col : Pos -> Pos
Col (MkPos n) =
  if isEven n
    then MkPos (half n)
    else MkPos (3 * n + 1)

public export
Syr : OddPos -> OddPos
Syr (MkOddPos n) = MkOddPos (oddFactor (3 * n + 1))

public export
posSize : Pos -> Nat
posSize = posValue

public export
oddSize : OddPos -> Nat
oddSize = oddValue

public export
oddPart : Pos -> OddPos
oddPart (MkPos n) = MkOddPos (oddFactor n)

public export
oddAsPos : OddPos -> Pos
oddAsPos (MkOddPos n) = MkPos n

public export
ColBelow : Pos -> Nat -> Type
ColBelow n bound = EventuallyBelow Pos Col posSize n bound

public export
SyrBelow : OddPos -> Nat -> Type
SyrBelow n bound = EventuallyBelow OddPos Syr oddSize n bound

public export
oddFactorFuelColNormalize :
  (fuel : Nat) ->
  (n : Nat) ->
  posValue (iter (oddPartDropTimeFuel fuel n) Col (MkPos n)) = oddFactorFuel fuel n
oddFactorFuelColNormalize Z n = Refl
oddFactorFuelColNormalize (S fuel) n with (isEven n) proof evenProof
  oddFactorFuelColNormalize (S fuel) n | True =
    rewrite evenProof in
      oddFactorFuelColNormalize fuel (half n)
  oddFactorFuelColNormalize (S fuel) n | False = Refl

public export
oddPartDropTimeNormalizesValue :
  (n : Nat) ->
  posValue (iter (oddPartDropTime n) Col (MkPos n)) = oddFactor n
oddPartDropTimeNormalizesValue n =
  oddFactorFuelColNormalize n n

public export
oddPartDropTimeInitialHeightBound :
  (n : Nat) ->
  Leq
    (posSize (iter (oddPartDropTime n) Col (MkPos n)))
    (oddSize (oddPart (MkPos n)))
oddPartDropTimeInitialHeightBound n =
  rewrite oddPartDropTimeNormalizesValue n in
    leqRefl (oddFactor n)

public export
oddPartInitialSourceTime : Pos -> Nat
oddPartInitialSourceTime (MkPos n) = oddPartDropTime n

public export
oddPartInitialHeightBound :
  (pos : Pos) ->
  Leq
    (posSize (iter (oddPartInitialSourceTime pos) Col pos))
    (oddSize (oddPart pos))
oddPartInitialHeightBound (MkPos n) =
  oddPartDropTimeInitialHeightBound n

public export
colThreeExample : posValue (Col (MkPos 3)) = 10
colThreeExample = Refl

public export
syrSevenExample : oddValue (Syr (MkOddPos 7)) = 11
syrSevenExample = Refl

public export
oddPartTwelveExample : oddValue (oddPart (MkPos 12)) = 3
oddPartTwelveExample = Refl

public export
oddPartDropTimeTwelveExample : oddPartDropTime 12 = 2
oddPartDropTimeTwelveExample = Refl

public export
oddPartDropTimeFortyExample : oddPartDropTime 40 = 3
oddPartDropTimeFortyExample = Refl

public export
oddPartNormalizeSevenExample :
  posValue (iter (oddPartDropTime 7) Col (MkPos 7)) = 7
oddPartNormalizeSevenExample = Refl

public export
oddPartNormalizeTwelveExample :
  posValue (iter (oddPartDropTime 12) Col (MkPos 12)) = oddValue (oddPart (MkPos 12))
oddPartNormalizeTwelveExample = oddPartDropTimeNormalizesValue 12

public export
oddPartNormalizeFortyExample :
  posValue (iter (oddPartDropTime 40) Col (MkPos 40)) = oddValue (oddPart (MkPos 40))
oddPartNormalizeFortyExample = oddPartDropTimeNormalizesValue 40

public export
oddPartNormalizeTwelveSync :
  oddPart (iter (oddPartDropTime 12) Col (MkPos 12)) = oddPart (MkPos 12)
oddPartNormalizeTwelveSync = Refl

public export
oddPartNormalizeTwelveHeightBound :
  Leq
    (posSize (iter (oddPartDropTime 12) Col (MkPos 12)))
    (oddSize (oddPart (MkPos 12)))
oddPartNormalizeTwelveHeightBound = oddPartDropTimeInitialHeightBound 12

public export
twelveInitialOrbitComparison :
  OrbitHeightComparison
    Pos
    OddPos
    Col
    Syr
    TaoCollatz.Dynamics.posSize
    TaoCollatz.Dynamics.oddSize
    TaoCollatz.Dynamics.oddPart
    (MkPos 12)
twelveInitialOrbitComparison =
  MkOrbitHeightComparison
    (oddPartDropTime 12)
    0
    oddPartNormalizeTwelveHeightBound

public export
colThreeTwoStepsExample : posValue (iter 2 Col (MkPos 3)) = 5
colThreeTwoStepsExample = Refl

public export
syrOddPartThreeOneStepExample :
  oddValue (iter 1 Syr (oddPart (MkPos 3))) = 5
syrOddPartThreeOneStepExample = Refl

public export
colThreeSyracuseHeightComparison :
  OrbitHeightComparison
    Pos
    OddPos
    Col
    Syr
    TaoCollatz.Dynamics.posSize
    TaoCollatz.Dynamics.oddSize
    TaoCollatz.Dynamics.oddPart
    (MkPos 3)
colThreeSyracuseHeightComparison =
  MkOrbitHeightComparison 2 1 (leqRefl 5)

public export
colThreeBelowFromSyracuseComparison : ColBelow (MkPos 3) 5
colThreeBelowFromSyracuseComparison =
  comparisonTransfersBelow
    colThreeSyracuseHeightComparison
    5
    (leqRefl 5)

public export
twelveOddPartHeightComparison :
  OrbitHeightComparison
    Pos
    OddPos
    Col
    Syr
    TaoCollatz.Dynamics.posSize
    TaoCollatz.Dynamics.oddSize
    TaoCollatz.Dynamics.oddPart
    (MkPos 12)
twelveOddPartHeightComparison =
  MkOrbitHeightComparison 2 0 (leqRefl 3)

public export
twelveBelowFromOddPartComparison : ColBelow (MkPos 12) 12
twelveBelowFromOddPartComparison =
  comparisonTransfersBelow
    twelveOddPartHeightComparison
    12
    (LeqS (LeqS (LeqS LeqZ)))

public export
threeIsPaperPositive : PaperPositive (MkPos 3)
threeIsPaperPositive = ()

public export
sevenIsPaperOddPositive : PaperOddPositive (MkOddPos 7)
sevenIsPaperOddPositive = ()

public export
colThreeBelowTen : ColBelow (MkPos 3) 10
colThreeBelowTen = Reaches 1 (leqRefl 10)

public export
syrSevenBelowEleven : SyrBelow (MkOddPos 7) 11
syrSevenBelowEleven = Reaches 1 (leqRefl 11)
