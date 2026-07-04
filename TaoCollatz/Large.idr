module TaoCollatz.Large

import TaoCollatz.Core
import TaoCollatz.Dual
import TaoCollatz.Dynamics

%default total

public export
record TendsToInfinityOn
  (carrier : Type)
  (height : carrier -> Nat)
  (f : carrier -> Nat) where
  constructor MkTendsToInfinityOn
  thresholdFor : Nat -> Nat
  growsPast :
    (target : Nat) ->
    (x : carrier) ->
    Leq (thresholdFor target) (height x) ->
    Leq target (f x)

public export
TendsToInfinityPos : (Pos -> Nat) -> Type
TendsToInfinityPos = TendsToInfinityOn Pos posSize

public export
TendsToInfinityOdd : (OddPos -> Nat) -> Type
TendsToInfinityOdd = TendsToInfinityOn OddPos oddSize

public export
growthMonotone :
  {carrier : Type} ->
  {height : carrier -> Nat} ->
  {f : carrier -> Nat} ->
  {g : carrier -> Nat} ->
  ((x : carrier) -> Leq (f x) (g x)) ->
  TendsToInfinityOn carrier height f ->
  TendsToInfinityOn carrier height g
growthMonotone fBelowG fGrows =
  MkTendsToInfinityOn
    (thresholdFor fGrows)
    (\target, x, xLarge =>
      leqTrans (growsPast fGrows target x xLarge) (fBelowG x))

public export
growthPred :
  {carrier : Type} ->
  {height : carrier -> Nat} ->
  {f : carrier -> Nat} ->
  TendsToInfinityOn carrier height f ->
  TendsToInfinityOn carrier height (\x => natPred (f x))
growthPred fGrows =
  MkTendsToInfinityOn
    (\target => thresholdFor fGrows (S target))
    (\target, x, xLarge =>
      leqPredFromSuccLeq (growsPast fGrows (S target) x xLarge))

public export
posSizeTendsToInfinity : TendsToInfinityPos TaoCollatz.Dynamics.posSize
posSizeTendsToInfinity =
  MkTendsToInfinityOn
    (\target => target)
    (\target, (MkPos n), xLarge => xLarge)

public export
oddSizeTendsToInfinity : TendsToInfinityOdd TaoCollatz.Dynamics.oddSize
oddSizeTendsToInfinity =
  MkTendsToInfinityOn
    (\target => target)
    (\target, (MkOddPos n), xLarge => xLarge)

public export
record VanishesAtInfinity (errorBound : Nat -> Nat) where
  constructor MkVanishesAtInfinity
  cutoffForPrecision : Nat -> Nat
  errorBelowPrecision :
    (precision : Nat) ->
    (cutoff : Nat) ->
    Leq (cutoffForPrecision precision) cutoff ->
    Leq (errorBound cutoff) precision

public export
zeroVanishesAtInfinity : VanishesAtInfinity (\cutoff => Z)
zeroVanishesAtInfinity =
  MkVanishesAtInfinity
    (\precision => Z)
    (\precision, cutoff, cutoffLarge => LeqZ)

public export
record LogarithmicSmallness
  (carrier : Type)
  (goodSet : carrier -> Type) where
  constructor MkLogarithmicSmallness
  smallnessPayload : Type
  smallnessPayloadEvidence : smallnessPayload
  errorBound : Nat -> Nat
  errorVanishes : VanishesAtInfinity errorBound

public export
record ExceptionalSmall
  (carrier : Type)
  (goodSet : carrier -> Type) where
  constructor MkExceptionalSmall
  smallnessCertificate : LogarithmicSmallness carrier goodSet
  orderSmallnessEvidence : OrderFilter (smallnessPayload smallnessCertificate)
  quantitativeSmallnessEvidence : QuantitativeProbability (smallnessPayload smallnessCertificate)

public export
exceptionalSmallPure :
  {carrier : Type} ->
  {goodSet : carrier -> Type} ->
  (certificate : Type) ->
  certificate ->
  ExceptionalSmall carrier goodSet
exceptionalSmallPure certificate evidence =
  MkExceptionalSmall
    (MkLogarithmicSmallness
      certificate
      evidence
      (\cutoff => Z)
      zeroVanishesAtInfinity)
    (InOrderFilter evidence)
    (InQuantitativeProbability evidence)

public export
smallnessDualProof :
  (small : ExceptionalSmall carrier goodSet) ->
  DualProof (smallnessPayload (smallnessCertificate small))
smallnessDualProof small =
  ProvedTwice
    (orderSmallnessEvidence small)
    (quantitativeSmallnessEvidence small)

public export
pullbackExceptionalSmall :
  (toTarget : source -> target) ->
  {goodSet : target -> Type} ->
  ExceptionalSmall target goodSet ->
  ExceptionalSmall source (\x => goodSet (toTarget x))
pullbackExceptionalSmall toTarget small =
  MkExceptionalSmall
    (MkLogarithmicSmallness
      (smallnessPayload (smallnessCertificate small))
      (smallnessPayloadEvidence (smallnessCertificate small))
      (errorBound (smallnessCertificate small))
      (errorVanishes (smallnessCertificate small)))
    (orderSmallnessEvidence small)
    (quantitativeSmallnessEvidence small)

public export
mapExceptionalSmall :
  {carrier : Type} ->
  {goodSet : carrier -> Type} ->
  {largerSet : carrier -> Type} ->
  ExceptionalSmall carrier goodSet ->
  ((x : carrier) -> goodSet x -> largerSet x) ->
  ExceptionalSmall carrier largerSet
mapExceptionalSmall small pointwise =
  MkExceptionalSmall
    (MkLogarithmicSmallness
      (smallnessPayload (smallnessCertificate small),
       (x : carrier) -> goodSet x -> largerSet x)
      ((smallnessPayloadEvidence (smallnessCertificate small)), pointwise)
      (errorBound (smallnessCertificate small))
      (errorVanishes (smallnessCertificate small)))
    (InOrderFilter
      (case orderSmallnessEvidence small of
        InOrderFilter evidence => (evidence, pointwise)))
    (InQuantitativeProbability
      (case quantitativeSmallnessEvidence small of
        InQuantitativeProbability evidence => (evidence, pointwise)))

public export
record ExceptionalControl
  (carrier : Type)
  (p : carrier -> Type) where
  constructor MkExceptionalControl
  controlledSet : carrier -> Type
  exceptionalSmall : ExceptionalSmall carrier controlledSet
  controlledImplies : (x : carrier) -> controlledSet x -> p x

public export
controlCertificate : ExceptionalControl carrier p -> Type
controlCertificate control =
  smallnessPayload (smallnessCertificate (exceptionalSmall control))

public export
certificateEvidence : (control : ExceptionalControl carrier p) -> controlCertificate control
certificateEvidence control =
  case orderSmallnessEvidence (exceptionalSmall control) of
    InOrderFilter evidence => evidence

public export
controlErrorBound : ExceptionalControl carrier p -> Nat -> Nat
controlErrorBound control =
  errorBound (smallnessCertificate (exceptionalSmall control))

public export
controlErrorVanishes :
  (control : ExceptionalControl carrier p) ->
  VanishesAtInfinity (controlErrorBound control)
controlErrorVanishes control =
  errorVanishes (smallnessCertificate (exceptionalSmall control))

public export
AlmostAllOn : (carrier : Type) -> (carrier -> Type) -> Type
AlmostAllOn carrier p = ExceptionalControl carrier p

public export
AlmostAllPos : (Pos -> Type) -> Type
AlmostAllPos = AlmostAllOn Pos

public export
AlmostAllOdd : (OddPos -> Type) -> Type
AlmostAllOdd = AlmostAllOn OddPos

public export
controlByProperty :
  {carrier : Type} ->
  {p : carrier -> Type} ->
  (certificate : Type) ->
  certificate ->
  ExceptionalControl carrier p
controlByProperty certificate evidence =
  MkExceptionalControl
    p
    (exceptionalSmallPure certificate evidence)
    (\x, px => px)

public export
ControlPullback :
  (source : Type) ->
  (target : Type) ->
  (toTarget : source -> target) ->
  Type
ControlPullback source target toTarget =
  {p : target -> Type} ->
  ExceptionalControl target p ->
  ExceptionalControl source (\x => p (toTarget x))

public export
controlPullback : (toTarget : source -> target) -> ControlPullback source target toTarget
controlPullback toTarget control =
  MkExceptionalControl
    (\x => controlledSet control (toTarget x))
    (pullbackExceptionalSmall toTarget (exceptionalSmall control))
    (\x, good => controlledImplies control (toTarget x) good)

public export
ControlMap : Type -> Type
ControlMap carrier =
  {p : carrier -> Type} ->
  {q : carrier -> Type} ->
  ExceptionalControl carrier p ->
  ((x : carrier) -> p x -> q x) ->
  ExceptionalControl carrier q

public export
mapExceptionalControl :
  {carrier : Type} ->
  {p : carrier -> Type} ->
  {q : carrier -> Type} ->
  ExceptionalControl carrier p ->
  ((x : carrier) -> p x -> q x) ->
  ExceptionalControl carrier q
mapExceptionalControl {carrier} {p} {q} control pointwise =
  MkExceptionalControl
    (controlledSet control)
    (mapExceptionalSmall (exceptionalSmall control) (\x, good => good))
    (\x, good => pointwise x (controlledImplies control x good))

public export
controlMap : (carrier : Type) -> ControlMap carrier
controlMap carrier = mapExceptionalControl

public export
almostAllMap :
  {carrier : Type} ->
  {p : carrier -> Type} ->
  {q : carrier -> Type} ->
  AlmostAllOn carrier p ->
  ((x : carrier) -> p x -> q x) ->
  AlmostAllOn carrier q
almostAllMap control pointwise =
  mapExceptionalControl control pointwise

public export
almostAllPullback :
  (toTarget : source -> target) ->
  {p : target -> Type} ->
  AlmostAllOn target p ->
  AlmostAllOn source (\x => p (toTarget x))
almostAllPullback toTarget control =
  controlPullback toTarget control

public export
LargeSet : (carrier : Type) -> ((carrier -> Type) -> Type) -> Type
LargeSet carrier large =
  {p : carrier -> Type} ->
  {q : carrier -> Type} ->
  large p ->
  ((x : carrier) -> p x -> q x) ->
  large q

public export
almostAllLargeSet : (carrier : Type) -> LargeSet carrier (AlmostAllOn carrier)
almostAllLargeSet carrier = almostAllMap

public export
TransferToOdd :
  (source : Type) ->
  (target : Type) ->
  (largeSource : (source -> Type) -> Type) ->
  (largeTarget : (target -> Type) -> Type) ->
  (toTarget : source -> target) ->
  Type
TransferToOdd source target largeSource largeTarget toTarget =
  {p : target -> Type} ->
  largeTarget p ->
  largeSource (\x => p (toTarget x))

public export
almostAllTransferToOdd :
  (toTarget : source -> target) ->
  TransferToOdd source target (AlmostAllOn source) (AlmostAllOn target) toTarget
almostAllTransferToOdd toTarget = almostAllPullback toTarget

public export
PointwiseOrbitTransfer :
  (source : Type) ->
  (target : Type) ->
  (toTarget : source -> target) ->
  (sourceBelow : source -> Nat -> Type) ->
  (targetBelow : target -> Nat -> Type) ->
  Type
PointwiseOrbitTransfer source target toTarget sourceBelow targetBelow =
  (x : source) ->
  (bound : Nat) ->
  targetBelow (toTarget x) bound ->
  sourceBelow x bound

public export
Theorem13 : Type
Theorem13 =
  (f : Pos -> Nat) ->
  TendsToInfinityPos f ->
  AlmostAllPos (\n => ColBelow n (f n))

public export
ColBelowStrict : Pos -> Nat -> Type
ColBelowStrict n bound = ColBelow n (natPred bound)

public export
Theorem13Strict : Type
Theorem13Strict =
  (f : Pos -> Nat) ->
  TendsToInfinityPos f ->
  AlmostAllPos (\n => ColBelowStrict n (f n))

public export
Theorem13PaperDomain : Type
Theorem13PaperDomain =
  (f : Pos -> Nat) ->
  TendsToInfinityPos f ->
  AlmostAllPos (\n => PaperPositive n -> ColBelowStrict n (f n))

public export
theorem13StrictFromNonStrict : Theorem13 -> Theorem13Strict
theorem13StrictFromNonStrict theorem13 f fGrows =
  theorem13 (\n => natPred (f n)) (growthPred fGrows)

public export
theorem13PaperDomainFromStrict : Theorem13Strict -> Theorem13PaperDomain
theorem13PaperDomainFromStrict theorem13Strict f fGrows =
  almostAllMap
    (theorem13Strict f fGrows)
    (\n, below, positive => below)

public export
Theorem16 : Type
Theorem16 =
  (f : OddPos -> Nat) ->
  TendsToInfinityOdd f ->
  AlmostAllOdd (\n => SyrBelow n (f n))

public export
Theorem16PaperDomain : Type
Theorem16PaperDomain =
  (f : OddPos -> Nat) ->
  TendsToInfinityOdd f ->
  AlmostAllOdd (\n => PaperOddPositive n -> SyrBelow n (f n))

public export
theorem16PaperDomainFromTheorem16 : Theorem16 -> Theorem16PaperDomain
theorem16PaperDomainFromTheorem16 theorem16 f fGrows =
  almostAllMap
    (theorem16 f fGrows)
    (\n, below, oddPositive => below)
