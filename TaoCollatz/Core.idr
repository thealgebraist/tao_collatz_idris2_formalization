module TaoCollatz.Core

%default total

public export
iter : Nat -> (a -> a) -> a -> a
iter Z _ x = x
iter (S k) f x = iter k f (f x)

public export
iterPlus :
  (m : Nat) ->
  (n : Nat) ->
  (f : a -> a) ->
  (x : a) ->
  iter (m + n) f x = iter n f (iter m f x)
iterPlus Z n f x = Refl
iterPlus (S m) n f x = iterPlus m n f (f x)

public export
data Leq : Nat -> Nat -> Type where
  LeqZ : Leq Z n
  LeqS : Leq m n -> Leq (S m) (S n)

public export
leqRefl : (n : Nat) -> Leq n n
leqRefl Z = LeqZ
leqRefl (S n) = LeqS (leqRefl n)

public export
leqTrans : Leq a b -> Leq b c -> Leq a c
leqTrans LeqZ _ = LeqZ
leqTrans (LeqS ab) (LeqS bc) = LeqS (leqTrans ab bc)

public export
natPred : Nat -> Nat
natPred Z = Z
natPred (S n) = n

public export
leqPredFromSuccLeq : Leq (S m) n -> Leq m (natPred n)
leqPredFromSuccLeq (LeqS mLeqPredN) = mLeqPredN

public export
record EventuallyBelow
  (a : Type)
  (step : a -> a)
  (height : a -> Nat)
  (start : a)
  (bound : Nat) where
  constructor Reaches
  time : Nat
  below : Leq (height (iter time step start)) bound

public export
eventuallyMonotoneBound :
  {a : Type} ->
  {step : a -> a} ->
  {height : a -> Nat} ->
  {x : a} ->
  {smaller : Nat} ->
  {larger : Nat} ->
  EventuallyBelow a step height x smaller ->
  Leq smaller larger ->
  EventuallyBelow a step height x larger
eventuallyMonotoneBound (Reaches time below) smallerLeqLarger =
  Reaches time (leqTrans below smallerLeqLarger)

public export
record OrbitSimulation
  (source : Type)
  (target : Type)
  (sourceStep : source -> source)
  (targetStep : target -> target)
  (sourceHeight : source -> Nat)
  (targetHeight : target -> Nat)
  (toTarget : source -> target) where
  constructor MkOrbitSimulation
  sourceTimeForTargetTime : source -> Nat -> Nat
  simulatedHeightBound :
    (x : source) ->
    (targetTime : Nat) ->
    Leq
      (sourceHeight (iter (sourceTimeForTargetTime x targetTime) sourceStep x))
      (targetHeight (iter targetTime targetStep (toTarget x)))

public export
record OrbitHeightComparison
  (source : Type)
  (target : Type)
  (sourceStep : source -> source)
  (targetStep : target -> target)
  (sourceHeight : source -> Nat)
  (targetHeight : target -> Nat)
  (toTarget : source -> target)
  (x : source) where
  constructor MkOrbitHeightComparison
  sourceTime : Nat
  targetTime : Nat
  comparedHeightBound :
    Leq
      (sourceHeight (iter sourceTime sourceStep x))
      (targetHeight (iter targetTime targetStep (toTarget x)))

public export
comparisonTransfersBelow :
  (comparison :
    OrbitHeightComparison source target sourceStep targetStep sourceHeight targetHeight toTarget x) ->
  (limit : Nat) ->
  Leq
    (targetHeight (iter (targetTime comparison) targetStep (toTarget x)))
    limit ->
  EventuallyBelow source sourceStep sourceHeight x limit
comparisonTransfersBelow comparison limit targetBelow =
  Reaches
    (sourceTime comparison)
    (leqTrans (comparedHeightBound comparison) targetBelow)

public export
simulationTransfersEventuallyBelow :
  OrbitSimulation source target sourceStep targetStep sourceHeight targetHeight toTarget ->
  (x : source) ->
  (limit : Nat) ->
  EventuallyBelow target targetStep targetHeight (toTarget x) limit ->
  EventuallyBelow source sourceStep sourceHeight x limit
simulationTransfersEventuallyBelow simulation x limit (Reaches targetTime targetBelow) =
  Reaches
    (simulation.sourceTimeForTargetTime x targetTime)
    (leqTrans (simulation.simulatedHeightBound x targetTime) targetBelow)

--------------------------------------------------------------------------------
-- Simulation algebra: the identity and composition of orbit simulations.
--
-- These two orthogonal, fully generic lemmas make `OrbitSimulation` a category
-- (objects: dynamical systems with a height; morphisms: height-dominating
-- semiconjugacies).  Every concrete transfer in the development is an instance
-- of these, so downstream reductions never need bespoke simulation glue.
--------------------------------------------------------------------------------

public export
orbitSimulationId :
  {a : Type} ->
  {step : a -> a} ->
  {height : a -> Nat} ->
  OrbitSimulation a a step step height height (\x => x)
orbitSimulationId {step} {height} =
  MkOrbitSimulation
    (\_, t => t)
    (\x, t => leqRefl (height (iter t step x)))

public export
orbitSimulationCompose :
  {s : Type} -> {m : Type} -> {t : Type} ->
  {stepS : s -> s} -> {stepM : m -> m} -> {stepT : t -> t} ->
  {hS : s -> Nat} -> {hM : m -> Nat} -> {hT : t -> Nat} ->
  {toM : s -> m} -> {toT : m -> t} ->
  OrbitSimulation s m stepS stepM hS hM toM ->
  OrbitSimulation m t stepM stepT hM hT toT ->
  OrbitSimulation s t stepS stepT hS hT (\x => toT (toM x))
orbitSimulationCompose {toM} sim1 sim2 =
  MkOrbitSimulation
    (\x, tt =>
      sim1.sourceTimeForTargetTime x (sim2.sourceTimeForTargetTime (toM x) tt))
    (\x, tt =>
      leqTrans
        (sim1.simulatedHeightBound x (sim2.sourceTimeForTargetTime (toM x) tt))
        (sim2.simulatedHeightBound (toM x) tt))
