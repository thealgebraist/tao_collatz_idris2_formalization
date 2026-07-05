module TaoCollatz.OddToPosTransfer

-- The density transfer completing step 8: from density-one Syracuse first
-- passage on the odd domain (`OddPos`, indexed by raw value) to the
-- positive-integer domain (`Pos`) via the odd-part map.  Everything here is
-- genuine (natural density); the analytic core `negligiblePull`
-- (density-one sets pull back along `oddFactor`) is proved in
-- `TaoCollatz.DensityTransfer`.

import TaoCollatz.Core
import TaoCollatz.Dynamics
import TaoCollatz.Large
import TaoCollatz.Density
import TaoCollatz.DensityTransfer
import TaoCollatz.CarrierDensity
import TaoCollatz.MinimalProof
import TaoCollatz.OddThreshold
import Data.Nat

%default total

--------------------------------------------------------------------------------
-- A "slow inverse" of the threshold function, giving a height `g` on `OddPos`
-- with `g (oddPart x) <= f x` for every `x`, and `g -> infinity`.
--------------------------------------------------------------------------------

public export
leqB : Nat -> Nat -> Bool
leqB Z _ = True
leqB (S _) Z = False
leqB (S a) (S b) = leqB a b

public export
leqBTrue : (a : Nat) -> (b : Nat) -> leqB a b = True -> Leq a b
leqBTrue Z b _ = LeqZ
leqBTrue (S a) (S b) prf = LeqS (leqBTrue a b prf)

public export
leqBFalse : (a : Nat) -> (b : Nat) -> leqB a b = False -> Leq (S b) a
leqBFalse (S a) Z _ = LeqS LeqZ
leqBFalse (S a) (S b) prf = LeqS (leqBFalse a b prf)

public export
notLeqBoth : {x : Nat} -> {v : Nat} -> Leq x v -> Leq (S v) x -> Void
notLeqBoth (LeqS h1) (LeqS h2) = notLeqBoth h1 h2
notLeqBoth LeqZ h2 impossible

public export
leSuccCases : (t0 : Nat) -> (c : Nat) -> Leq t0 (S c) ->
              Either (Leq t0 c) (t0 = S c)
leSuccCases Z c _ = Left LeqZ
leSuccCases (S t0) Z (LeqS h) = Right (cong S (case h of LeqZ => Refl))
leSuccCases (S t0) (S c) (LeqS h) =
  case leSuccCases t0 c h of
    Left l => Left (LeqS l)
    Right e => Right (cong S e)

public export
searchDown : (thr : Nat -> Nat) -> (v : Nat) -> (t : Nat) -> Nat
searchDown thr v Z = Z
searchDown thr v (S t) with (leqB (thr (S t)) v)
  _ | True = S t
  _ | False = searchDown thr v t

public export
slowInv : (thr : Nat -> Nat) -> (v : Nat) -> Nat
slowInv thr v = searchDown thr v v

public export
searchDownPass : (thr : Nat -> Nat) -> (v : Nat) -> (t : Nat) ->
  Either (searchDown thr v t = 0) (Leq (thr (searchDown thr v t)) v)
searchDownPass thr v Z = Left Refl
searchDownPass thr v (S t) with (leqB (thr (S t)) v) proof eq
  _ | True = Right (leqBTrue (thr (S t)) v eq)
  _ | False = searchDownPass thr v t

public export
searchDownGe : (thr : Nat -> Nat) -> (v : Nat) -> (cap : Nat) -> (t0 : Nat) ->
  Leq t0 cap -> Leq (thr t0) v -> Leq t0 (searchDown thr v cap)
searchDownGe thr v Z t0 le _ = le
searchDownGe thr v (S c) t0 le hthr with (leqB (thr (S c)) v) proof eq
  _ | True = le
  _ | False =
      case leSuccCases t0 c le of
        Left lc => searchDownGe thr v c t0 lc hthr
        Right e =>
          void (notLeqBoth (rewrite sym e in hthr) (leqBFalse (thr (S c)) v eq))

public export
slowInvPass : (thr : Nat -> Nat) -> (v : Nat) ->
  Either (slowInv thr v = 0) (Leq (thr (slowInv thr v)) v)
slowInvPass thr v = searchDownPass thr v v

public export
slowInvGe : (thr : Nat -> Nat) -> (v : Nat) -> (t0 : Nat) ->
  Leq t0 v -> Leq (thr t0) v -> Leq t0 (slowInv thr v)
slowInvGe thr v t0 le hthr = searchDownGe thr v v t0 le hthr

--------------------------------------------------------------------------------
-- The transfer.
--------------------------------------------------------------------------------

||| From density-one Syracuse first passage on the odd domain to the
||| positive-integer gate `SyracuseDensityControl`.
public export
oddToPosTransfer :
  ((f : OddPos -> Nat) -> TendsToInfinityOdd f ->
     (good : OddPos -> Bool **
       (AlmostAllOddD good,
        (y : OddPos) -> good y = True -> SyrBelow y (f y)))) ->
  SyracuseDensityControl
oddToPosTransfer odc f fGrows =
  let thr : Nat -> Nat
      thr = thresholdFor fGrows
      g : OddPos -> Nat
      g = \y => slowInv thr (oddSize y)
      gGrows : TendsToInfinityOdd g
      gGrows =
        MkTendsToInfinityOn
          (\target => maxN target (thr target))
          (\target, y, yLarge =>
             slowInvGe thr (oddSize y) target
               (leqTrans (leqMaxL target (thr target)) yLarge)
               (leqTrans (leqMaxR target (thr target)) yLarge))
  in case odc g gGrows of
       (oddGood ** (aaOdd, impOdd)) =>
         let posGood : Pos -> Bool
             posGood = \x => oddGood (oddPart x)
             aaPos : AlmostAllPosD posGood
             aaPos = negligiblePull (\m => not (oddGood (MkOddPos m))) aaOdd
             boundProp : (x : Pos) -> Leq (g (oddPart x)) (f x)
             boundProp (MkPos n) =
               case slowInvPass thr (oddFactor n) of
                 Left e0 => rewrite e0 in LeqZ
                 Right hpass =>
                   growsPast fGrows (slowInv thr (oddFactor n)) (MkPos n)
                     (leqTrans hpass (oddFactorLe n))
             impPos : (x : Pos) -> posGood x = True -> SyrBelow (oddPart x) (f x)
             impPos x gx =
               eventuallyMonotoneBound (impOdd (oddPart x) gx) (boundProp x)
         in (posGood ** (aaPos, impPos))
