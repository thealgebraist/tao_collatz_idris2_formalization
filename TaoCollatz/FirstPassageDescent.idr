module TaoCollatz.FirstPassageDescent

-- Genuine, fully-proved bridge from the Syracuse descent lemma to the
-- first-passage predicate `SyrBelow` that the central theorem's gate
-- (`SyracuseDensityControl`) is actually stated with.
--
-- `SyrBelow (MkOddPos n) bound` is `EventuallyBelow` for the Syracuse dynamics:
-- some iterate of `Syr` has height at most `bound`.  This module shows that a
-- single good Syracuse step (valuation `>= 2`) already produces such a witness
-- at time one, so the descent lemma of `SyracuseDescent` speaks directly in the
-- currency of the gate.
--
-- Everything here is real mathematics: `%default total`, no placeholders, no
-- `believe_me`, no axioms, no holes.

import TaoCollatz.Core
import TaoCollatz.Dynamics
import TaoCollatz.TwoAdic
import TaoCollatz.SyracuseStructure
import TaoCollatz.SyracuseDescent

%default total

||| One Syracuse step realises any bound the step's value already meets: if
||| `Syr(n) <= bound` then `SyrBelow (MkOddPos n) bound` (witnessed at time 1).
public export
syrOneStepBelow :
  (n : Nat) -> (bound : Nat) ->
  Leq (oddValue (Syr (MkOddPos n))) bound ->
  SyrBelow (MkOddPos n) bound
syrOneStepBelow n bound h = Reaches 1 h

||| The descent lemma in first-passage form: if the valuation of `3n+1` is at
||| least two, the Syracuse orbit of the odd number `n` reaches (at time one) a
||| value at most `n`.
public export
syrDescendStepBelow :
  (n : Nat) ->
  Leq (S Z) n ->
  Leq 4 (pow2 (syrValuation n)) ->
  SyrBelow (MkOddPos n) n
syrDescendStepBelow n h1 hval =
  syrOneStepBelow n n (syrDescends n h1 hval)

--------------------------------------------------------------------------------
-- Concrete sanity check: Syr(5) = 1 <= 5, witnessed at time one.
--------------------------------------------------------------------------------

public export
syrFiveBelowFive : SyrBelow (MkOddPos 5) 5
syrFiveBelowFive =
  syrDescendStepBelow 5 (LeqS LeqZ) (LeqS (LeqS (LeqS (LeqS LeqZ))))
