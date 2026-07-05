module TaoCollatz.OddPart

import TaoCollatz.Core
import TaoCollatz.Dynamics
import TaoCollatz.TwoAdic
import TaoCollatz.SyracuseStructure
import TaoCollatz.PaperInterfaces

%default total

--------------------------------------------------------------------------------
-- A genuine proof of the odd-part orbit simulation
--   (the Syracuse map is the odd part of the Collatz map).
--
-- Previously this dynamical fact was postulated with `believe_me`.  Here it is
-- proved: for every positive integer, iterating the Collatz map `Col` visits
-- exactly the odd values produced by the Syracuse map `Syr` on the odd part.
--------------------------------------------------------------------------------

-- Elementary arithmetic on `Leq` and `half`.

public export
leqSucc : (n : Nat) -> Leq n (S n)
leqSucc Z = LeqZ
leqSucc (S k) = LeqS (leqSucc k)

public export
halfLe : (n : Nat) -> Leq (half n) n
halfLe Z = LeqZ
halfLe (S Z) = LeqZ
halfLe (S (S k)) = LeqS (leqTrans (halfLe k) (leqSucc k))

public export
succNonZero : (k : Nat) -> Not (S k = 0)
succNonZero k Refl impossible

||| A nonzero `Nat` is at least one.  This bridges the `Not (n = 0)` phrasing
||| used in this module to the `Leq 1 n` phrasing of `TaoCollatz.TwoAdic`.
public export
nonZeroToPos : (n : Nat) -> Not (n = 0) -> Leq (S Z) n
nonZeroToPos Z nz = absurd (nz Refl)
nonZeroToPos (S k) _ = LeqS LeqZ

-- The odd factor of any positive number is odd.  Rather than re-running the
-- fuelled induction here, we reuse the single proof in `TaoCollatz.TwoAdic`
-- (`oddFactorIsOdd`), keeping one source of truth for this fact.

public export
oddFactorOdd : (n : Nat) -> Not (n = 0) -> isEven (oddFactor n) = False
oddFactorOdd n nz = oddFactorIsOdd n (nonZeroToPos n nz)

public export
plusOneNonZero : (x : Nat) -> Not (x + 1 = 0)
plusOneNonZero Z Refl impossible
plusOneNonZero (S k) Refl impossible

--------------------------------------------------------------------------------
-- Parity and idempotence of the odd factor (orthogonal number-theoretic facts).
--
-- `oddFactor` extracts the odd part, so it fixes numbers that are already odd
-- and is idempotent on positives; `Syr` and `oddPart` always land on odd
-- values.  These are the elementary invariants that make the odd-part picture
-- consistent (the Syracuse map really does act on odd numbers).
--------------------------------------------------------------------------------

-- An odd number is its own odd factor (regardless of the fuel supplied).
public export
oddFactorFuelFixed :
  (fuel : Nat) -> (n : Nat) -> isEven n = False -> oddFactorFuel fuel n = n
oddFactorFuelFixed Z n prf = Refl
oddFactorFuelFixed (S f) n prf = rewrite prf in Refl

public export
oddFactorFixed : (n : Nat) -> isEven n = False -> oddFactor n = n
oddFactorFixed n prf = oddFactorFuelFixed n n prf

-- Extracting the odd factor is idempotent on positive numbers.
public export
oddFactorIdempotent :
  (n : Nat) -> Not (n = 0) -> oddFactor (oddFactor n) = oddFactor n
oddFactorIdempotent n nz = oddFactorFixed (oddFactor n) (oddFactorOdd n nz)

-- The odd part of a positive number is odd.
public export
oddPartValueOdd :
  (p : Pos) -> Not (posValue p = 0) -> isEven (oddValue (oddPart p)) = False
oddPartValueOdd (MkPos n) nz = oddFactorOdd n nz

-- One Syracuse step always lands on an odd number (no hypothesis needed:
-- `3n+1` is positive for every `n`).  This is the `OddPos`-packaged form of the
-- single fact proved in `TaoCollatz.SyracuseStructure` (`syrValueOdd` on `Nat`);
-- we reuse it here rather than re-deriving it.
public export
syrValueOdd : (o : OddPos) -> isEven (oddValue (Syr o)) = False
syrValueOdd (MkOddPos n) = SyracuseStructure.syrValueOdd n

-- The odd part of a positive number is a fixed point of `oddPart`
-- (as a bare value): re-extracting the odd factor changes nothing.
public export
oddPartValueIdempotent :
  (p : Pos) -> Not (posValue p = 0) ->
  oddValue (oddPart (oddAsPos (oddPart p))) = oddValue (oddPart p)
oddPartValueIdempotent (MkPos n) nz = oddFactorIdempotent n nz

-- Record eta and basic rewriting helpers.

public export
posEta : (p : Pos) -> p = MkPos (posValue p)
posEta (MkPos x) = Refl

public export
oddEta : (o : OddPos) -> o = MkOddPos (oddValue o)
oddEta (MkOddPos x) = Refl

-- Structural (not merely value-level) idempotence of the odd part:
-- the odd part of the odd part is the odd part.
public export
oddPartIdempotent :
  (p : Pos) -> Not (posValue p = 0) ->
  oddPart (oddAsPos (oddPart p)) = oddPart p
oddPartIdempotent p nz =
  trans (oddEta (oddPart (oddAsPos (oddPart p))))
        (trans (cong MkOddPos (oddPartValueIdempotent p nz))
               (sym (oddEta (oddPart p))))

public export
leqOfEq : {a, b : Nat} -> a = b -> Leq a b
leqOfEq Refl = leqRefl _

-- One Collatz step on an odd number equals the `3n+1` map.

public export
colOdd : (m : Nat) -> isEven m = False -> Col (MkPos m) = MkPos (3 * m + 1)
colOdd m prf = rewrite prf in Refl

-- Dropping the even part in the Collatz orbit reaches the odd factor (as a Pos).

public export
normalizeToPos :
  (k : Nat) -> iter (oddPartDropTime k) Col (MkPos k) = MkPos (oddFactor k)
normalizeToPos k =
  trans (posEta (iter (oddPartDropTime k) Col (MkPos k)))
        (cong MkPos (oddPartDropTimeNormalizesValue k))

-- One Syracuse step realised inside the Collatz orbit (starting from an odd m).

public export
syrRealizeStep :
  (m : Nat) -> isEven m = False -> (k : Nat) -> (s' : Nat) ->
  (eq' : posValue (iter s' Col (MkPos (oddFactor (3 * m + 1))))
          = oddValue (iter k Syr (MkOddPos (oddFactor (3 * m + 1))))) ->
  posValue (iter (S (oddPartDropTime (3 * m + 1) + s')) Col (MkPos m))
    = oddValue (iter (S k) Syr (MkOddPos m))
syrRealizeStep m mOdd k s' eq' =
  rewrite colOdd m mOdd in
  rewrite iterPlus (oddPartDropTime (3 * m + 1)) s' Col (MkPos (3 * m + 1)) in
  rewrite normalizeToPos (3 * m + 1) in
  eq'

-- The exact Collatz/Syracuse correspondence, starting from an odd number.

public export
syrRealize :
  (m : Nat) -> isEven m = False -> (t : Nat) ->
  (s : Nat ** posValue (iter s Col (MkPos m)) = oddValue (iter t Syr (MkOddPos m)))
syrRealize m mOdd Z = (0 ** Refl)
syrRealize m mOdd (S k) =
  let (s' ** eq') =
        syrRealize (oddFactor (3 * m + 1))
                   (oddFactorOdd (3 * m + 1) (plusOneNonZero (3 * m))) k
  in (S (oddPartDropTime (3 * m + 1) + s') ** syrRealizeStep m mOdd k s' eq')

-- The height-matching equality for a positive starting value.

public export
oddPartHeightEqPos :
  (n : Nat) -> (t : Nat) -> (s' : Nat) ->
  (eq' : posValue (iter s' Col (MkPos (oddFactor n)))
          = oddValue (iter t Syr (MkOddPos (oddFactor n)))) ->
  posValue (iter (oddPartDropTime n + s') Col (MkPos n))
    = oddValue (iter t Syr (oddPart (MkPos n)))
oddPartHeightEqPos n t s' eq' =
  rewrite iterPlus (oddPartDropTime n) s' Col (MkPos n) in
  rewrite normalizeToPos n in
  eq'

-- The orbit-simulation height bound, for every positive integer (and 0).

public export
oddPartHeightBoundAt :
  (pos : Pos) -> (t : Nat) ->
  (s : Nat ** Leq (posValue (iter s Col pos)) (oddValue (iter t Syr (oddPart pos))))
oddPartHeightBoundAt (MkPos Z) t = (0 ** LeqZ)
oddPartHeightBoundAt (MkPos (S k)) t =
  let (s' ** eq') =
        syrRealize (oddFactor (S k))
                   (oddFactorOdd (S k) (succNonZero k)) t
  in (oddPartDropTime (S k) + s'
        ** leqOfEq (oddPartHeightEqPos (S k) t s' eq'))

-- The proven odd-part orbit simulation.

public export
provenOddPartOrbitSimulation : OddPartOrbitSimulation
provenOddPartOrbitSimulation =
  MkOrbitSimulation
    (\pos, t => fst (oddPartHeightBoundAt pos t))
    (\pos, t => snd (oddPartHeightBoundAt pos t))

-- Coherence with the generic simulation algebra (`orbitSimulationId`,
-- `orbitSimulationCompose` from `TaoCollatz.Core`): the odd-part simulation
-- composes with the identity simulation on either side and still typechecks as
-- an `OddPartOrbitSimulation`.  This certifies that the concrete Collatz =>
-- Syracuse transfer is an instance of the reusable simulation category rather
-- than a one-off construction.

public export
oddPartOrbitSimulationViaAlgebraL : OddPartOrbitSimulation
oddPartOrbitSimulationViaAlgebraL =
  orbitSimulationCompose orbitSimulationId provenOddPartOrbitSimulation

public export
oddPartOrbitSimulationViaAlgebraR : OddPartOrbitSimulation
oddPartOrbitSimulationViaAlgebraR =
  orbitSimulationCompose provenOddPartOrbitSimulation orbitSimulationId
