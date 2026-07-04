module TaoCollatz.DynamicsExtra

-- Further genuine, fully computational facts about the concrete Collatz /
-- Syracuse dynamics of `TaoCollatz.Dynamics`.  These are elementary invariants
-- that round out the odd-part picture and provide reusable single-step rewrite
-- lemmas, together with a handful of machine-checked first-passage examples.
--
-- Everything here is real mathematics: no placeholders, no `believe_me`, no
-- axioms; every definition is total and every lemma is proved from first
-- principles (or checked by computation).

import TaoCollatz.Core
import TaoCollatz.Dynamics
import TaoCollatz.OddPart

%default total

--------------------------------------------------------------------------------
-- Single-step rewrite lemmas.
--------------------------------------------------------------------------------

||| One Collatz step on an even number halves it.
public export
colEvenStep : (n : Nat) -> isEven n = True -> Col (MkPos n) = MkPos (half n)
colEvenStep n ev = rewrite ev in Refl

||| One Collatz step on an odd number is the `3n+1` map (restated from
||| `TaoCollatz.OddPart.colOdd` for convenience).
public export
colOddStep : (n : Nat) -> isEven n = False -> Col (MkPos n) = MkPos (3 * n + 1)
colOddStep = colOdd

||| The odd part of an odd number is itself.
public export
oddPartOfOdd : (n : Nat) -> isEven n = False -> oddPart (MkPos n) = MkOddPos n
oddPartOfOdd n odd = cong MkOddPos (oddFactorFixed n odd)

||| `oddPart` fixes any element of `OddPos` (viewed back in `Pos`) that is
||| genuinely odd.
public export
oddPartFixesOdd :
  (o : OddPos) -> isEven (oddValue o) = False -> oddPart (oddAsPos o) = o
oddPartFixesOdd (MkOddPos n) odd = cong MkOddPos (oddFactorFixed n odd)

||| The Syracuse map always lands on an odd value (restated from
||| `TaoCollatz.OddPart.syrValueOdd`).
public export
syrIsOdd : (o : OddPos) -> isEven (oddValue (Syr o)) = False
syrIsOdd = syrValueOdd

--------------------------------------------------------------------------------
-- The odd-part drop time vanishes exactly on odd numbers.
--------------------------------------------------------------------------------

||| An odd number is already normalised: its odd-part drop time is zero.
public export
oddPartDropTimeOdd : (n : Nat) -> isEven n = False -> oddPartDropTime n = Z
oddPartDropTimeOdd Z odd = absurd odd
oddPartDropTimeOdd (S k) odd = rewrite odd in Refl

||| On an odd number the Collatz orbit starts exactly at that number.
public export
oddNormalizeFixed :
  (n : Nat) -> isEven n = False ->
  iter (oddPartDropTime n) Col (MkPos n) = MkPos n
oddNormalizeFixed n odd =
  rewrite oddPartDropTimeOdd n odd in Refl

--------------------------------------------------------------------------------
-- Machine-checked first-passage examples.
--------------------------------------------------------------------------------

||| `4 -> 2 -> 1` under the Collatz map.
public export
colFourToOne : iter 2 Col (MkPos 4) = MkPos 1
colFourToOne = Refl

||| The Collatz orbit of 4 reaches height 1.
public export
colFourBelowOne : ColBelow (MkPos 4) 1
colFourBelowOne = Reaches 2 (leqRefl 1)

||| `16 -> 8 -> 4 -> 2 -> 1` under the Collatz map.
public export
colSixteenToOne : iter 4 Col (MkPos 16) = MkPos 1
colSixteenToOne = Refl

||| The Collatz orbit of 16 reaches height 1.
public export
colSixteenBelowOne : ColBelow (MkPos 16) 1
colSixteenBelowOne = Reaches 4 (leqRefl 1)

||| The Syracuse orbit of 7 reaches height 1: `7 -> 11 -> 17 -> 13 -> 5 -> 1`.
public export
syrSevenToOne : iter 5 Syr (MkOddPos 7) = MkOddPos 1
syrSevenToOne = Refl

||| The Syracuse orbit of 7 reaches height 1.
public export
syrSevenBelowOne : SyrBelow (MkOddPos 7) 1
syrSevenBelowOne = Reaches 5 (leqRefl 1)
