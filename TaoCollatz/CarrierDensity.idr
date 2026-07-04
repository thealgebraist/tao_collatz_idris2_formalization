module TaoCollatz.CarrierDensity

-- The genuine natural-density model of "almost all" (`TaoCollatz.Density`),
-- transported to the two carriers that actually occur in the main theorem:
-- `Pos` (the domain of the Collatz map) and `OddPos` (the domain of the
-- Syracuse map).  Both are thin wrappers around `Nat`, so a `Bool`-valued
-- predicate on them reindexes to an indicator on `Nat` and inherits the whole
-- density algebra verbatim.
--
-- This exhibits a *genuine model* of the largeness algebra the reduction chain
-- of `TaoCollatz.Large` abstracts over (closure under supersets and finite
-- intersection, non-degeneracy), on exactly the carriers `Theorem13` /
-- `Theorem16` are stated over.  Everything is real mathematics: no
-- placeholders, no `believe_me`, no axioms; every lemma reduces to the proved
-- lemmas of `TaoCollatz.Density` / `TaoCollatz.DensityExtra`.

import TaoCollatz.Core
import TaoCollatz.Dynamics
import TaoCollatz.Density
import TaoCollatz.DensityExtra

%default total

--------------------------------------------------------------------------------
-- Density-based "almost all" over `Pos`.
--------------------------------------------------------------------------------

||| A `Bool`-valued predicate on `Pos` is negligible when its reindexing to
||| `Nat` has natural density zero.
public export
NegligiblePos : (Pos -> Bool) -> Type
NegligiblePos p = Negligible (\n => p (MkPos n))

||| Almost every `Pos` satisfies `p` when the complement of `p` is negligible.
public export
AlmostAllPosD : (Pos -> Bool) -> Type
AlmostAllPosD p = AlmostAll (\n => p (MkPos n))

public export
almostAllPosMono :
  {p : Pos -> Bool} -> {q : Pos -> Bool} ->
  ((x : Pos) -> p x = True -> q x = True) ->
  AlmostAllPosD p -> AlmostAllPosD q
almostAllPosMono sub ap =
  almostAllMono (\n => sub (MkPos n)) ap

public export
andAlmostAllPos :
  {p : Pos -> Bool} -> {q : Pos -> Bool} ->
  AlmostAllPosD p -> AlmostAllPosD q ->
  AlmostAllPosD (\x => p x && q x)
andAlmostAllPos ap aq = andAlmostAll ap aq

public export
almostAllPosTrue : AlmostAllPosD (\_ => True)
almostAllPosTrue = almostAllTrue

||| A cofinite subset of `Pos` (all values with size `>= b`) is almost all.
public export
almostAllPosCofinite :
  (p : Pos -> Bool) -> (b : Nat) ->
  ((n : Nat) -> Leq b n -> p (MkPos n) = True) ->
  AlmostAllPosD p
almostAllPosCofinite p b h =
  almostAllCofinite (\n => p (MkPos n)) b h

||| Non-degeneracy: the whole of `Pos` is not negligible.
public export
allPosNotNegligible : NegligiblePos (\_ => True) -> Void
allPosNotNegligible neg = allNotNegligible neg

--------------------------------------------------------------------------------
-- Density-based "almost all" over `OddPos`.
--------------------------------------------------------------------------------

public export
NegligibleOdd : (OddPos -> Bool) -> Type
NegligibleOdd p = Negligible (\n => p (MkOddPos n))

public export
AlmostAllOddD : (OddPos -> Bool) -> Type
AlmostAllOddD p = AlmostAll (\n => p (MkOddPos n))

public export
almostAllOddMono :
  {p : OddPos -> Bool} -> {q : OddPos -> Bool} ->
  ((x : OddPos) -> p x = True -> q x = True) ->
  AlmostAllOddD p -> AlmostAllOddD q
almostAllOddMono sub ap =
  almostAllMono (\n => sub (MkOddPos n)) ap

public export
andAlmostAllOdd :
  {p : OddPos -> Bool} -> {q : OddPos -> Bool} ->
  AlmostAllOddD p -> AlmostAllOddD q ->
  AlmostAllOddD (\x => p x && q x)
andAlmostAllOdd ap aq = andAlmostAll ap aq

public export
almostAllOddTrue : AlmostAllOddD (\_ => True)
almostAllOddTrue = almostAllTrue

public export
almostAllOddCofinite :
  (p : OddPos -> Bool) -> (b : Nat) ->
  ((n : Nat) -> Leq b n -> p (MkOddPos n) = True) ->
  AlmostAllOddD p
almostAllOddCofinite p b h =
  almostAllCofinite (\n => p (MkOddPos n)) b h

public export
allOddNotNegligible : NegligibleOdd (\_ => True) -> Void
allOddNotNegligible neg = allNotNegligible neg
