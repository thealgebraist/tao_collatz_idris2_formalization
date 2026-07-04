module TaoCollatz.DensityClosure

-- Finite (list-indexed) closure of the natural-density model of "almost all"
-- (`TaoCollatz.Density`).  The base module proves *binary* closure
-- (`orNegligible`, `andAlmostAll`).  Here we lift those to *finite families*:
-- a finite union of negligible sets is negligible, and a finite intersection of
-- "almost all" sets is "almost all".  These are exactly the finite-additivity /
-- finite-intersection properties a measure-of-smallness is expected to have,
-- now proved for arbitrarily many sets at once, by induction on the list.
--
-- As with the rest of the density development this is genuine, total
-- mathematics: no placeholders, no `believe_me`, no axioms, no holes; every
-- definition is total and every lemma is proved from first principles on top of
-- the binary closure lemmas of `TaoCollatz.Density`.
--
-- Main results:
--
--   * `orListNegligible`  — if every member of a finite list of sets is
--       negligible, so is their union `orList`.
--   * `andListAlmostAll`  — if every member of a finite list of sets is
--       "almost all", so is their intersection `andList`.
--   * `replicateOrNegligible` / `replicateAndAlmostAll` — the special case of a
--       repeated set, sanity-checking the general lemmas.

import Data.List
import TaoCollatz.Core
import TaoCollatz.Density

%default total

--------------------------------------------------------------------------------
-- Finite unions and intersections of indicator predicates.
--------------------------------------------------------------------------------

||| Pointwise `or` over a finite list of indicator predicates.  The empty union
||| is the empty set (`False` everywhere).
public export
orList : List (Nat -> Bool) -> (Nat -> Bool)
orList [] = \_ => False
orList (p :: ps) = \n => p n || orList ps n

||| Pointwise `and` over a finite list of indicator predicates.  The empty
||| intersection is the whole space (`True` everywhere).
public export
andList : List (Nat -> Bool) -> (Nat -> Bool)
andList [] = \_ => True
andList (p :: ps) = \n => p n && andList ps n

--------------------------------------------------------------------------------
-- "Every member of the list is negligible / almost all".
--------------------------------------------------------------------------------

public export
data AllNegligible : List (Nat -> Bool) -> Type where
  ANNil  : AllNegligible []
  ANCons : Negligible p -> AllNegligible ps -> AllNegligible (p :: ps)

public export
data AllAlmostAll : List (Nat -> Bool) -> Type where
  AANil  : AllAlmostAll []
  AACons : AlmostAll p -> AllAlmostAll ps -> AllAlmostAll (p :: ps)

--------------------------------------------------------------------------------
-- Finite closure.
--------------------------------------------------------------------------------

||| A finite union of negligible sets is negligible.
public export
orListNegligible :
  {ps : List (Nat -> Bool)} -> AllNegligible ps -> Negligible (orList ps)
orListNegligible ANNil = negligibleFalse
orListNegligible (ANCons np rest) =
  orNegligible np (orListNegligible rest)

||| A finite intersection of "almost all" sets is "almost all".
public export
andListAlmostAll :
  {ps : List (Nat -> Bool)} -> AllAlmostAll ps -> AlmostAll (andList ps)
andListAlmostAll AANil = almostAllTrue
andListAlmostAll (AACons ap rest) =
  andAlmostAll ap (andListAlmostAll rest)

--------------------------------------------------------------------------------
-- The repeated-set special case (a sanity check on the general lemmas).
--------------------------------------------------------------------------------

public export
allNegligibleReplicate :
  (m : Nat) -> {p : Nat -> Bool} -> Negligible p ->
  AllNegligible (replicate m p)
allNegligibleReplicate Z _ = ANNil
allNegligibleReplicate (S m) np = ANCons np (allNegligibleReplicate m np)

public export
allAlmostAllReplicate :
  (m : Nat) -> {p : Nat -> Bool} -> AlmostAll p ->
  AllAlmostAll (replicate m p)
allAlmostAllReplicate Z _ = AANil
allAlmostAllReplicate (S m) ap = AACons ap (allAlmostAllReplicate m ap)

||| The union of finitely many copies of a negligible set is negligible.
public export
replicateOrNegligible :
  (m : Nat) -> {p : Nat -> Bool} -> Negligible p ->
  Negligible (orList (replicate m p))
replicateOrNegligible m np =
  orListNegligible (allNegligibleReplicate m np)

||| The intersection of finitely many copies of an "almost all" set is
||| "almost all".
public export
replicateAndAlmostAll :
  (m : Nat) -> {p : Nat -> Bool} -> AlmostAll p ->
  AlmostAll (andList (replicate m p))
replicateAndAlmostAll m ap =
  andListAlmostAll (allAlmostAllReplicate m ap)
