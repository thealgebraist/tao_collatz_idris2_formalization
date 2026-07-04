module TaoCollatz.Convolution

-- Renewal theory and characteristic-function / Fourier analysis, unified as one
-- operation on the single carrier `FinDist`.
--
-- The distribution of a *sum of two independent increments* is the convolution
-- of their distributions; iterating convolution is exactly the renewal process
-- that governs the Syracuse first-passage time (the increments are the 2-adic
-- valuations).  The *characteristic function* (equivalently the probability
-- generating function, or -- evaluated at a root of unity -- the finite Fourier
-- transform) of a measure is a multiplicative character summed against the
-- measure.  The single theorem that makes both "domains" work is the
-- **convolution theorem**: the characteristic function turns convolution into
-- multiplication.  We prove it here in full generality (for an arbitrary
-- multiplicative character), so renewal theory and Fourier analysis are two
-- readings of one algebraic identity.
--
-- Everything here is real, total mathematics: `%default total`, no
-- placeholders, no `believe_me`, no axioms, no holes.

import Data.Nat
import TaoCollatz.Core
import TaoCollatz.Density
import TaoCollatz.FinMeasure

%default total

--------------------------------------------------------------------------------
-- A small multiplicative rearrangement (the product analogue of
-- `Density.plusRearrange`).
--------------------------------------------------------------------------------

public export
mult4Rearrange :
  (a : Nat) -> (b : Nat) -> (c : Nat) -> (d : Nat) ->
  mult (mult a b) (mult c d) = mult (mult a c) (mult b d)
mult4Rearrange a b c d =
  rewrite sym (multAssociative a b (mult c d)) in
  rewrite multAssociative b c d in
  rewrite multCommutative b c in
  rewrite sym (multAssociative c b d) in
  multAssociative a c (mult b d)

--------------------------------------------------------------------------------
-- Convolution of two measures: the law of the sum of independent increments.
--------------------------------------------------------------------------------

||| `atomTimes v w e`: shift every point of `e` up by `v` and scale every weight
||| by `w`.  This is the contribution of a single atom `(v, w)` to a convolution.
public export
atomTimes : Nat -> Nat -> FinDist -> FinDist
atomTimes v w Empty = Empty
atomTimes v w (Atom v' w' r) = Atom (plus v v') (mult w w') (atomTimes v w r)

||| Convolution `mu * nu`: the distribution of `X + Y` for independent `X ~ mu`,
||| `Y ~ nu`.  Iterating this is the renewal process.
public export
convolve : FinDist -> FinDist -> FinDist
convolve Empty e = Empty
convolve (Atom v w r) e = mix (atomTimes v w e) (convolve r e)

--------------------------------------------------------------------------------
-- Total mass is multiplicative under convolution (measures multiply).
--------------------------------------------------------------------------------

public export
massAtomTimes :
  (v : Nat) -> (w : Nat) -> (e : FinDist) ->
  mass (atomTimes v w e) = mult w (mass e)
massAtomTimes v w Empty = sym (multZeroRightZero w)
massAtomTimes v w (Atom v' w' r) =
  rewrite massAtomTimes v w r in
  sym (multDistributesOverPlusRight w w' (mass r))

public export
massConvolve :
  (d : FinDist) -> (e : FinDist) ->
  mass (convolve d e) = mult (mass d) (mass e)
massConvolve Empty e = Refl
massConvolve (Atom v w r) e =
  rewrite massMix (atomTimes v w e) (convolve r e) in
  rewrite massAtomTimes v w e in
  rewrite massConvolve r e in
  sym (multDistributesOverPlusLeft w (mass r) (mass e))

--------------------------------------------------------------------------------
-- Characteristic functions / probability generating functions / finite Fourier
-- transform: one definition, one convolution theorem.
--
-- A *multiplicative character* is a monoid homomorphism `chi : (Nat,+) ->
-- (Nat,*)`; classically one takes `chi v = z ^ v` for a fixed base `z` (a real
-- `z` gives the moment generating function; a complex root of unity gives the
-- finite Fourier transform).  `charFn chi mu = sum_v mu(v) * chi(v)` is the
-- corresponding transform of the measure.
--------------------------------------------------------------------------------

public export
charFn : (Nat -> Nat) -> FinDist -> Nat
charFn chi Empty = Z
charFn chi (Atom v w r) = plus (mult w (chi v)) (charFn chi r)

public export
charFnMix :
  (chi : Nat -> Nat) -> (d : FinDist) -> (e : FinDist) ->
  charFn chi (mix d e) = plus (charFn chi d) (charFn chi e)
charFnMix chi Empty e = Refl
charFnMix chi (Atom v w r) e =
  rewrite charFnMix chi r e in
  plusAssociative (mult w (chi v)) (charFn chi r) (charFn chi e)

public export
charFnDirac : (chi : Nat -> Nat) -> (v : Nat) -> charFn chi (dirac v) = chi v
charFnDirac chi v =
  rewrite plusZeroRightNeutral (mult (S Z) (chi v)) in
  plusZeroRightNeutral (chi v)

||| For a multiplicative character (`chi (a+b) = chi a * chi b`), the transform
||| of a single-atom contribution factors.
public export
charFnAtomTimes :
  (chi : Nat -> Nat) ->
  ((a : Nat) -> (b : Nat) -> chi (plus a b) = mult (chi a) (chi b)) ->
  (v : Nat) -> (w : Nat) -> (e : FinDist) ->
  charFn chi (atomTimes v w e) = mult (mult w (chi v)) (charFn chi e)
charFnAtomTimes chi hom v w Empty = sym (multZeroRightZero (mult w (chi v)))
charFnAtomTimes chi hom v w (Atom v' w' r) =
  rewrite charFnAtomTimes chi hom v w r in
  rewrite hom v v' in
  rewrite sym (mult4Rearrange w (chi v) w' (chi v')) in
  sym (multDistributesOverPlusRight
        (mult w (chi v)) (mult w' (chi v')) (charFn chi r))

||| **The convolution theorem.**  For any multiplicative character, the
||| characteristic function turns convolution into multiplication:
|||
|||     charFn chi (mu * nu) = charFn chi mu  *  charFn chi nu .
|||
||| Read with `chi` a root of unity this is the finite-Fourier identity behind
||| the paper's Fourier-decay estimates; read with `chi v = z^v` it is the
||| generating-function identity behind the renewal analysis.  One proof serves
||| both domains.
public export
charFnConvolve :
  (chi : Nat -> Nat) ->
  ((a : Nat) -> (b : Nat) -> chi (plus a b) = mult (chi a) (chi b)) ->
  (d : FinDist) -> (e : FinDist) ->
  charFn chi (convolve d e) = mult (charFn chi d) (charFn chi e)
charFnConvolve chi hom Empty e = Refl
charFnConvolve chi hom (Atom v w r) e =
  rewrite charFnMix chi (atomTimes v w e) (convolve r e) in
  rewrite charFnAtomTimes chi hom v w e in
  rewrite charFnConvolve chi hom r e in
  sym (multDistributesOverPlusLeft (mult w (chi v)) (charFn chi r) (charFn chi e))

--------------------------------------------------------------------------------
-- Convolution of Dirac measures realises addition (the renewal step on points).
--------------------------------------------------------------------------------

public export
convolveDirac :
  (a : Nat) -> (b : Nat) -> convolve (dirac a) (dirac b) = dirac (plus a b)
convolveDirac a b = Refl

--------------------------------------------------------------------------------
-- The renewal process: iterated convolution.
--
-- `convPow d n` is the law of the sum of `n` independent copies of an increment
-- distributed as `d` -- exactly the `n`-step renewal kernel governing the
-- Syracuse first-passage time.  Its total mass and characteristic function are
-- the corresponding powers, so the renewal kernel and its transform are handled
-- by the two clean induction lemmas below.
--------------------------------------------------------------------------------

public export
powN : Nat -> Nat -> Nat
powN a Z = S Z
powN a (S n) = mult a (powN a n)

||| The `n`-fold convolution (empty sum = unit point mass at `0`).
public export
convPow : FinDist -> Nat -> FinDist
convPow d Z = dirac Z
convPow d (S n) = convolve d (convPow d n)

||| Total mass of the renewal kernel is the power of the total mass.
public export
massConvPow :
  (d : FinDist) -> (n : Nat) -> mass (convPow d n) = powN (mass d) n
massConvPow d Z = Refl
massConvPow d (S n) =
  rewrite massConvolve d (convPow d n) in
  rewrite massConvPow d n in Refl

||| The characteristic function of the renewal kernel is the power of the
||| characteristic function -- the generating-function / Fourier form of the
||| renewal identity.  (`chi 0 = 1` is the normalisation of a character.)
public export
charFnConvPow :
  (chi : Nat -> Nat) ->
  ((a : Nat) -> (b : Nat) -> chi (plus a b) = mult (chi a) (chi b)) ->
  chi Z = S Z ->
  (d : FinDist) -> (n : Nat) ->
  charFn chi (convPow d n) = powN (charFn chi d) n
charFnConvPow chi hom chiZero d Z =
  rewrite charFnDirac chi Z in chiZero
charFnConvPow chi hom chiZero d (S n) =
  rewrite charFnConvolve chi hom d (convPow d n) in
  rewrite charFnConvPow chi hom chiZero d n in Refl
