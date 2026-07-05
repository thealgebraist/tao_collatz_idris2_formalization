module TaoCollatz.DensityTransfer
import TaoCollatz.Core
import TaoCollatz.Dynamics
import TaoCollatz.OddPart
import TaoCollatz.TwoAdic
import TaoCollatz.Density
import Data.Nat
%default total

public export
halfLeMono : (a : Nat) -> (b : Nat) -> Leq a b -> Leq (half a) (half b)
halfLeMono Z b _ = LeqZ
halfLeMono (S Z) (S b) _ = LeqZ
halfLeMono (S (S k)) (S Z) (LeqS h) = void (notLeqSZ h)
halfLeMono (S (S k)) (S (S j)) (LeqS (LeqS h)) = LeqS (halfLeMono k j h)

public export
halfSuccLe : (m : Nat) -> Leq (half (S m)) m
halfSuccLe Z = LeqZ
halfSuccLe (S k) = LeqS (halfLe k)

public export
oddFactorFuelZero : (f : Nat) -> oddFactorFuel f 0 = 0
oddFactorFuelZero Z = Refl
oddFactorFuelZero (S f) = oddFactorFuelZero f

-- any fuel >= n computes the canonical odd factor
public export
canon : (b : Nat) -> (n : Nat) -> (f : Nat) ->
        Leq n b -> Leq n f -> oddFactorFuel f n = oddFactor n
canon b Z f _ _ = oddFactorFuelZero f
canon Z (S n1) f le _ = void (notLeqSZ le)
canon b (S n1) Z _ lef = void (notLeqSZ lef)
canon (S b') (S n1) (S f') le lef with (isEven (S n1)) proof ev
  _ | False = Refl
  _ | True =
      let hn : Nat
          hn = half (S n1)
          -- half (S n1) <= b'
          leB : Leq hn b'
          leB = leqTrans (halfLeMono (S n1) (S b') le) (halfSuccLe b')
          -- half (S n1) <= f'
          leF : Leq hn f'
          leF = leqTrans (halfLeMono (S n1) (S f') lef) (halfSuccLe f')
          -- half (S n1) <= n1
          leN : Leq hn n1
          leN = halfSuccLe n1
          ih1 : oddFactorFuel f' hn = oddFactor hn
          ih1 = canon b' hn f' leB leF
          ih2 : oddFactorFuel n1 hn = oddFactor hn
          ih2 = canon b' hn n1 leB leN
      in trans ih1 (sym ih2)

public export
oddFactorEnough : (n : Nat) -> (f : Nat) -> Leq n f -> oddFactorFuel f n = oddFactor n
oddFactorEnough n f lef = canon f n f lef lef

public export
doubleEven : (m : Nat) -> isEven (plus m m) = True
doubleEven Z = Refl
doubleEven (S m) = rewrite sym (plusSuccRightSucc m m) in doubleEven m

public export
halfDouble : (m : Nat) -> half (plus m m) = m
halfDouble Z = Refl
halfDouble (S m) = rewrite sym (plusSuccRightSucc m m) in cong S (halfDouble m)

public export
isEvenSuccFlip : (n : Nat) -> isEven (S n) = not (isEven n)
isEvenSuccFlip Z = Refl
isEvenSuccFlip (S Z) = Refl
isEvenSuccFlip (S (S k)) = isEvenSuccFlip k

public export
oddOfDoubleSucc : (m : Nat) -> isEven (S (plus m m)) = False
oddOfDoubleSucc m = trans (isEvenSuccFlip (plus m m)) (cong not (doubleEven m))

public export
leqDoublePred : (m : Nat) -> Leq (S m) (S (plus m m))
leqDoublePred m = LeqS (leqPlusExtraRight m m)

public export
oddFactorDoubleEq : (m : Nat) -> oddFactor (plus m m) = oddFactor m
oddFactorDoubleEq Z = Refl
oddFactorDoubleEq (S m) =
  -- plus (S m) (S m) = S (S (plus m m)); even; half = S m
  rewrite sym (plusSuccRightSucc m m) in
    -- goal: oddFactorFuel (S (S (plus m m))) (S (S (plus m m))) = oddFactor (S m)
    rewrite doubleEven m in
      -- reduces to oddFactorFuel (S (plus m m)) (half (S (S (plus m m)))) = oddFactor (S m)
      -- half (S (S (plus m m))) = S (half (plus m m)) = S m
      rewrite halfDouble m in
        oddFactorEnough (S m) (S (plus m m)) (leqDoublePred m)

public export
pullc : (Nat -> Bool) -> Nat -> Bool
pullc b n = b (oddFactor n)

public export
oddHits : (Nat -> Bool) -> Nat -> Nat
oddHits b n = count (\m => b (S (plus m m))) n

public export
rearr4 : (a, b, c, d : Nat) ->
         plus a (plus b (plus c d)) = plus (plus b c) (plus a d)
rearr4 a b c d =
  rewrite plusAssociative b c d in
  rewrite plusAssociative a (plus b c) d in
  rewrite plusCommutative a (plus b c) in
  rewrite sym (plusAssociative (plus b c) a d) in
  Refl

public export
countPullDouble : (b : Nat -> Bool) -> (M : Nat) ->
  count (pullc b) (plus M M) = plus (count (pullc b) M) (oddHits b M)
countPullDouble b Z = Refl
countPullDouble b (S m) =
  rewrite sym (plusSuccRightSucc m m) in
  -- LHS is count (pullc b) (S (S (plus m m)))
  -- pullc b (S (plus m m)) = b (oddFactor (S (plus m m))) = b (S (plus m m))
  rewrite oddFactorFixed (S (plus m m)) (oddOfDoubleSucc m) in
  -- pullc b (plus m m) = b (oddFactor (plus m m)) = b (oddFactor m)
  rewrite oddFactorDoubleEq m in
  -- now use IH
  rewrite countPullDouble b m in
  rearr4 (indicator (b (S (plus m m))))
         (indicator (b (oddFactor m)))
         (count (pullc b) m)
         (oddHits b m)

public export
evenHits : (Nat -> Bool) -> Nat -> Nat
evenHits b n = count (\m => b (plus m m)) n

public export
countParitySplit : (b : Nat -> Bool) -> (M : Nat) ->
  count b (plus M M) = plus (evenHits b M) (oddHits b M)
countParitySplit b Z = Refl
countParitySplit b (S m) =
  rewrite sym (plusSuccRightSucc m m) in
  rewrite countParitySplit b m in
  rearr4 (indicator (b (S (plus m m))))
         (indicator (b (plus m m)))
         (evenHits b m)
         (oddHits b m)

public export
oddHitsLe : (b : Nat -> Bool) -> (M : Nat) ->
  Leq (oddHits b M) (count b (plus M M))
oddHitsLe b m =
  leqCastR (leqPlusExtraLeft (evenHits b m) (oddHits b m))
           (sym (countParitySplit b m))

public export
countArgMono : (p : Nat -> Bool) -> (a : Nat) -> (b : Nat) ->
  Leq a b -> Leq (count p a) (count p b)
countArgMono p a b le =
  case leqExists le of
    (d ** eq) => rewrite eq in go p a d
  where
    go : (p : Nat -> Bool) -> (a : Nat) -> (d : Nat) ->
         Leq (count p a) (count p (plus a d))
    go p a Z = rewrite plusZeroRightNeutral a in leqRefl (count p a)
    go p a (S d) =
      rewrite sym (plusSuccRightSucc a d) in
      leqTrans (go p a d)
               (leqPlusExtraLeft (indicator (p (plus a d))) (count p (plus a d)))

public export
parityDecomp : (n : Nat) ->
  Either (n = plus (half n) (half n)) (n = S (plus (half n) (half n)))
parityDecomp Z = Left Refl
parityDecomp (S Z) = Right Refl
parityDecomp (S (S k)) =
  case parityDecomp k of
    Left eq =>
      Left (rewrite sym (plusSuccRightSucc (half k) (half k)) in cong (S . S) eq)
    Right eq =>
      Right (rewrite sym (plusSuccRightSucc (half k) (half k)) in cong (S . S) eq)

public export
leqOne : (b : Bool) -> Leq (indicator b) (S Z)
leqOne True = leqRefl (S Z)
leqOne False = LeqZ

public export
pullRecStep : (b : Nat -> Bool) -> (n : Nat) ->
  Leq (count (pullc b) n)
      (plus (count (pullc b) (half n)) (S (count b n)))
pullRecStep b n =
  case parityDecomp n of
    Left eq =>
      let h : Nat
          h = half n
          e1 : count (pullc b) n = plus (count (pullc b) h) (oddHits b h)
          e1 = trans (cong (count (pullc b)) eq) (countPullDouble b h)
          oh : Leq (oddHits b h) (count b n)
          oh = leqCastR (oddHitsLe b h) (cong (count b) (sym eq))
          bnd : Leq (plus (count (pullc b) h) (oddHits b h))
                    (plus (count (pullc b) h) (S (count b n)))
          bnd = leqAdd (leqRefl (count (pullc b) h))
                       (leqTrans oh (leqSuccRight (count b n)))
      in leqCastL e1 bnd
    Right eq =>
      let h : Nat
          h = half n
          e1 : count (pullc b) n
               = plus (indicator (pullc b (plus h h)))
                      (plus (count (pullc b) h) (oddHits b h))
          e1 = trans (cong (count (pullc b)) eq)
                     (cong (\z => plus (indicator (pullc b (plus h h))) z)
                           (countPullDouble b h))
          -- oddHits b h <= count b (plus h h) <= count b n
          ohn : Leq (oddHits b h) (count b n)
          ohn = leqTrans (oddHitsLe b h)
                         (countArgMono b (plus h h) n
                            (leqCastR (leqSuccRight (plus h h)) (sym eq)))
          -- indicator <= 1
          ind1 : Leq (indicator (pullc b (plus h h))) (S Z)
          ind1 = leqOne (pullc b (plus h h))
          bnd : Leq (plus (indicator (pullc b (plus h h)))
                          (plus (count (pullc b) h) (oddHits b h)))
                    (plus (S Z) (plus (count (pullc b) h) (count b n)))
          bnd = leqAdd ind1 (leqAdd (leqRefl (count (pullc b) h)) ohn)
          -- rearrange plus 1 (x + y) = plus x (S y)
          rr : plus (S Z) (plus (count (pullc b) h) (count b n))
               = plus (count (pullc b) h) (S (count b n))
          rr = plusSuccRightSucc (count (pullc b) h) (count b n)
      in leqCastL e1 (leqCastR bnd rr)

-- ============ density (natural-density) transfer along oddFactor ============

public export
db : Nat -> Nat
db x = plus x x

public export
qd : Nat -> Nat
qd x = plus (db x) (db x)

public export
qdCancel : {a, b : Nat} -> Leq (qd a) (qd b) -> Leq a b
qdCancel h = leqHalf (leqHalf h)

public export
dbMono : {a, b : Nat} -> Leq a b -> Leq (db a) (db b)
dbMono h = leqAdd h h

public export
qdMono : {a, b : Nat} -> Leq a b -> Leq (qd a) (qd b)
qdMono h = leqAdd (dbMono h) (dbMono h)

public export
dbPlus : (x, y : Nat) -> db (plus x y) = plus (db x) (db y)
dbPlus x y = plusRearrange x y x y

public export
qdPlus : (x, y : Nat) -> qd (plus x y) = plus (qd x) (qd y)
qdPlus x y =
  rewrite dbPlus x y in plusRearrange (db x) (db y) (db x) (db y)

-- 2 * half n <= n
public export
halfDoubleLe : (n : Nat) -> Leq (db (half n)) n
halfDoubleLe Z = LeqZ
halfDoubleLe (S Z) = LeqZ
halfDoubleLe (S (S k)) =
  rewrite sym (plusSuccRightSucc (half k) (half k)) in
  LeqS (LeqS (halfDoubleLe k))

public export
qdMultRight : (a, p : Nat) -> qd (mult a p) = mult a (qd p)
qdMultRight a p =
  rewrite sym (multDistributesOverPlusRight a p p) in
  rewrite sym (multDistributesOverPlusRight a (plus p p) (plus p p)) in
  Refl

public export
qdSkSucc : (k : Nat) -> qd (S k) = S (pred (qd (S k)))
qdSkSucc k = Refl

public export
negFeed : (b : Nat -> Bool) -> Negligible b -> (k : Nat) ->
  (n0 : Nat ** ((n : Nat) -> Leq n0 n -> Leq (mult (count b n) (qd (S k))) n))
negFeed b neg k =
  let (n0 ** pf) = neg (pred (qd (S k)))
  in (n0 ** \n, le =>
        rewrite qdSkSucc k in pf n le)

public export
dbLeToHalf : (q : Nat) -> (n : Nat) -> Leq (db q) n -> Leq q (half n)
dbLeToHalf q n h = leqCastL (sym (halfDouble q)) (halfLeMono (db q) n h)

public export
mult3Eq : (x : Nat) -> mult 3 x = plus x (db x)
mult3Eq x = rewrite plusZeroRightNeutral x in Refl

-- 3h + qp <= 2n  given 2h <= n and qp <= h
public export
finalIneq : (h : Nat) -> (qp : Nat) -> (n : Nat) ->
  Leq (db h) n -> Leq qp h ->
  Leq (plus (plus h (db h)) qp) (db n)
finalIneq h qp n dh qh =
  let e : (plus (plus h (db h)) qp = plus (db h) (plus h qp))
      e = trans (cong (\z => plus z qp) (plusAssociative h h h))
                (sym (plusAssociative (plus h h) h qp))
      hq : Leq (plus h qp) n
      hq = leqTrans (leqAdd (leqRefl h) qh) dh
  in leqCastL e (leqAdd dh hq)

public export
rearrB : (a, c, q, n : Nat) ->
  plus (plus a c) (plus q n) = plus (plus (plus a q) n) c
rearrB a c q n =
  trans (plusRearrange a c q n)
        (trans (cong (plus (plus a q)) (plusCommutative c n))
               (plusAssociative (plus a q) n c))

public export
combineFinal : (a, c0, qp, n : Nat) ->
  Leq (plus a qp) (db n) ->
  Leq (plus (plus a c0) (plus qp n)) (plus (mult 3 n) c0)
combineFinal a c0 qp n hyp =
  let e2 : (plus (plus (db n) n) c0 = plus (mult 3 n) c0)
      e2 = cong (\z => plus z c0)
                (trans (plusCommutative (db n) n) (sym (mult3Eq n)))
  in leqCastR
       (leqCastL (rearrB a c0 qp n)
          (leqAdd (leqAdd hyp (leqRefl n)) (leqRefl c0)))
       e2

public export
trichLeq : (a : Nat) -> (b : Nat) -> Either (Leq a b) (Leq (S b) a)
trichLeq Z b = Left LeqZ
trichLeq (S a) Z = Right (LeqS LeqZ)
trichLeq (S a) (S b) =
  case trichLeq a b of
    Left h => Left (LeqS h)
    Right h => Right (LeqS h)

public export
qd4 : (x : Nat) -> plus (mult 3 x) x = qd x
qd4 x =
  rewrite mult3Eq x in
  -- plus (plus x (db x)) x = qd x = plus (db x)(db x)
  trans (sym (plusAssociative x (db x) x))
    (trans (cong (plus x) (plusCommutative (db x) x))
      (plusAssociative x x (db x)))


public export
baseR : (b : Nat -> Bool) -> (k : Nat) -> (th : Nat) -> (nn : Nat) ->
  Leq nn th ->
  Leq (qd (mult (count (pullc b) nn) (S k)))
      (plus (mult 3 nn) (qd (mult th (S k))))
baseR b k th nn leNth =
  let cntLeTh : Leq (count (pullc b) nn) th
      cntLeTh = leqTrans (countLeN (pullc b) nn) leNth
  in leqTrans (qdMono (leqMultRight cntLeTh (S k)))
              (leqPlusExtraLeft (mult 3 nn) (qd (mult th (S k))))

public export
masterR :
  (b : Nat -> Bool) -> (k : Nat) ->
  (n0 : Nat) ->
  (hcb : (n : Nat) -> Leq n0 n -> Leq (mult (count b n) (qd (S k))) n) ->
  (th : Nat) ->
  (thGeN0 : Leq n0 th) ->
  (thGeDbqp : Leq (db (qd (S k))) th) ->
  (bnd : Nat) -> (bigN : Nat) -> Leq bigN bnd ->
  Leq (qd (mult (count (pullc b) bigN) (S k)))
      (plus (mult 3 bigN) (qd (mult th (S k))))
masterR b k n0 hcb th thGeN0 thGeDbqp Z bigN leNbnd =
  baseR b k th bigN (leqTrans leNbnd LeqZ)
masterR b k n0 hcb th thGeN0 thGeDbqp (S bnd') bigN leNbnd =
  case trichLeq bigN th of
    Left leNth => baseR b k th bigN leNth
    Right ltThN =>
      let qp : Nat
          qp = qd (S k)
          c0 : Nat
          c0 = qd (mult th (S k))
          thN : Leq th bigN
          thN = leqTrans (leqSuccRight th) ltThN
          n0N : Leq n0 bigN
          n0N = leqTrans thGeN0 thN
          dbqpN : Leq (db qp) bigN
          dbqpN = leqTrans thGeDbqp thN
          qpHalf : Leq qp (half bigN)
          qpHalf = dbLeToHalf qp bigN dbqpN
          hHalfBnd : Leq (half bigN) bnd'
          hHalfBnd = leqTrans (halfLeMono bigN (S bnd') leNbnd) (halfSuccLe bnd')
          ih : Leq (qd (mult (count (pullc b) (half bigN)) (S k)))
                   (plus (mult 3 (half bigN)) c0)
          ih = masterR b k n0 hcb th thGeN0 thGeDbqp bnd' (half bigN) hHalfBnd
          wStep : Leq (mult (count (pullc b) bigN) (S k))
                      (plus (mult (count (pullc b) (half bigN)) (S k))
                            (plus (S k) (mult (count b bigN) (S k))))
          wStep = leqCastR (leqMultRight (pullRecStep b bigN) (S k))
                    (multDistributesOverPlusLeft
                       (count (pullc b) (half bigN)) (S (count b bigN)) (S k))
          expandEq :
            (qd (plus (mult (count (pullc b) (half bigN)) (S k))
                      (plus (S k) (mult (count b bigN) (S k))))
             = plus (qd (mult (count (pullc b) (half bigN)) (S k)))
                    (plus qp (mult (count b bigN) qp)))
          expandEq =
            trans (qdPlus (mult (count (pullc b) (half bigN)) (S k))
                          (plus (S k) (mult (count b bigN) (S k))))
                  (cong (plus (qd (mult (count (pullc b) (half bigN)) (S k))))
                     (trans (qdPlus (S k) (mult (count b bigN) (S k)))
                            (cong (plus qp) (qdMultRight (count b bigN) (S k)))))
          chain1 : Leq (qd (mult (count (pullc b) bigN) (S k)))
                       (plus (qd (mult (count (pullc b) (half bigN)) (S k)))
                             (plus qp (mult (count b bigN) qp)))
          chain1 = leqCastR (qdMono wStep) expandEq
          hcbBound : Leq (mult (count b bigN) qp) bigN
          hcbBound = hcb bigN n0N
          chain2 : Leq (plus (qd (mult (count (pullc b) (half bigN)) (S k)))
                             (plus qp (mult (count b bigN) qp)))
                       (plus (plus (mult 3 (half bigN)) c0) (plus qp bigN))
          chain2 = leqAdd ih (leqAdd (leqRefl qp) hcbBound)
          hyp : Leq (plus (mult 3 (half bigN)) qp) (db bigN)
          hyp = leqCastL (cong (\z => plus z qp) (mult3Eq (half bigN)))
                         (finalIneq (half bigN) qp bigN (halfDoubleLe bigN) qpHalf)
          chain3 : Leq (plus (plus (mult 3 (half bigN)) c0) (plus qp bigN))
                       (plus (mult 3 bigN) c0)
          chain3 = combineFinal (mult 3 (half bigN)) c0 qp bigN hyp
      in leqTrans chain1 (leqTrans chain2 chain3)

public export
negligiblePull : (b : Nat -> Bool) -> Negligible b -> Negligible (pullc b)
negligiblePull b neg k =
  let (n0 ** hcb) = negFeed b neg k
      qp : Nat
      qp = qd (S k)
      th : Nat
      th = maxN n0 (db qp)
      c0 : Nat
      c0 = qd (mult th (S k))
      thGeN0 : Leq n0 th
      thGeN0 = leqMaxL n0 (db qp)
      thGeDbqp : Leq (db qp) th
      thGeDbqp = leqMaxR n0 (db qp)
  in (maxN th c0 ** \bigN, big =>
        let leC0 : Leq c0 bigN
            leC0 = leqTrans (leqMaxR th c0) big
            mr : Leq (qd (mult (count (pullc b) bigN) (S k)))
                     (plus (mult 3 bigN) c0)
            mr = masterR b k n0 hcb th thGeN0 thGeDbqp bigN bigN (leqRefl bigN)
            step : Leq (plus (mult 3 bigN) c0) (qd bigN)
            step = leqCastR (leqAdd (leqRefl (mult 3 bigN)) leC0) (qd4 bigN)
        in qdCancel (leqTrans mr step))
