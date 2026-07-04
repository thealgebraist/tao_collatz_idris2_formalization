module TaoCollatz.Dual

%default total

public export
data OrderFilter : Type -> Type where
  InOrderFilter : claim -> OrderFilter claim

public export
data QuantitativeProbability : Type -> Type where
  InQuantitativeProbability : claim -> QuantitativeProbability claim

public export
record DualProof (claim : Type) where
  constructor ProvedTwice
  orderFilterPath : OrderFilter claim
  quantitativeProbabilityPath : QuantitativeProbability claim

public export
orderClaim : DualProof claim -> claim
orderClaim (ProvedTwice (InOrderFilter claim) _) = claim

public export
quantitativeClaim : DualProof claim -> claim
quantitativeClaim (ProvedTwice _ (InQuantitativeProbability claim)) = claim

public export
dualPure : claim -> DualProof claim
dualPure claim =
  ProvedTwice
    (InOrderFilter claim)
    (InQuantitativeProbability claim)

public export
dualMap : (a -> b) -> DualProof a -> DualProof b
dualMap f prf =
  ProvedTwice
    (InOrderFilter (f (orderClaim prf)))
    (InQuantitativeProbability (f (quantitativeClaim prf)))

public export
dualId : DualProof (a -> a)
dualId =
  ProvedTwice
    (InOrderFilter (\x => x))
    (InQuantitativeProbability (\x => x))

public export
dualApply : DualProof (a -> b) -> DualProof a -> DualProof b
dualApply f x =
  ProvedTwice
    (InOrderFilter (orderClaim f (orderClaim x)))
    (InQuantitativeProbability (quantitativeClaim f (quantitativeClaim x)))

public export
dualCompose : DualProof (b -> c) -> DualProof (a -> b) -> DualProof (a -> c)
dualCompose f g =
  ProvedTwice
    (InOrderFilter (\x => orderClaim f (orderClaim g x)))
    (InQuantitativeProbability
      (\x => quantitativeClaim f (quantitativeClaim g x)))

public export
dualApply2 : DualProof (a -> b -> c) -> DualProof a -> DualProof b -> DualProof c
dualApply2 f x y =
  ProvedTwice
    (InOrderFilter (orderClaim f (orderClaim x) (orderClaim y)))
    (InQuantitativeProbability
      (quantitativeClaim f (quantitativeClaim x) (quantitativeClaim y)))
