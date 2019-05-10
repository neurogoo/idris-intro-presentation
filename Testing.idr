module Testing

import Data.Vect

data ListLast : List a -> Type where
  Empty : ListLast []
  NonEmpty : (xs : List a) -> (x : a) -> ListLast (xs ++ [x])

data MyList : (a : Type) -> Type where
  Nil : MyList a
  (::) : (x : a) -> (xs : MyList a) -> MyList a

data PriceCategory = Regular | BestBefore | Membership

data ProductPrice : (price : Double) -> PriceCategory -> Type where
  RegularPrice : ProductPrice price Regular
  BestBeforePrice : ProductPrice price BestBefore
  MembershipPrice : (discountPercent : Double) -> ProductPrice price Membership

calculateFinalPrice : (productPrice : ProductPrice price category) -> Double
calculateFinalPrice {price} RegularPrice = price
calculateFinalPrice {price} BestBeforePrice = 0.7 * price
calculateFinalPrice {price} (MembershipPrice discount) = discount * price

limitedOffer : (productPrice : ProductPrice price category) -> {auto p : price < 20.0 = True} -> Double
limitedOffer {price} _ = 0.5 * price

sayLength : Vect n a -> String
sayLength {n} _ = "You gave Vector of length " ++ (cast n)

record Car where
  constructor MkCar
  model : String
  year : Int

car : Car
car = MkCar "Ferrari" 1988
