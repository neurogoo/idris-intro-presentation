module Testing

import Data.Vect
import Data.IORef

record Login where
  constructor MkLogin
  loginName : String
  password : (p : String ** length p `GTE` 12)

passwordStrengthChecker : (password : String) -> Dec (length password `GTE` 12)
passwordStrengthChecker password = isLTE 12 (length password)

createNewUser : (loginName : String) -> (password : String) -> Either String Login
createNewUser loginName password = case passwordStrengthChecker password of
  Yes prf => Right $ MkLogin loginName (password ** prf)
  No prf  => Left "Password was not long enough"

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

data Access = LoggedOut | LoggedIn

checkDataStoreLogin : (username : String) -> Access
checkDataStoreLogin "root" = LoggedIn
checkDataStoreLogin _      = LoggedOut

data DataStore : (m : Type) -> (beforeState : Access) -> (afterState : Access) -> Type where
  LoginToStore : (username : String) -> DataStore () LoggedOut LoggedIn
  LogoutFromStore : DataStore () LoggedIn LoggedOut
  GetData : DataStore () LoggedIn a -> DataStore () LoggedIn LoggedIn

  AddToList : String -> DataStore (List String) state state
  Display : DataStore (List String) state state

  Pure : m -> DataStore m state state
  (>>=) : DataStore a state1 state2 -> (a -> DataStore b state2 state3) -> DataStore b state1 state3

addAndDisplay : DataStore () LoggedOut LoggedOut
addAndDisplay = do
  LoginToStore "jee"
  AddToList "Super secret secret"
  Display
  LogoutFromStore

runDataStore : IORef a -> DataStore res state1 state2 -> IO res
runDataStore a (LoginToStore username) = pure ()
runDataStore a LogoutFromStore = pure ()
runDataStore a (GetData x) = pure ()
runDataStore a (AddToList x) = ?aukko4
runDataStore a Display = ?runDataStore_rhs_8
runDataStore a (Pure x) = pure x
runDataStore a (x >>= f) = do r <- runDataStore a x
                              runDataStore a (f r)
