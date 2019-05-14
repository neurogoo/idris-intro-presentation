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

data UsernameCheck = Authorized | NotAuthorized

data DataStore : (m : Type) -> (beforeState : Access) -> (afterStateFn : m -> Access) -> Type where
  LoginToStore : (username : String)
               -> DataStore UsernameCheck LoggedOut (\check => case check of
                                                                    Authorized => LoggedIn
                                                                    NotAuthorized => LoggedOut)
  LogoutFromStore : DataStore () LoggedIn (const LoggedOut)

  AddToList : String -> List String -> DataStore (List String) LoggedIn (const LoggedIn)
  Display : (Show a) => a -> DataStore () LoggedIn (const LoggedIn)
  Message : String -> DataStore () state (const state)

  Pure : (res : m) -> DataStore m (stateFn res) stateFn
  (>>=) : DataStore a state1 state2Fn -> ((res : a) -> DataStore b (state2Fn res) state3Fn) -> DataStore b state1 state3Fn

addAndDisplay : DataStore () LoggedOut (const LoggedOut)
addAndDisplay = do
  res <- LoginToStore "root"
  case res of
    NotAuthorized => Message "Not authorized user"
    Authorized => do
      store <- AddToList "Super secret secret" []
      Display store
      store <- AddToList "Second super secret secret" store
      Display store
      LogoutFromStore

runDataStore : DataStore res state1 state2fn -> IO res
runDataStore (LoginToStore username) =
  case username of
    "root" => pure Authorized
    _      => pure NotAuthorized
runDataStore LogoutFromStore = pure ()
runDataStore (AddToList x xs) = pure (x :: xs)
runDataStore (Display as) = do putStr $ show as
                               pure ()
runDataStore (Message s) = do putStr s
                              pure ()
runDataStore (Pure x) = pure x
runDataStore (x >>= f) = do r <- runDataStore x
                            runDataStore (f r)
