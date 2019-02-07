module LeftPad

import Data.Vect
import Data.Vect.Quantifiers

simpleLeftPad : Char -> Int -> String -> Int
simpleLeftPad = 2

testing : String -> Type
testing "Give me text" = String
testing _              = Int

-- `minus` is saturating subtraction, so this works like we want it to
eq_max : (n, k : Nat) -> maximum k n = plus (n `minus` k) k
eq_max  n     Z    = rewrite minusZeroRight n in
                     rewrite plusZeroRightNeutral n in Refl
eq_max  Z    (S _) = Refl
eq_max (S n) (S k) = rewrite sym $ plusSuccRightSucc (n `minus` k) k in rewrite eq_max n k in Refl

-- The type here says "the result is" padded to (maximum k n), and is padding plus the original
leftPad : (x : a) -> (n : Nat) -> (xs : Vect k a)
       -> (ys : Vect (maximum k n) a ** m : Nat ** ys = replicate m x ++ xs)
leftPad {k} x n xs = rewrite eq_max n k in (replicate (n `minus` k) x ++ xs ** n `minus` k ** Refl)

-- helperProof : (m : Fin n) -> Vect n a -> Vect (cast m) a
-- helperProof FZ v = []
-- helperProof (FS x) (y :: xs) = y :: helperProof x xs

-- minusItselfZero : (a : Nat) -> (b : Nat) -> LTE b a -> Vect (a - b + b) Char = Vect a Char
-- minusItselfZero a b p = ?minusItselfZero_rhs1

-- leftPad : (c : Char)
--         -> (s : List Char)
--         -> (n : Nat)
--         -> (case isLTE (length s) (S n) of
--                  No _ => (x : List Char ** (x = s))
--                  Yes _ => (v : Vect (S n) Char
--                               **
--                               (y : Vect ((S n) - (length s)) Char ** (y ++ (fromList s) = v))))
-- leftPad padChar s n with (isLTE (length s) (S n))
--   leftPad padChar s n | No _ = (s ** Refl)
--   leftPad padChar s n | Yes lteproof = let paddingVec = replicate ((S n) - (length s)) padChar
--                                            newVec = paddingVec ++ (fromList s)
--                                        in rewrite sym (minusItselfZero (S n) (length s) lteproof) in (newVec ** (paddingVec ** ?jotain))
