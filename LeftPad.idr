module LeftPad

import Data.Vect
import Data.Vect.Quantifiers

helperProof : (m : Fin n) -> Vect n a -> Vect (cast m) a
helperProof FZ v = []
helperProof (FS x) (y :: xs) = y :: helperProof x xs

addToVec : (c : Char) -> Vect n Char -> (m : Nat) -> Vect (m + n) Char
addToVec {n} c v k =  replicate k c ++ v

minusItselfZero : (a : Nat) -> (b : Nat) -> LTE b a -> Vect (a - b + b) Char = Vect a Char
minusItselfZero a b p = ?minusItselfZero_rhs1

leftPad : (c : Char)
        -> (s : List Char)
        -> (n : Nat)
        -> (case isLTE (length s) (S n) of
                 No _ => (x : List Char ** (x = s))
                 Yes _ => (v : Vect (S n) Char
                              **
                              (y : Vect ((S n) - (length s)) Char ** (y ++ (fromList s) = v))))
leftPad padChar s n with (isLTE (length s) (S n))
  leftPad padChar s n | No _ = (s ** Refl)
  leftPad padChar s n | Yes lteproof = let paddingVec = replicate ((S n) - (length s)) padChar
                                           newVec = paddingVec ++ (fromList s)
                                       in ((rewrite sym (minusItselfZero (S n) (length s) lteproof) in newVec) ** (paddingVec ** Refl))
                                       --     newVec = addToVec padChar (fromList s) ((S n) - (length s))
                                       -- in ((rewrite sym (minusItselfZero (S n) (length s) lteproof) in newVec) ** ( paddingVec ** Refl))
