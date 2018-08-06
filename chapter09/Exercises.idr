module Exercises

import Data.Vect
import Data.List

oneInVector : Vect.Elem 1 [1, 2, 3]
oneInVector = Here

maryInVector : Vect.Elem "Mary" ["Peter", "Paul", "Mary"]
maryInVector = There (There Here)

removeElem : (value : a) -> (xs : Vect (S n) a) -> (prf : Elem value xs) -> Vect n a
removeElem value (value :: xs) Here = xs
removeElem {n = Z} value (x :: []) (There later) = absurd later
removeElem {n = (S k)} value (x :: xs) (There later) = x :: removeElem value xs later

removeElem_auto : (value : a) -> (xs : Vect (S n) a) -> {auto prf : Elem value xs} -> Vect n a
removeElem_auto value xs {prf} = removeElem value xs prf

data Last : List a -> a -> Type where
  LastOne : Last [value] value
  LastCons : (prf : Last xs value) -> Last (x :: xs) value

Uninhabited (Last [] value) where
  uninhabited LastOne impossible
  uninhabited (LastCons _) impossible

lastNotEq : (contra : x = value -> Void) -> Last [x] value -> Void
lastNotEq contra LastOne = contra Refl
lastNotEq _ (LastCons LastOne) impossible
lastNotEq _ (LastCons (LastCons _)) impossible

tailNotEq : (contra : Last xs value -> Void) -> Last (x :: xs) value -> Void
tailNotEq contra (LastCons prf) = contra prf

isLast : DecEq a => (xs : List a) -> (value : a) -> Dec (Last xs value)
isLast [] value = No absurd
isLast (x :: []) value = case decEq x value of
                              Yes Refl => Yes LastOne
                              No contra => No (lastNotEq contra)
isLast (x :: xs) value = case isLast xs value of
                              Yes prf => Yes (LastCons prf)
                              No contra => No (tailNotEq contra)
