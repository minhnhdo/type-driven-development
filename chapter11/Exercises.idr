module Exercises

import Data.Primitives.Views

data InfList : Type -> Type where
  (::) : (value : elem) -> Inf (InfList elem) -> InfList elem

%name InfList xs, ys, zs

Functor InfList where
  map func (value :: xs) = func value :: map func xs

countFrom : Integer -> InfList Integer
countFrom x = x :: countFrom (x + 1)

getPrefix : Nat -> InfList a -> List a
getPrefix Z _ = []
getPrefix (S k) (value :: xs) = value :: getPrefix k xs

quiz : Stream Int -> (score : Int) -> IO ()
quiz (num1 :: (num2 :: nums)) score =
  do putStrLn ("Score so far: " ++ show score)
     putStr (show num1 ++ " * " ++ show num2 ++ "? ")
     answer <- getLine
     if cast answer == num1 * num2
        then do putStrLn "Correct!"
                quiz nums (score + 1)
        else do putStrLn ("Wrong, the answer is " ++ show (num1 * num2))
                quiz nums score

randoms : Int -> Stream Int
randoms seed = let seed' = 1664525 * seed + 1013904223 in
                   (seed' `shiftR` 2) :: randoms seed'

arithInputs : Int -> Stream Int
arithInputs seed = map bound (randoms seed)
  where bound : Int -> Int
        bound num with (divides num 12)
          bound ((12 * _) + rem) | (DivBy _) = rem + 1

everyOther : Stream a -> Stream a
everyOther (_ :: (x :: xs)) = x :: everyOther xs

data Face = Heads | Tails

coinFlips : (count : Nat) -> Stream Int -> List Face
coinFlips Z _ = []
coinFlips (S k) (value :: xs) = let face = if value `div` 2 == 0
                                              then Heads
                                              else Tails in
                                    face :: coinFlips k xs

squareRootApprox : (number : Double) -> (approx : Double) -> Stream Double
squareRootApprox number approx = let next = (approx + (number / approx)) / 2 in
                                     next :: squareRootApprox number next

squareRootBound : (max : Nat) -> (number : Double) -> (bound : Double) ->
                  (approxs : Stream Double) -> Double
squareRootBound Z _ _ (value :: _) = value
squareRootBound (S k) number bound (value :: xs) =
  if abs (value * value - number) <= bound
     then value
     else squareRootBound k number bound xs

squareRoot : (number : Double) -> Double
squareRoot number =
  squareRootBound 100 number 0.00000000001 (squareRootApprox number number)
