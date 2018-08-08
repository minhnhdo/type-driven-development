module Main

import Data.Primitives.Views
import System

%default total

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

partial
quizPartial : Stream Int -> (score : Int) -> IO ()
quizPartial (num1 :: (num2 :: nums)) score =
  do putStrLn ("Score so far: " ++ show score)
     putStr (show num1 ++ " * " ++ show num2 ++ "? ")
     answer <- getLine
     if cast answer == num1 * num2
        then do putStrLn "Correct!"
                quizPartial nums (score + 1)
        else do putStrLn ("Wrong, the answer is " ++ show (num1 * num2))
                quizPartial nums score

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

partial
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

data InfIO : Type where
  Do : IO a -> (a -> Inf InfIO) -> InfIO

(>>=) : IO a -> (a -> Inf InfIO) -> InfIO
(>>=) = Do

data Fuel = Dry | More (Lazy Fuel)

tank : Nat -> Fuel
tank Z = Dry
tank (S k) = More (tank k)

loopPrint : String -> InfIO
loopPrint msg = do putStrLn msg
                   loopPrint msg

partial
forever : Fuel
forever = More forever

-- run : InfIO -> IO ()
-- run (Do action cont) = do res <- action
--                           run (cont res)

run : Fuel -> InfIO -> IO ()
run Dry _ = putStrLn "Out of fuel"
run (More fuel) (Do action cont) = do res <- action
                                      run fuel (cont res)

greetInf : InfIO
greetInf = do putStr "Enter your name: "
              name <- getLine
              putStrLn ("Hello " ++ name)
              greetInf

namespace RunIO
  data RunIO : Type -> Type where
    Quit : a -> RunIO a
    Do : IO a -> (a -> Inf (RunIO b)) -> RunIO b

  (>>=) : IO a -> (a -> Inf (RunIO b)) -> RunIO b
  (>>=) = Do

  run : Fuel -> RunIO a -> IO (Maybe a)
  run fuel (Quit value) = pure (Just value)
  run Dry _ = pure Nothing
  run (More fuel) (Do cmd f) = do res <- cmd
                                  run fuel (f res)

greet : RunIO ()
greet = do putStr "Enter your name: "
           name <- getLine
           if name == ""
              then do putStrLn "Bye bye!"
                      Quit ()
              else do putStrLn ("Hello " ++ name)
                      greet

totalRepl : (prompt : String) -> (action : String -> String) -> InfIO
totalRepl prompt action = do putStr prompt
                             input <- getLine
                             putStr (action input)
                             totalRepl prompt action

quiz : Stream Int -> (score : Nat) -> InfIO
quiz (num1 :: (num2 :: nums)) score =
  do putStrLn ("Score so far: " ++ show score)
     putStr (show num1 ++ " * " ++ show num2 ++ "? ")
     answer <- getLine
     if cast answer == num1 * num2
        then do putStrLn "Correct!"
                quiz nums (score + 1)
        else do putStrLn ("Wrong, the answer is " ++ show (num1 * num2))
                quiz nums score

partial
main : IO ()
main = do seed <- time
          run forever (quiz (arithInputs (fromInteger seed)) 0)
