module Exercises

import Data.Fin
import Data.Vect

data Tree elem = Empty | Node (Tree elem) elem (Tree elem)

insert : Ord a => a -> Tree a -> Tree a
insert x Empty = Node Empty x Empty
insert x orig@(Node l val r) = case compare x val of
                                    LT => Node (insert x l) val r
                                    EQ => orig
                                    GT => Node l val (insert x r)

listToTree : Ord a => List a -> Tree a
listToTree xs = foldr insert Empty xs

treeToList : Ord a => Tree a -> List a
treeToList Empty = []
treeToList (Node l val r) = treeToList l ++ [val] ++ treeToList r

data Expr = I Int | Add Expr Expr | Sub Expr Expr | Mul Expr Expr

evaluate : Expr -> Int
evaluate (I x) = x
evaluate (Add x y) = evaluate x + evaluate y
evaluate (Sub x y) = evaluate x - evaluate y
evaluate (Mul x y) = evaluate x * evaluate y

maxMaybe : Ord a => Maybe a -> Maybe a -> Maybe a
maxMaybe x y = case (x, y) of
                    (Nothing, b) => b
                    (a, Nothing) => a
                    (Just a, Just b) => Just $ case compare a b of
                                                    LT => b
                                                    EQ => b
                                                    GT => a

data PowerSource = Petrol | Electricity | Pedal

data Vehicle : PowerSource -> Type where
  Unicycle : Vehicle Pedal
  Bicycle : Vehicle Pedal
  Motocycle : (fuel : Nat) -> Vehicle Petrol
  Car : (fuel : Nat) -> Vehicle Petrol
  ElectricCar : (battery_level : Nat) -> Vehicle Electricity
  Bus : (fuel : Nat) -> Vehicle Petrol
  Tram : (battery_level : Nat) -> Vehicle Electricity

wheels : Vehicle power -> Nat
wheels Unicycle = 1
wheels Bicycle = 2
wheels (Motocycle _) = 2
wheels (Car _) = 4
wheels (Bus _) = 4

refuel : Vehicle Petrol -> Vehicle Petrol
refuel (Motocycle _) = Motocycle 50
refuel (Car _) = Car 100
refuel (Bus _) = Bus 200
refuel Unicycle impossible
refuel Bicycle impossible
refuel (ElectricCar _) impossible
refuel (Tram _) impossible

recharge : Vehicle Electricity -> Vehicle Electricity
recharge (ElectricCar _) = ElectricCar 100
recharge (Tram _) = Tram 1000
recharge Unicycle impossible
recharge Bicycle impossible
recharge (Car _) impossible
recharge (Bus _) impossible

vectTake : (m : Fin n) -> Vect n a -> Vect (finToNat m) a
vectTake FZ _ = []
vectTake (FS m) (x :: xs) = x :: vectTake m xs

sumEntries : Num a => (pos : Integer) -> Vect n a -> Vect n a -> Maybe a
sumEntries {n} pos xs ys = case integerToFin pos n of
                                Nothing => Nothing
                                Just idx => Just (index idx xs + index idx ys)
