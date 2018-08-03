module Main

data Shape = Triangle Double Double
           | Rectangle Double Double
           | Circle Double

area : Shape -> Double
area (Triangle base height) = 0.5 * base * height
area (Rectangle length height) = length * height
area (Circle radius) = pi * radius * radius

Eq Shape where
  (Triangle x y) == (Triangle z w) = x == z && y == w
  (Rectangle x y) == (Rectangle z w) = x == z && y == w
  (Circle x) == (Circle y) = x == y
  _ == _ = False

Ord Shape where
  compare s1 s2 = compare (area s1) (area s2)

data Expr num = Val num
              | Add (Expr num) (Expr num)
              | Sub (Expr num) (Expr num)
              | Mul (Expr num) (Expr num)
              | Div (Expr num) (Expr num)
              | Abs (Expr num)

eval : (Abs num, Integral num, Neg num) => Expr num -> num
eval (Val x) = x
eval (Add x y) = eval x + eval y
eval (Sub x y) = eval x - eval y
eval (Mul x y) = eval x * eval y
eval (Div x y) = eval x `div` eval y
eval (Abs x) = abs (eval x)

Num ty => Num (Expr ty) where
  (+) = Add
  (*) = Mul
  fromInteger = Val . fromInteger

Neg ty => Neg (Expr ty) where
  negate x = 0 - x
  (-) = Sub

Abs ty => Abs (Expr ty) where
  abs = Abs

Show ty => Show (Expr ty) where
  show (Val x) = show x
  show (Add x y) = "(" ++ show x ++ " + " ++ show y ++ ")"
  show (Sub x y) = "(" ++ show x ++ " - " ++ show y ++ ")"
  show (Mul x y) = "(" ++ show x ++ " * " ++ show y ++ ")"
  show (Div x y) = "(" ++ show x ++ " / " ++ show y ++ ")"
  show (Abs x) = "|" ++ show x ++ "|"

(Abs ty, Integral ty, Neg ty, Eq ty) => Eq (Expr ty) where
  x == y = eval x == eval y

(Abs num, Integral num, Neg num, Num num) => Cast (Expr num) num where
  cast = eval

Functor Expr where
  map f (Val x) = Val (f x)
  map f (Add x y) = Add (map f x) (map f y)
  map f (Sub x y) = Add (map f x) (map f y)
  map f (Mul x y) = Add (map f x) (map f y)
  map f (Div x y) = Add (map f x) (map f y)
  map f (Abs x) = Abs (map f x)
