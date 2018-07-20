module Exercises

import Data.Vect

transposeMat : Vect m (Vect n a) -> Vect n (Vect m a)
transposeMat [] = replicate _ []
transposeMat (x :: xs) = zipWith (::) x (transposeMat xs)

addMatrix : Num a => Vect m (Vect n a) -> Vect m (Vect n a) -> Vect m (Vect n a)
addMatrix xs ys = zipWith (\x,y => zipWith (+) x y) xs ys

multMatrix : Num a => Vect m (Vect n a) -> Vect n (Vect p a) -> Vect m (Vect p a)
multMatrix xs ys = let ts = transposeMat ys
                   in map (\x => map (\t => foldr (+) 0 (zipWith (*) x t)) ts) xs
