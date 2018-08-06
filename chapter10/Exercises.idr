module Exercises

import Data.Vect
import Data.List.Views
import Data.Nat.Views
import Data.Vect.Views

data ListLast : List a -> Type where
  Empty : ListLast []
  NonEmpty : (xs : List a) -> (x : a) -> ListLast (xs ++ [x])

total listLast : (xs : List a) -> ListLast xs
listLast [] = Empty
listLast (x :: xs) = case listLast xs of
                          Empty => NonEmpty [] x
                          NonEmpty ys y => NonEmpty (x :: ys) y

total describeListEnd : List Int -> String
describeListEnd xs with (listLast xs)
  describeListEnd [] | Empty = "Empty"
  describeListEnd (ys ++ [x]) | (NonEmpty ys x) = "Non-empty, initial portion = " ++ show ys

-- total myReverse : List a -> List a
-- myReverse xs with (listLast xs)
--   myReverse [] | Empty = []
--   myReverse (ys ++ [x]) | (NonEmpty ys x) = x :: myReverse ys

data SplitList : List a -> Type where
  SplitNil : SplitList []
  SplitOne : SplitList [x]
  SplitPair : (lefts : List a) -> (rights : List a) -> SplitList (lefts ++ rights)

total splitList : (input : List a) -> SplitList input
splitList input = splitListHelper input input
  where splitListHelper : List a -> (input : List a) -> SplitList input
        splitListHelper _ [] = SplitNil
        splitListHelper _ [x] = SplitOne
        splitListHelper (_ :: _ :: counter) (item :: items) =
          case splitListHelper counter items of
               SplitNil => SplitOne
               SplitOne {x} => SplitPair [item] [x]
               SplitPair lefts rights => SplitPair (item :: lefts) rights
        splitListHelper _ items = SplitPair [] items

-- mergeSort : Ord a => List a -> List a
-- mergeSort input with (splitList input)
--   mergeSort [] | SplitNil = []
--   mergeSort [x] | SplitOne = [x]
--   mergeSort (lefts ++ rights) | (SplitPair lefts rights) = merge (mergeSort lefts) (mergeSort rights)

data TakeN : List a -> Type where
  Fewer : TakeN xs
  Exact : (n_xs : List a) -> TakeN (n_xs ++ rest)

takeN : (n : Nat) -> (input : List a) -> TakeN input
takeN Z input = Exact []
takeN (S k) [] = Fewer
takeN (S k) (x :: xs) = case takeN k xs of
                             Fewer => Fewer
                             Exact n_xs => Exact (x :: n_xs)

groupByN : (n : Nat) -> (xs : List a) -> List (List a)
groupByN n xs with (takeN n xs)
  groupByN n xs | Fewer = [xs]
  groupByN n (n_xs ++ rest) | (Exact n_xs) = n_xs :: groupByN n rest

halves : List a -> (List a, List a)
halves xs with (takeN (length xs `div` 2) xs)
  halves xs | Fewer = (xs, xs) -- impossible?
  halves (n_xs ++ rest) | (Exact n_xs) = (n_xs, rest)

-- total mergeSort : Ord a => List a -> List a
-- mergeSort xs with (splitRec xs)
--   mergeSort [] | SplitRecNil = []
--   mergeSort [x] | SplitRecOne = [x]
--   mergeSort (lefts ++ rights) | (SplitRecPair lrec rrec) =
--     merge (mergeSort lefts | lrec) (mergeSort rights | rrec)

equalSuffix : Eq a => List a -> List a -> List a
equalSuffix xs ys with (snocList xs)
  equalSuffix [] ys | Empty with (snocList ys)
    equalSuffix [] [] | Empty | Empty = []
    equalSuffix [] (xs ++ [x]) | Empty | (Snoc rec) = []
  equalSuffix (zs ++ [x]) ys | (Snoc rec) with (snocList ys)
    equalSuffix (zs ++ [x]) [] | (Snoc rec) | Empty = []
    equalSuffix (zs ++ [x]) (xs ++ [y]) | (Snoc rec) | (Snoc z) =
      if x == y
         then equalSuffix zs xs ++ [x]
         else []

total mergeSort : Ord elem => Vect n elem -> Vect n elem
mergeSort xs with (splitRec xs)
  mergeSort [] | SplitRecNil = []
  mergeSort [x] | SplitRecOne = [x]
  mergeSort (ys ++ zs) | (SplitRecPair lrec rrec) =
    merge (mergeSort ys | lrec) (mergeSort zs | rrec)

total toBinary : Nat -> String
toBinary k with (halfRec k)
  toBinary Z | HalfRecZ = ""
  toBinary (n + n) | (HalfRecEven rec) = (toBinary n | rec) ++ "0"
  toBinary (S (n + n)) | (HalfRecOdd rec) = (toBinary n | rec) ++ "1"

palindrome : Eq a => List a -> Bool
palindrome xs with (vList xs)
  palindrome [] | VNil = True
  palindrome [x] | VOne = True
  palindrome (x :: (ys ++ [y])) | (VCons rec) = if x == y
                                                   then palindrome ys | rec
                                                   else False
