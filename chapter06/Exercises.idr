module Exercises

import Data.Vect

Matrix : Nat -> Nat -> Type
Matrix n m = Vect n (Vect m Int)

data Format = Number Format
            | FNumber Format
            | Str Format
            | C Format
            | Lit String Format
            | End

PrintfType : Format -> Type
PrintfType (Number fmt) = (i : Int) -> PrintfType fmt
PrintfType (FNumber fmt) = (d : Double) -> PrintfType fmt
PrintfType (Str fmt) = (str : String) -> PrintfType fmt
PrintfType (C fmt) = (c : Char) -> PrintfType fmt
PrintfType (Lit str fmt) = PrintfType fmt
PrintfType End = String

printfFmt : (fmt : Format) -> (acc : String) -> PrintfType fmt
printfFmt (Number fmt) acc = \i:Int => printfFmt fmt (acc ++ show i)
printfFmt (FNumber fmt) acc = \d => printfFmt fmt (acc ++ show d)
printfFmt (Str fmt) acc = \s => printfFmt fmt (acc ++ s)
printfFmt (C fmt) acc = \c => printfFmt fmt (acc ++ cast c)
printfFmt (Lit lit fmt) acc = printfFmt fmt (acc ++ lit)
printfFmt End acc = acc

toFormat : (xs : List Char) -> Format
toFormat [] = End
toFormat ('%' :: 'd' :: xs) = Number $ toFormat xs
toFormat ('%' :: 'f' :: xs) = FNumber $ toFormat xs
toFormat ('%' :: 's' :: xs) = Str $ toFormat xs
toFormat ('%' :: 'c' :: xs) = C $ toFormat xs
toFormat ('%' :: xs) = Lit "%" $ toFormat xs
toFormat (x :: xs) = case toFormat xs of
                          Lit lit fmt => Lit (strCons x lit) fmt
                          fmt => Lit (strCons x "") fmt

printf : (fmt : String) -> PrintfType (toFormat (unpack fmt))
printf fmt = printfFmt _ ""

TupleVect : Nat -> Type -> Type
TupleVect Z ty = ()
TupleVect (S k) ty = (ty, TupleVect k ty)

test : TupleVect 4 Nat
test = (1,2,3,4,())
