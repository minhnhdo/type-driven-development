module Main

v1 : (String, String, String)
v1 = ("A", "B", "C")

v2 : List String
v2 = ["A", "B", "C"]

v3 : ((String, String), String)
v3 =  (("A", "B"), "C")

palindrome : String -> Bool
palindrome s = s == reverse s

palindromeCaseInsensitive : String -> Bool
palindromeCaseInsensitive s =
  let ls = toLower s
  in ls == reverse ls

palindromeAtLeast10Char : String -> Bool
palindromeAtLeast10Char s = length s > 10 && palindrome s

palindromeLongerThan : Nat -> String -> Bool
palindromeLongerThan len s = length s >= len && palindrome s

counts : String -> (Nat, Nat)
counts s = (length (words s), length s)

top_ten : Ord a => List a -> List a
top_ten = take 10 . List.reverse . sort

over_length : Nat -> List String -> Nat
over_length len = length . filter ((> len) . length)

exec_palindrome : IO ()
exec_palindrome = repl "Enter a string: " ((++ "\n") . show . palindromeCaseInsensitive)

exec_counts : IO ()
exec_counts = repl "Enter a string: " ((++ "\n") . show . counts)

main : IO ()
main = exec_counts
