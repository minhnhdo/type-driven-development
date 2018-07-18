module Main

average : (str : String) -> Double
average str = let numWords = wordCount str
                  totalLength = sum (allLengths (words str))
              in cast totalLength / cast numWords
  where wordCount : String -> Nat
        wordCount s = length (words s)

        allLengths : List String -> List Nat
        allLengths ss = map length ss

showAverage : String -> String
showAverage str = "The average word length is: " ++ show (average str) ++ "\n"

main : IO ()
main = repl "Enter a string: " showAverage
