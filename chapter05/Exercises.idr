module Main

import Data.Vect
import System

printLonger : IO ()
printLonger = do putStr "First string: "
                 first_string <- getLine
                 putStr "Second string: "
                 second_string <- getLine
                 let longer_string = if length first_string > length second_string
                                        then first_string
                                        else second_string
                 putStrLn ("The longer string is: " ++ longer_string ++ "\n")

printLonger' : IO ()
printLonger' = putStr "First string: "
             >>= \_ => getLine
             >>= \first_string => putStr "First string: "
             >>= \_ => getLine
             >>= \second_string => let longer_string = if length first_string > length second_string
                                                          then first_string
                                                          else second_string
                                   in putStrLn ("The longer string is: " ++ longer_string ++ "\n")

myReplWith : a -> String -> (a -> String -> Maybe (String, a)) -> IO ()
myReplWith init str f =
   do putStr str
      input <- getLine
      case f init input of
           Nothing => pure ()
           Just (output, next) => do putStr output
                                     myReplWith next str f

myRepl : String -> (String -> String) -> IO ()
myRepl str f = do putStr str
                  input <- getLine
                  putStr $ f input
                  myRepl str f

parseNat : String -> Maybe Nat
parseNat str = if all isDigit (unpack str)
                  then Just (cast str)
                  else Nothing

guess : (target : Nat) -> (guesses : Nat) -> IO ()
guess target guesses =
  do putStr "Guess: "
     input <- getLine
     case parseNat input of
          Nothing => do putStrLn "Invalid number!"
                        guess target guesses
          Just g => let current_guesses = guesses + 1
                    in case compare g target of
                            LT => do putStrLn "Too low!"
                                     guess target current_guesses
                            EQ => putStrLn ("Correct! You made " ++ show current_guesses ++ " guesses!")
                            GT => do putStrLn "Too high!"
                                     guess target current_guesses

readToBlank : IO (List String)
readToBlank = do input <- getLine
                 if length input == 0
                    then pure []
                    else do rest <- readToBlank
                            pure (input :: rest)

readAndSave : IO ()
readAndSave = do input <- readToBlank
                 putStr "Enter a filename: "
                 filename <- getLine
                 Right file <- openFile filename WriteTruncate
                   | Left err => putStrLn ("Cannot open file " ++ filename ++ " for writing!")
                 writeAllLines file input
  where writeAllLines : File -> List String -> IO ()
        writeAllLines file [] = closeFile file
        writeAllLines file (x :: xs) = do fPutStrLn file x
                                          writeAllLines file xs

readVectFile : (filename : String) -> IO (n ** Vect n String)
readVectFile filename = do Right file <- openFile filename Read
                             | Left err => do putStrLn ("Cannot open file " ++ filename ++ " for reading!")
                                              pure (_ ** [])
                           r <- readAllLines file
                           closeFile file
                           pure r
  where readAllLines : File -> IO (n ** Vect n String)
        readAllLines file = do Right line <- fGetLine file
                                   | Left err => do putStrLn "Error reading from file!"
                                                    pure (_ ** [])
                               if length line == 0
                                  then pure (_ ** [])
                                  else do (_ ** rest) <- readAllLines file
                                          pure (_ ** line :: rest)

main : IO ()
main = do putStr "Filename: "
          filename <- getLine
          (_ ** v) <- readVectFile filename
          putStrLn $ show v

-- main : IO ()
-- main = do current <- time
--           let target = current `mod` 100 + 1
--           guess (cast target) 0
