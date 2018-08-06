module Main

import Data.Vect

data WordState : (guesses_remaining : Nat) -> (letters : Nat) -> Type where
  MkWordState : (word : String) -> (missing : Vect letters Char) -> WordState guesses_remaining letters

data Finished : Type where
  Lost : (game : WordState 0 (S letters)) -> Finished
  Won  : (game : WordState (S guesses) 0) -> Finished

data ValidInput : List Char -> Type where
  Letter : (c : Char) -> ValidInput [c]

Uninhabited (ValidInput []) where
  uninhabited (Letter _) impossible

Uninhabited (ValidInput (x :: y :: xs)) where
  uninhabited (Letter _) impossible

isValidInput : (cs : List Char) -> Dec (ValidInput cs)
isValidInput [] = No absurd
isValidInput (x :: []) = Yes (Letter x)
isValidInput (x :: (y :: xs)) = No absurd

isValidString : (s : String) -> Dec (ValidInput (unpack s))
isValidString s = isValidInput (unpack s)

readGuess : IO (x ** ValidInput x)
readGuess = do putStr "Guess: "
               line <- getLine
               case isValidString (toUpper line) of
                    Yes prf => pure (_ ** prf)
                    No contra => do putStrLn "Invalid guess"
                                    readGuess

removeElem : (value : a) -> (xs : Vect (S n) a) -> {auto prf : Elem value xs} -> Vect n a
removeElem value (value :: xs) {prf = Here} = xs
removeElem {n = Z} value (x :: []) {prf = There later} = absurd later
removeElem {n = (S k)} value (x :: xs) {prf = There later} = x :: removeElem value xs

processGuess : (letter : Char) -> WordState (S guesses) (S letters) ->
               Either (WordState guesses (S letters))
                      (WordState (S guesses) letters)
processGuess letter (MkWordState word missing) =
  case letter `isElem` missing of
       Yes prf => Right (MkWordState word (removeElem letter missing))
       No contra => Left (MkWordState word missing)

game : WordState (S guesses) (S letters) -> IO Finished
game {guesses} {letters} st =
  do (_ ** Letter letter) <- readGuess
     case processGuess letter st of
          Left l => do putStrLn "Wrong!"
                       case guesses of
                            Z => pure (Lost l)
                            S _ => game l
          Right r => do putStrLn "Right!"
                        case letters of
                             Z => pure (Won r)
                             S _ => game r

main : IO ()
main = do result <- game {guesses = 2} (MkWordState "Test" ['T', 'E', 'S'])
          case result of
               Lost (MkWordState word _) => putStrLn ("You lose. The word was " ++ word)
               Won _ => putStrLn "You win!"
