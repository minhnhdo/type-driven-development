module Main

import Data.Vect

%default total

letters : String -> List Char
letters str = nub (map toUpper (unpack str))

data GuessResult = Correct | Incorrect

data GameState : Type where
  NotRunning : GameState
  Running : (guesses : Nat) -> (letters : Nat) -> GameState

data Game : GameState -> Type where
  GameStart  : Game NotRunning
  GameWon    : (word : String) -> Game NotRunning
  GameLost   : (word : String) -> Game NotRunning
  InProgress : (word : String) -> (guesses : Nat) ->
               (missing : Vect letters Char) ->
               Game (Running guesses letters)

Show (Game g) where
  show GameStart = "Starting"
  show (GameWon word) = "Game won: word was " ++ word
  show (GameLost word) = "Game lost: word was " ++ word
  show (InProgress word guesses missing) =
    "\n" ++ pack (map hideMissing (unpack word)) ++
    "\n" ++ show guesses ++ " guesses left"
    where hideMissing : Char -> Char
          hideMissing c = if c `elem` missing then '-' else c

data GameCmd : (ty : Type) -> GameState -> (ty -> GameState) -> Type where
  NewGame : (word : String) -> GameCmd () NotRunning (const (Running 6 (length (letters word))))
  Won : GameCmd () (Running (S guesses) 0) (const NotRunning)
  Lost : GameCmd () (Running 0 (S letters)) (const NotRunning)

  Guess : (c : Char) ->
          GameCmd GuessResult (Running (S guesses) (S letters))
                    (\res => case res of
                                  Correct => Running (S guesses) letters
                                  Incorrect => Running guesses (S letters))

  ShowState : GameCmd () state (const state)
  Message : String -> GameCmd () state (const state)
  ReadGuess : GameCmd Char state (const state)

  Pure : (res : ty) -> GameCmd ty (stateFn res) stateFn
  (>>=) : GameCmd a state1 state2Fn ->
          ((res : a) -> GameCmd b (state2Fn res) state3Fn) ->
          GameCmd b state1 state3Fn

namespace Loop
  data GameLoop : (ty : Type) -> GameState -> (ty -> GameState) -> Type where
    (>>=) : GameCmd a state1 state2Fn ->
            ((res : a) -> GameLoop b (state2Fn res) state3Fn) ->
            GameLoop b state1 state3Fn
    Exit : GameLoop () NotRunning (const NotRunning)

data GameResult : (ty : Type) -> (ty -> GameState) -> Type where
  Ok : (res : ty) -> Game (outStateFn res) -> GameResult ty outStateFn
  OutOfFuel : GameResult ty outStateFn

data Fuel = Dry | More (Lazy Fuel)

ok : (res : ty) -> Game (outStateFn res) -> IO (GameResult ty outStateFn)
ok res state = pure (Ok res state)

removeElem : (value : a) -> (xs : Vect (S n) a) ->
             {auto prf : Elem value xs} ->
             Vect n a
removeElem value (value :: ys) {prf = Here} = ys
removeElem {n = Z} value (y :: []) {prf = There later} = absurd later
removeElem {n = S k} value (y :: ys) {prf = There later} = y :: removeElem value ys

runCmd : Fuel -> Game inState -> GameCmd ty inState outStateFn ->
         IO (GameResult ty outStateFn)
runCmd Dry _ _ = pure OutOfFuel
runCmd fuel state (NewGame word) = ok () (InProgress (toUpper word) _ (fromList (letters word)))
runCmd fuel (InProgress word _ _) Won = ok () (GameWon word)
runCmd fuel (InProgress word _ _) Lost = ok () (GameLost word)
runCmd fuel (InProgress word _ missing) (Guess c) =
  case isElem c missing of
       Yes _ => ok Correct (InProgress word _ (removeElem c missing))
       No _ => ok Incorrect (InProgress word _ missing)
runCmd fuel state ShowState = do putStrLn (show state)
                                 ok () state
runCmd fuel state (Message str) = do putStrLn str
                                     ok () state
runCmd (More fuel) state ReadGuess = do
  putStr "Guess: "
  input <- getLine
  case unpack input of
       [x] => if isAlpha x
                 then ok (toUpper x) state
                 else do putStrLn "Invalid input"
                         runCmd fuel state ReadGuess
       _ => do putStrLn "Invalid input"
               runCmd fuel state ReadGuess
runCmd fuel state (Pure res) = ok res state
runCmd fuel state (cmd >>= next) = do Ok cmdRes newState <- runCmd fuel state cmd
                                        | OutOfFuel => pure OutOfFuel
                                      runCmd fuel newState (next cmdRes)

partial
forever : Fuel
forever = More forever

run : Fuel -> Game inState -> GameLoop ty inState outStateFn ->
      IO (GameResult ty outStateFn)
run Dry _ _ = pure OutOfFuel
run (More fuel) state (cmd >>= next) = do Ok cmdRes newState <- runCmd fuel state cmd
                                            | OutOfFuel => pure OutOfFuel
                                          run fuel newState (next cmdRes)
run (More _) state Exit = ok () state

gameLoop : GameLoop () (Running (S guesses) (S letters)) (const NotRunning)
gameLoop {guesses} {letters} = do
  ShowState
  g <- ReadGuess
  ok <- Guess g
  case ok of
       Correct => case letters of
                       Z => do Won
                               ShowState
                               Exit
                       S k => do Message "Correct"
                                 gameLoop
       Incorrect => case guesses of
                         Z => do Lost
                                 ShowState
                                 Exit
                         S k => do Message "Incorrect"
                                   gameLoop

hangman : GameLoop () NotRunning (const NotRunning)
hangman = do NewGame "testing"
             gameLoop

partial
main : IO ()
main = do run forever GameStart hangman
          pure ()
