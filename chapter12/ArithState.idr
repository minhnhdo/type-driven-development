module ArithState

import Data.Primitives.Views
import System

%default total

GameState : Type

data Command : Type -> Type where
  PutStr : String -> Command ()
  GetLine : Command String

  GetRandom : Command Int
  GetGameState : Command GameState
  PutGameState : GameState -> Command ()

  Pure : ty -> Command ty
  Bind : Command a -> (a -> Command b) -> Command b

mutual
  Functor Command where
    map func x = do val <- x
                    pure (func val)

  Applicative Command where
    pure = Pure
    (<*>) f a = do f' <- f
                   a' <- a
                   pure (f' a')

  Monad Command where
    (>>=) = Bind

data ConsoleIO : Type -> Type where
  Quit : a -> ConsoleIO a
  Do : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b

namespace ConsoleDo
  (>>=) : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b
  (>>=) = Do

data Input = Answer Int
           | QuitCmd

data Fuel = Dry | More (Lazy Fuel)

partial
forever : Fuel
forever = More forever

record Score where
  constructor MkScore
  correct : Nat
  attempted : Nat

record GameState where
  constructor MkGameState
  score : Score
  difficulty : Int

initState : GameState
initState = MkGameState (MkScore 0 0) 12

updateGameState : (GameState -> GameState) -> Command ()
updateGameState f = do st <- GetGameState
                       PutGameState (f st)

Show GameState where
  show st = show (correct (score st)) ++ "/" ++
            show (attempted (score st)) ++ "\n" ++
            "Difficulty: " ++ show (difficulty st)

setDifficulty : Int -> GameState -> GameState
setDifficulty newDiff state = record { difficulty = newDiff } state

addWrong : GameState -> GameState
addWrong state = record { score->attempted $= (+ 1) } state

addCorrect : GameState -> GameState
addCorrect state = record { score->correct $= (+ 1)
                          , score->attempted $= (+ 1)
                          } state

mutual
  correct : ConsoleIO GameState
  correct = do PutStr "Correct!\n"
               updateGameState addCorrect
               quiz

  wrong : Int -> ConsoleIO GameState
  wrong ans = do PutStr ("Wrong, the answer is " ++ show ans ++ "\n")
                 updateGameState addWrong
                 quiz

  readInput : (prompt : String) -> Command Input
  readInput prompt = do PutStr prompt
                        answer <- GetLine
                        if toLower answer == "quit"
                           then Pure QuitCmd
                           else Pure (Answer (cast answer))

  quiz : ConsoleIO GameState
  quiz = do num1 <- GetRandom
            num2 <- GetRandom
            st <- GetGameState
            PutStr (show st ++ "\n")

            input <- readInput (show num1 ++ " * " ++ show num2 ++ "? ")
            case input of
                 Answer answer => if answer == num1 * num2
                                     then correct
                                     else wrong (num1 * num2)
                 QuitCmd => Quit st

runCommand : Stream Int -> GameState -> Command a -> IO (a, Stream Int, GameState)
runCommand rnds state (PutStr x) = do putStr x
                                      pure ((), rnds, state)
runCommand rnds state GetLine = do str <- getLine
                                   pure (str, rnds, state)
runCommand rnds state (Pure x) = pure (x, rnds, state)
runCommand rnds state (Bind x f) = do (val, newRnds, newState) <- runCommand rnds state x
                                      runCommand newRnds newState (f val)
runCommand (val :: rnds) state GetRandom =
  pure (getRandom val (difficulty state), rnds, state)
  where getRandom : Int -> Int -> Int
        getRandom val max with (divides val max)
          getRandom val 0 | DivByZero = 1
          getRandom ((max * div) + rem) max | (DivBy prf) = abs rem + 1
runCommand rnds state GetGameState = pure (state, rnds, state)
runCommand rnds state (PutGameState newState) = pure ((), rnds, newState)

run : Fuel -> Stream Int -> GameState -> ConsoleIO a -> IO (Maybe a, Stream Int, GameState)
run fuel rnds state (Quit x) = pure (Just x, rnds, state)
run Dry rnds state _ = pure (Nothing, rnds, state)
run (More fuel) rnds state (Do y f) = do
  (val, newRnds, newState) <- runCommand rnds state y
  run fuel newRnds newState (f val)

randoms : Int -> Stream Int
randoms seed = let seed' = 1664525 * seed + 1013904223 in
                   (seed' `shiftR` 2) :: randoms seed'

partial
main : IO ()
main = do
  seed <- time
  (Just score, _, state) <- run forever (randoms (fromInteger seed)) initState quiz
    | _ => putStrLn "Ran out of fuel"
  putStrLn ("Final score: " ++ show state)

record Votes where
  constructor MkVotes
  upvotes : Integer
  downvotes : Integer

record Article where
  constructor MkArticle
  title : String
  url : String
  score : Votes

%name Article article

initPage : (title : String) -> (url : String) -> Article
initPage title url = MkArticle title url (MkVotes 0 0)

badSite : Article
badSite = MkArticle "Bad Page" "https://example.com/bad" (MkVotes 5 47)

goodSite : Article
goodSite = MkArticle "Good Page" "https://example.com/good" (MkVotes 101 7)

getScore : Article -> Integer
getScore (MkArticle _ _ score) = upvotes score - downvotes score

addUpvote : Article -> Article
addUpvote article = record { score->upvotes $= (+1) } article

addDownvote : Article -> Article
addDownvote article = record { score->downvotes $= (+1) } article
