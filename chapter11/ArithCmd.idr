module Main

import Data.Primitives.Views
import System

%default total

data Fuel = Dry | More (Lazy Fuel)

data Command : Type -> Type where
  PutStr : String -> Command ()
  GetLine : Command String
  ReadFile : String -> Command (Either FileError String)
  WriteFile : String -> String -> Command (Either FileError ())

  Pure : ty -> Command ty
  Bind : Command a -> (a -> Command b) -> Command b

namespace CommandDo
  (>>=) : Command a -> (a -> Command b) -> Command b
  (>>=) = Bind

data ConsoleIO : Type -> Type where
  Quit : a -> ConsoleIO a
  Do : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b

namespace ConsoleDo
  (>>=) : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b
  (>>=) = Do

runCommand : Command a -> IO a
runCommand (PutStr x) = putStr x
runCommand GetLine = getLine
runCommand (ReadFile fname) = readFile fname
runCommand (WriteFile fname contents) = writeFile fname contents
runCommand (Pure x) = pure x
runCommand (Bind x f) = do val <- runCommand x
                           runCommand (f val)

run : Fuel -> ConsoleIO a -> IO (Maybe a)
run fuel (Quit val) = do pure (Just val)
run Dry _ = do pure Nothing
run (More fuel) (Do cmd f) = do val <- runCommand cmd
                                run fuel (f val)

partial
forever : Fuel
forever = More forever

randoms : Int -> Stream Int
randoms seed = let seed' = 1664525 * seed + 1013904223 in
                   (seed' `shiftR` 2) :: randoms seed'

arithInputs : Int -> Stream Int
arithInputs seed = map bound (randoms seed)
  where bound : Int -> Int
        bound num with (divides num 12)
          bound ((12 * _) + rem) | (DivBy _) = rem + 1

data Input = Answer Int
           | QuitCmd

readInput : (prompt : String) -> Command Input
readInput prompt = do PutStr prompt
                      answer <- GetLine
                      if toLower answer == "quit"
                         then Pure QuitCmd
                         else Pure (Answer (cast answer))

mutual
  correct : Stream Int -> (nQuestion : Nat) -> (score : Nat) -> ConsoleIO Nat
  correct nums nQuestion score = do PutStr "Correct!\n"
                                    quiz nums (nQuestion + 1) (score + 1)

  wrong : Stream Int -> Int -> (nQuestion : Nat) -> (score : Nat) -> ConsoleIO Nat
  wrong nums ans nQuestion score = do
    PutStr ("Wrong, the answer is " ++ show ans ++ "\n")
    quiz nums (nQuestion + 1) score

  quiz : Stream Int -> (nQuestion : Nat) -> (score : Nat) -> ConsoleIO Nat
  quiz (num1 :: num2 :: nums) nQuestion score = do
    PutStr ("Score so far: " ++ show score ++ " / " ++ show nQuestion ++ "\n")
    input <- readInput (show num1 ++ " * " ++ show num2 ++ "? ")
    case input of
         Answer answer => if answer == num1 * num2
                             then correct nums nQuestion score
                             else wrong nums (num1 * num2) nQuestion score
         QuitCmd => Quit score

data ShellInput = Cat String
                | Copy String String
                | Exit

processShellInput : (cmd : String) -> (rest : String) -> Maybe ShellInput
processShellInput "exit" "" = Just Exit
processShellInput "cat" rest = Just (Cat rest)
processShellInput "copy" rest =
  let (fromFileName, rest') = span (/= ' ') rest
      toFileName = ltrim rest' in
      case (fromFileName, toFileName) of
           ("", _) => Nothing
           (_, "") => Nothing
           _ => Just (Copy fromFileName toFileName)
processShellInput _ _ = Nothing

readShellInput : (prompt : String) -> Command (Maybe ShellInput)
readShellInput prompt = do PutStr prompt
                           answer <- GetLine
                           let (cmd, rest) = span (/= ' ') answer
                           Pure $ processShellInput (toLower cmd) (ltrim rest)

interactiveShell : ConsoleIO ()
interactiveShell = do
  Just cmd <- readShellInput "> "
    | Nothing => do PutStr "Invalid command!\n"
                    interactiveShell
  case cmd of
       Cat fileName => do
         Right contents <- ReadFile fileName
           | Left err => do
               PutStr $ "Error reading " ++ fileName ++ ": " ++ show err ++ "\n"
               interactiveShell
         PutStr contents
         interactiveShell
       Copy fromFileName toFileName => do
         Right contents <- ReadFile fromFileName
           | Left err => do
               PutStr $ "Error reading " ++ fromFileName ++ ": " ++ show err ++ "\n"
               interactiveShell
         Right _ <- WriteFile toFileName contents
           | Left err => do
               PutStr $ "Error writing to " ++ toFileName ++ ": " ++ show err ++ "\n"
               interactiveShell
         interactiveShell
       Exit => Quit ()

partial
main : IO ()
main = do seed <- time
          Just score <- run forever (quiz (arithInputs (fromInteger seed)) 0 0)
            | Nothing => putStrLn "Ran out of fuel"
          putStrLn ("Final score: " ++ show score)
