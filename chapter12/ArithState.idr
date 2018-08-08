module ArithState

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

runCommand : Command a -> IO a
runCommand (PutStr x) = putStr x
runCommand GetLine = getLine
runCommand (Pure x) = pure x
runCommand (Bind x f) = do val <- runCommand x
                           runCommand (f val)
runCommand GetRandom = ?runCommand_rhs_1
runCommand GetGameState = ?runCommand_rhs_2
runCommand (PutGameState x) = ?runCommand_rhs_3

data ConsoleIO : Type -> Type where
  Quit : a -> ConsoleIO a
  Do : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b

namespace ConsoleDo
  (>>=) : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b
  (>>=) = Do

data Fuel = Dry | More (Lazy Fuel)

partial
forever : Fuel
forever = More forever

run : Fuel -> ConsoleIO a -> IO (Maybe a)
run fuel (Quit x) = pure (Just x)
run Dry _ = pure Nothing
run (More fuel) (Do y f) = do val <- runCommand y
                              run fuel (f val)
