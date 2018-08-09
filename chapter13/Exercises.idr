module Main

import Data.Vect

namespace Door
  data DoorState = DoorClosed | DoorOpen

  data DoorCmd : Type -> DoorState -> DoorState -> Type where
    Open     : DoorCmd () DoorClosed DoorOpen
    Close    : DoorCmd () DoorOpen   DoorClosed
    RingBell : DoorCmd () state state

    Pure : ty -> DoorCmd ty state state
    (>>=) : DoorCmd a state1 state2 -> (a -> DoorCmd b state2 state3) -> DoorCmd b state1 state3

  doorProg : DoorCmd () DoorClosed DoorClosed
  doorProg = do RingBell
                Open
                RingBell
                Close

namespace Machine
  VendState : Type
  VendState = (Nat, Nat)

  data Input = COIN
             | VEND
             | CHANGE
             | REFILL Nat

  data MachineCmd : Type -> VendState -> VendState -> Type where
    InsertCoin : MachineCmd () (pounds, chocs)     (S pounds, chocs)
    Vend       : MachineCmd () (S pounds, S chocs) (pounds, chocs)
    GetCoins   : MachineCmd () (pounds, chocs)     (Z, chocs)
    Refill     : (bars : Nat) ->
                 MachineCmd () (Z, chocs)          (Z, bars + chocs)

    Display    : String -> MachineCmd () state state
    GetInput   : MachineCmd (Maybe Input) state state

    Pure       : ty -> MachineCmd ty state state
    (>>=)      : MachineCmd a state1 state2 -> (a -> MachineCmd b state2 state3) -> MachineCmd b state1 state3

  data MachineIO : VendState -> Type where
    Do : MachineCmd a state1 state2 -> (a -> Inf (MachineIO state2)) -> MachineIO state1

namespace MachineDo
  (>>=) : MachineCmd a state1 state2 -> (a -> Inf (MachineIO state2)) -> MachineIO state1
  (>>=) = Do

mutual
  vend : MachineIO (pounds, chocs)
  vend {pounds = Z} = do Display "Insert a coin"
                         machineLoop
  vend {chocs = Z} = do Display "Out of stock"
                        machineLoop
  vend {pounds = (S k)} {chocs = (S j)} = do Vend
                                             Display "Enjoy!"
                                             machineLoop

  refill : (num : Nat) -> MachineIO (pounds, chocs)
  refill {pounds = Z} num = do Refill num
                               machineLoop
  refill _ = do Display "Can't refill: Coins in machine"
                machineLoop

  machineLoop : MachineIO (pounds, chocs)
  machineLoop = do
    Just x <- GetInput
      | Nothing => do Display "Invalid input"
                      machineLoop
    case x of
         COIN => do InsertCoin
                    machineLoop
         VEND => vend
         CHANGE => do GetCoins
                      Display "Change returned"
                      machineLoop
         REFILL num => refill num

namespace Guess
  data GuessCmd : Type -> Nat -> Nat -> Type where
    Try : Integer -> GuessCmd Ordering (S guessRemaining) guessRemaining

    Pure : ty -> GuessCmd ty state state
    (>>=) : GuessCmd a state1 state2 ->
            (a -> GuessCmd b state2 state3) ->
            GuessCmd b state1 state3

threeGuesses : GuessCmd () 3 0
threeGuesses = do Try 10
                  Try 20
                  Try 5
                  Pure ()

noGuesses : GuessCmd () 0 0
noGuesses = do -- Try 1
               Pure ()

namespace Matter
  data Matter = Solid | Liquid | Gas

  data MatterCmd : Type -> Matter -> Matter -> Type where
    Melt     : MatterCmd () Solid  Liquid
    Boil     : MatterCmd () Liquid Gas
    Condense : MatterCmd () Gas    Liquid
    Freeze   : MatterCmd () Liquid Solid

    Pure     : ty -> MatterCmd ty state state
    (>>=) : MatterCmd a state1 state2 ->
            (a -> MatterCmd b state2 state3) ->
            MatterCmd b state1 state3

iceSteam : MatterCmd () Solid Gas
iceSteam = do Melt
              Boil

steamIce : MatterCmd () Gas Solid
steamIce = do Condense
              Freeze

overMelt : MatterCmd () Solid Gas
overMelt = do Melt
              -- Melt
              Boil

namespace Stack
  data StackCmd : Type -> Nat -> Nat -> Type where
    Push : Integer -> StackCmd () height (S height)
    Pop  : StackCmd Integer (S height) height
    Top  : StackCmd Integer (S height) (S height)

    GetStr : StackCmd String height height
    PutStr : String -> StackCmd () height height

    Pure : ty -> StackCmd ty height height
    (>>=) : StackCmd a height1 height2 ->
            (a -> StackCmd b height2 height3) ->
            StackCmd b height1 height3

  runStack : (stk : Vect inHeight Integer) -> StackCmd ty inHeight outHeight ->
             IO (ty, Vect outHeight Integer)
  runStack stk (Push val) = pure ((), val :: stk)
  runStack (val :: stk) Pop = pure (val, stk)
  runStack (val :: stk) Top = pure (val, val :: stk)
  runStack stk (Pure val) = pure (val, stk)
  runStack stk (cmd >>= next) = do (val, newStk) <- runStack stk cmd
                                   runStack newStk (next val)
  runStack stk GetStr = do str <- getLine
                           pure (str, stk)
  runStack stk (PutStr str) = do putStr str
                                 pure ((), stk)

  data StackIO : Nat -> Type where
    Do : StackCmd a height1 height2 ->
         (a -> Inf (StackIO height2)) ->
         StackIO height1

  namespace StackDo
    (>>=) : StackCmd a height1 height2 ->
            (a -> Inf (StackIO height2)) ->
            StackIO height1
    (>>=) = Do

  data Fuel = Dry | More (Lazy Fuel)

  partial
  forever : Fuel
  forever = More forever

  run : Fuel -> Vect height Integer -> StackIO height -> IO ()
  run Dry _ _ = pure ()
  run (More fuel) stk (Do cmd next) = do (res, newStk) <- runStack stk cmd
                                         run fuel newStk (next res)

testAdd : StackCmd Integer 0 0
testAdd = do Push 10
             Push 20
             val1 <- Pop
             val2 <- Pop
             Pure (val1 + val2)

doAdd : StackCmd () (S (S height)) (S height)
doAdd = do val1 <- Pop
           val2 <- Pop
           Push (val1 + val2)

data StkInput = Number Integer
              | Add
              | Subtract
              | Multiply
              | Negate
              | Discard
              | Duplicate

strToInput : String -> Maybe StkInput
strToInput "" = Nothing
strToInput "add" = Just Add
strToInput "subtract" = Just Subtract
strToInput "multiply" = Just Multiply
strToInput "negate" = Just Negate
strToInput "discard" = Just Discard
strToInput "duplicate" = Just Duplicate
strToInput x = if all isDigit (unpack x)
                  then Just (Number (cast x))
                  else Nothing

mutual
  tryBinOp : (Integer -> Integer -> Integer) -> StackIO height
  tryBinOp {height = (S (S k))} binop = do val1 <- Pop
                                           val2 <- Pop
                                           let result = binop val2 val1
                                           Push result
                                           PutStr (show result ++ "\n")
                                           stackCalc
  tryBinOp _ = do PutStr "Fewer than two items on the stack\n"
                  stackCalc

  tryNegate : StackIO height
  tryNegate {height = (S k)} = do val <- Pop
                                  let result = negate val
                                  Push result
                                  PutStr (show result ++ "\n")
                                  stackCalc
  tryNegate = do PutStr "No item on the stack\n"
                 stackCalc

  tryDiscard : StackIO height
  tryDiscard {height = (S k)} = do val <- Pop
                                   PutStr ("Discarded " ++ show val ++ "\n")
                                   stackCalc
  tryDiscard = do PutStr "No item on the stack\n"
                  stackCalc

  tryDuplicate : StackIO height
  tryDuplicate {height = (S k)} = do val <- Pop
                                     Push val
                                     Push val
                                     PutStr ("Duplicated " ++ show val ++ "\n")
                                     stackCalc
  tryDuplicate = do PutStr "No item on the stack\n"
                    stackCalc

  stackCalc : StackIO height
  stackCalc = do PutStr "> "
                 input <- GetStr
                 case strToInput input of
                      Nothing => do PutStr "Invalid input\n"
                                    stackCalc
                      Just (Number x) => do Push x
                                            stackCalc
                      Just Add => tryBinOp (+)
                      Just Subtract => tryBinOp (-)
                      Just Multiply => tryBinOp (*)
                      Just Negate => tryNegate
                      Just Discard => tryDiscard
                      Just Duplicate => tryDuplicate

main : IO ()
main = run forever [] stackCalc
