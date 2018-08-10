module Main

import Data.Vect

namespace Door
  data DoorState = DoorClosed | DoorOpen

  data DoorResult = Ok | Jammed

  data DoorCmd : (ty : Type) -> DoorState -> (ty -> DoorState) -> Type where
    Open     : DoorCmd DoorResult DoorClosed (\res => case res of
                                                           Ok => DoorOpen
                                                           Jammed => DoorClosed)
    Close    : DoorCmd () DoorOpen           (const DoorClosed)
    RingBell : DoorCmd () state              (const state)

    Display  : String -> DoorCmd () state (const state)

    Pure : (res : ty) -> DoorCmd ty (stateFn res) stateFn
    (>>=) : DoorCmd a state1 state2Fn ->
            ((res : a) -> DoorCmd b (state2Fn res) state3Fn) ->
            DoorCmd b state1 state3Fn

doorProg : DoorCmd () DoorClosed (const DoorClosed)
doorProg = do RingBell
              Ok <- Open | Jammed => Display "Door jammed"
              Display "Glad to be of service"
              Close
              Ok <- Open | Jammed => Display "Door jammed"
              Display "Glad to be of service"
              Close

logOpen : DoorCmd DoorResult DoorClosed (\res => case res of
                                                      Ok => DoorOpen
                                                      Jammed => DoorClosed)
logOpen = do Display "Trying to open door"
             Ok <- Open | Jammed => do Display "Jammed"
                                       Pure Jammed
             Display "Success"
             Pure Ok

namespace ATM
  PIN : Type
  PIN = Vect 4 Char

  data ATMState = Ready | CardInserted | Session

  data PINCheck = CorrectPIN | IncorrectPIN

  data HasCard : ATMState -> Type where
    HasCardInserted : HasCard CardInserted
    HasSession      : HasCard Session

  data ATMCmd : (ty : Type) -> ATMState -> (ty -> ATMState) -> Type where
    InsertCard : ATMCmd ()  Ready        (const CardInserted)
    EjectCard  : {auto prf : HasCard state} ->
                 ATMCmd ()  state        (const Ready)
    GetPIN     : ATMCmd PIN CardInserted (const CardInserted)

    CheckPIN   : PIN -> ATMCmd PINCheck CardInserted
                          (\check => case check of
                                          CorrectPIN => Session
                                          IncorrectPIN => CardInserted)

    GetAmount  : ATMCmd Nat state (const state)
    Dispense   : (amount : Nat) -> ATMCmd () Session (const Session)
    Message    : String -> ATMCmd () state (const state)

    Pure : (res : ty) -> ATMCmd ty (stateFn res) stateFn
    (>>=) : ATMCmd a state1 state2Fn ->
            ((res : a) -> ATMCmd b (state2Fn res) state3Fn) ->
            ATMCmd b state1 state3Fn

atm : ATMCmd () Ready (const Ready)
atm = do InsertCard
         pin <- GetPIN
         cash <- GetAmount
         pinOK <- CheckPIN pin
         Message "Checking card"
         case pinOK of
              CorrectPIN => do Dispense cash
                               EjectCard
                               Message "Please remove your card and cash"
              IncorrectPIN => do Message "Incorrect PIN"
                                 EjectCard

insertEject : ATMCmd () Ready (const Ready)
insertEject = do InsertCard
                 EjectCard

-- badATM : ATMCmd () Ready (const Ready)
-- badATM = EjectCard

testPIN : Vect 4 Char
testPIN = ['1', '2', '3', '4']

readVect : (n : Nat) -> IO (Vect n Char)
readVect Z = do _ <- getLine
                pure []
readVect (S k) = do ch <- getChar
                    chs <- readVect k
                    pure (ch :: chs)

runATM : ATMCmd res inState outStateFn -> IO res
runATM InsertCard = do putStrLn "Please insert your card (press Enter)"
                       _ <- getLine
                       pure ()
runATM EjectCard = putStrLn "Card ejected"
runATM GetPIN = do putStr "Enter PIN: "
                   readVect 4
runATM (CheckPIN pin) = if pin == testPIN
                           then pure CorrectPIN
                           else pure IncorrectPIN
runATM GetAmount = do putStr "How much would you like? "
                      x <- getLine
                      pure (cast x)
runATM (Dispense amount) = putStrLn ("Here is " ++ show amount)
runATM (Message msg) = putStrLn msg
runATM (Pure res) = pure res
runATM (x >>= f) = do x' <- runATM x
                      runATM (f x')

namespace Shell
  data Access = LoggedOut | LoggedIn

  data PwdCheck = Correct | Incorrect

  data ShellCmd : (ty : Type) -> Access -> (ty -> Access) -> Type where
    Password  : String -> ShellCmd PwdCheck LoggedOut
                            (\check => case check of
                                            Correct => LoggedIn
                                            Incorrect => LoggedOut)
    Logout    : ShellCmd () LoggedIn (const LoggedOut)
    GetSecret : ShellCmd String LoggedIn (const LoggedIn)

    PutStr    : String -> ShellCmd () state (const state)
    Pure : (res : ty) -> ShellCmd ty (stateFn res) stateFn
    (>>=) : ShellCmd a state1 state2Fn ->
            ((res : a) -> ShellCmd b (state2Fn res) state3Fn) ->
            ShellCmd b state1 state3Fn

session : ShellCmd () LoggedOut (const LoggedOut)
session = do Correct <- Password "wurzel"
               | Incorrect => PutStr "Wrong password"
             msg <- GetSecret
             PutStr ("Secret code: " ++ show msg ++ "\n")
             Logout

-- sessionBad : ShellCmd () LoggedOut (const LoggedOut)
-- sessionBad = do Password "wurzel"
--                 msg <- GetSecret
--                 PutStr ("Secret code: " ++ show msg ++ "\n")
--                 Logout

-- noLogout : ShellCmd () LoggedOut (const LoggedOut)
-- noLogout = do Correct <- Password "wurzel"
--                 | Incorrect => PutStr "Wrong password"
--               msg <- GetSecret
--               PutStr ("Secret code: " ++ show msg ++ "\n")

namespace Machine
  VendState : Type
  VendState = (Nat, Nat)

  data Input = COIN
             | VEND
             | CHANGE
             | REFILL Nat

  data CoinResult = CoinAccepted | CoinRejected

  data MachineCmd : (ty : Type) -> VendState -> (ty -> VendState) -> Type where
    InsertCoin : MachineCmd CoinResult (pounds, chocs)
                    (\check => case check of
                                    CoinAccepted => (S pounds, chocs)
                                    CoinRejected => (pounds, chocs))
    Vend       : MachineCmd ()         (S pounds, S chocs) (const (pounds, chocs))
    GetCoins   : MachineCmd ()         (pounds, chocs)     (const (Z, chocs))
    Refill     : (bars : Nat) ->
                 MachineCmd ()         (Z, chocs)          (const (Z, bars + chocs))

    Display    : String -> MachineCmd () state (const state)
    GetInput   : MachineCmd (Maybe Input) state (const state)

    Pure : (res : ty) -> MachineCmd ty (stateFn res) stateFn
    (>>=) : MachineCmd a state1 state2Fn ->
            ((res : a) -> MachineCmd b (state2Fn res) state3Fn) ->
            MachineCmd b state1 state3Fn

  data MachineIO : VendState -> Type where
    Do : MachineCmd a state1 state2Fn -> ((res : a) -> Inf (MachineIO (state2Fn res))) -> MachineIO state1

namespace MachineDo
  (>>=) : MachineCmd a state1 state2Fn -> ((res : a) -> Inf (MachineIO (state2Fn res))) -> MachineIO state1
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
         COIN => do CoinAccepted <- InsertCoin
                      | CoinRejected => do Display "Coin rejected"
                                           machineLoop
                    machineLoop
         VEND => vend
         CHANGE => do GetCoins
                      Display "Change returned"
                      machineLoop
         REFILL num => refill num
