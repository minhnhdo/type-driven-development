module Process

import System.Concurrency.Channels

%default total

export
data MessagePid : (iface : reqType -> Type) -> Type where
  MkMessage : PID -> MessagePid iface

public export
data ProcState = NoRequest | Sent | Complete

public export
data Process : (iface : regType -> Type) -> Type ->
               (inState : ProcState) -> (outState : ProcState) -> Type where
  Request : MessagePid serviceIface -> (message : serviceReqType) ->
            Process iface (serviceIface message) state state
  Respond : ((msg : reqType) -> Process iface (iface msg) NoRequest NoRequest) ->
            Process iface (Maybe reqType) state Sent
  Spawn : Process serviceIface () NoRequest Complete ->
          Process iface (Maybe (MessagePid serviceIface)) state state
  Loop : Inf (Process iface a NoRequest Complete) ->
         Process iface a Sent Complete
  Action : IO a -> Process iface a state state

  Pure : a -> Process iface a state state
  (>>=) : Process iface a state1 state2 ->
          (a -> Process iface b state2 state3) ->
          Process iface b state1 state3

public export
NoRecv : Void -> Type
NoRecv = const Void

public export
Service : (iface : reqType -> Type) -> Type -> Type
Service iface a = Process iface a NoRequest Complete

public export
Client : Type -> Type
Client a = Process NoRecv a NoRequest NoRequest

public export
data Fuel = Dry | More (Lazy Fuel)

export partial
forever : Fuel
forever = More forever

export
run : Fuel -> Process iface t inState outState -> IO (Maybe t)
run Dry _ = pure Nothing
run fuel (Request {serviceIface} (MkMessage pid) msg) = do
  Just chan <- connect pid
    | Nothing => pure Nothing
  ok <- unsafeSend chan msg
  if ok
     then do Just x <- unsafeRecv (serviceIface msg) chan
               | Nothing => pure Nothing
             pure (Just x)
     else pure Nothing
run fuel (Respond {reqType} calc) = do Just sender <- listen 1
                                         | Nothing => pure (Just Nothing)
                                       Just msg <- unsafeRecv reqType sender
                                         | Nothing => pure (Just Nothing)
                                       Just res <- run fuel (calc msg)
                                         | Nothing => pure Nothing
                                       unsafeSend sender res
                                       pure (Just (Just msg))
run fuel (Spawn proc) = do Just pid <- spawn (do run fuel proc
                                                 pure ())
                             | Nothing => pure (Just Nothing)
                           pure (Just (Just (MkMessage pid)))
run (More fuel) (Loop act) = run fuel act
run fuel (Action act) = do res <- act
                           pure (Just res)
run fuel (Pure x) = pure (Just x)
run fuel (act >>= next) = do Just x <- run fuel act
                               | Nothing => pure Nothing
                             run fuel (next x)

export partial
runProc : Process iface () inState outState -> IO ()
runProc proc = do run forever proc
                  pure ()
