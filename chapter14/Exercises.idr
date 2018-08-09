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
