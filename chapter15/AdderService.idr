module Main

import Process

%default total

data Message = Add Nat Nat

AdderType : Message -> Type
AdderType (Add x y) = Nat

procAdder : Service AdderType ()
procAdder = do Respond (\msg => case msg of
                                     Add x y => Pure (x + y))
               Loop procAdder

procAdderMain : Client ()
procAdderMain = do Just adderId <- Spawn procAdder
                     | Nothing => Action (putStrLn "Spawn failed")
                   answer <- Request adderId (Add 2 3)
                   Action (printLn answer)

partial
main : IO ()
main = do run forever procAdderMain
          pure ()
