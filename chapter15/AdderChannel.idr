module Main

import System.Concurrency.Channels

data Message = Add Nat Nat

adder : IO ()
adder = do Just senderChan <- listen 1
             | Nothing => adder
           Just msg <- unsafeRecv Message senderChan
             | Nothing => adder
           case msg of
                Add x y => do ok <- unsafeSend senderChan (x + y)
                              adder

main : IO ()
main = do Just adderId <- spawn adder
            | Nothing => putStrLn "Spawn failed"
          Just chan <- connect adderId
            | Nothing => putStrLn "Connection failed"
          ok <- unsafeSend chan (Add 2 3)
          Just answer <- unsafeRecv Nat chan
            | Nothing => putStrLn "Send failed"
          printLn answer
