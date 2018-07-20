module Main

import Data.Vect

data DataStore : Type where
  MkData : (size : Nat) -> (items : Vect size String) -> DataStore

size : DataStore -> Nat
size (MkData size' _) = size'

items : (store : DataStore) -> Vect (size store) String
items (MkData _ items') = items'

data Command = Add String
             | Search String
             | Get Integer
             | Size
             | Quit

addToStore : DataStore -> String -> DataStore
addToStore (MkData size items) str = MkData _ (addToData items)
  where addToData : Vect old String -> Vect (old + 1) String
        addToData [] = [str]
        addToData (x :: xs) = x :: addToData xs

parseCommand : (cmd : String) -> (args : String) -> Maybe Command
parseCommand "add" str = Just (Add str)
parseCommand "search" str = Just (Search str)
parseCommand "get" val = case all isDigit (unpack val) of
                              False => Nothing
                              True => Just (Get (cast val))
parseCommand "size" "" = Just Size
parseCommand "quit" "" = Just Quit
parseCommand _ _ = Nothing

parse : (input : String) -> Maybe Command
parse input = case span (/= ' ') input of
                   (cmd, args) => parseCommand cmd (ltrim args)

getEntry : DataStore -> Integer -> Maybe (String, DataStore)
getEntry store pos = case integerToFin pos (size store) of
                          Nothing => Just ("Out of range\n", store)
                          Just idx => Just (index idx (items store) ++ "\n", store)

search : DataStore -> String -> Maybe (String, DataStore)
search store str =
  let intermediate = snd $ foldr (\elem, (i, acc) => (i + 1, if str `isInfixOf` elem
                                                                then acc ++ show i ++ ": " ++ elem ++ "\n"
                                                                else acc))
                                 (0, "")
                                 (items store)
      result = if length intermediate == 0
                  then "Not found\n"
                  else intermediate
  in Just (result, store)

processInput : DataStore -> String -> Maybe (String, DataStore)
processInput store input = case parse input of
                                Nothing => Just ("Invalid command\n", store)
                                Just (Add str) => Just ("ID " ++ show (size store) ++ "\n", addToStore store str)
                                Just (Search str) => search store str
                                Just (Get pos) => getEntry store pos
                                Just Size => Just (show (size store) ++ "\n", store)
                                Just Quit => Nothing

main : IO ()
main = replWith (MkData _ []) "Command: " processInput
