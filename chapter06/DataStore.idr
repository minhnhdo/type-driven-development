module Main

import Data.Vect

infixr 5 .+.

data Schema = SString
            | SInt
            | SChar
            | (.+.) Schema Schema

Show Schema where
  show SString = "String"
  show SInt = "Int"
  show SChar = "Char"
  show (x .+. y) = "(" ++ show x ++ ", " ++ show y ++ ")"

SchemaType : Schema -> Type
SchemaType SString = String
SchemaType SInt = Int
SchemaType SChar = Char
SchemaType (x .+. y) = (SchemaType x, SchemaType y)

record DataStore where
  constructor MkData
  schema : Schema
  size : Nat
  items : Vect size (SchemaType schema)

addToStore : (store : DataStore) -> (new_item : SchemaType (schema store)) -> DataStore
addToStore (MkData schema' size' items') new_item = MkData _ _ (addToData items')
  where addToData : Vect old (SchemaType schema') -> Vect (old + 1) (SchemaType schema')
        addToData [] = [new_item]
        addToData (x :: xs) = x :: addToData xs

display : SchemaType schema -> String
display {schema = SString} item = show item
display {schema = SInt} item = show item
display {schema = SChar} item = show item
display {schema = (x .+. y)} (iteml, itemr) = display iteml ++ ", " ++ display itemr

getEntry : DataStore -> Integer -> Maybe (String, DataStore)
getEntry store pos = case integerToFin pos (size store) of
                          Nothing => Just ("Out of range\n", store)
                          Just idx => Just (display (index idx (items store)) ++ "\n", store)

data Command : Schema -> Type where
  SetSchema : (new_schema : Schema) -> Command schema
  Add : SchemaType schema -> Command schema
  Get : Integer -> Command schema
  GetAll : Command schema
  Size : Command schema
  Quit : Command schema

parsePrefix : (schema : Schema) -> String -> Maybe (SchemaType schema, String)
parsePrefix SString input = getQuoted (unpack input)
  where getQuoted : List Char -> Maybe (String, String)
        getQuoted [] = Nothing
        getQuoted ('"' :: xs) = case span (/= '"') xs of
                                     (quoted, '"' :: rest) => Just (pack quoted, ltrim (pack rest))
                                     _ => Nothing
        getQuoted _ = Nothing
parsePrefix SInt input = case span isDigit input of
                              ("", rest) => Nothing
                              (num, rest) => Just (cast num, ltrim rest)
parsePrefix SChar input = case unpack input of
                               '\'' :: c :: '\'' :: rest => Just (c, ltrim (pack rest))
                               _ => Nothing
parsePrefix (schemal .+. schemar) input = do (lval, rest) <- parsePrefix schemal input
                                             (rval, rest') <- parsePrefix schemar rest
                                             pure ((lval, rval), rest')

parseBySchema : (schema : Schema) -> String -> Maybe (SchemaType schema)
parseBySchema schema input = case parsePrefix schema input of
                                  Just (res, "") => Just res
                                  Just _ => Nothing
                                  Nothing => Nothing

parseSchema : List String -> Maybe Schema
parseSchema ("String" :: ss) = case ss of
                                    [] => Just SString
                                    _ => case parseSchema ss of
                                              Nothing => Nothing
                                              Just sch => Just (SString .+. sch)
parseSchema ("Int" :: ss) = case ss of
                                 [] => Just SInt
                                 _ => case parseSchema ss of
                                           Nothing => Nothing
                                           Just sch => Just (SInt .+. sch)
parseSchema ("Char" :: ss) = case ss of
                                  [] => Just SChar
                                  _ => case parseSchema ss of
                                            Nothing => Nothing
                                            Just sch => Just (SChar .+. sch)
parseSchema _ = Nothing

setSchema : (store : DataStore) -> Schema -> Maybe DataStore
setSchema store schema = case size store of
                              Z => Just (MkData schema _ [])
                              S _ => Nothing

parseCommand : (schema : Schema) -> (cmd : String) -> (args : String) -> Maybe (Command schema)
parseCommand _ "schema" str = do sch <- parseSchema (words str)
                                 pure (SetSchema sch)
parseCommand schema "add" str = do restok <- parseBySchema schema str
                                   pure (Add restok)
parseCommand schema "get" "" = Just GetAll
parseCommand schema "get" val = case all isDigit (unpack val) of
                                     False => Nothing
                                     True => Just (Get (cast val))
parseCommand schema "size" "" = Just Size
parseCommand schema "quit" "" = Just Quit
parseCommand _ _ _ = Nothing

parse : (schema : Schema) -> (input : String) -> Maybe (Command schema)
parse schema input = case span (/= ' ') input of
                          (cmd, args) => parseCommand schema cmd (ltrim args)

processInput : DataStore -> String -> Maybe (String, DataStore)
processInput store input =
  case parse (schema store) input of
       Nothing => Just ("Invalid command\n", store)
       Just (SetSchema schema') => case setSchema store schema' of
                                        Nothing => Just ("Can't update schema\n", store)
                                        Just store' => Just ("Schema updated to " ++ show schema' ++ "\n", store')
       Just (Add item) => Just ("ID " ++ show (size store) ++ "\n", addToStore store item)
       Just (Get pos) => getEntry store pos
       Just GetAll => Just (showItems store, store)
       Just Size => Just (show (size store) ++ "\n", store)
       Just Quit => Nothing
  where showItems : DataStore -> String
        showItems (MkData schema' size' items') = snd $
          foldr (\x, (i, a) => (i - 1, show i ++ ": " ++ display x ++ "\n" ++ a))
                (the Int (cast size') - 1, "")
                items'

main : IO ()
main = replWith (MkData SString _ []) "Command: " processInput
