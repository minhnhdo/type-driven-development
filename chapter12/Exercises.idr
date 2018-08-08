module Exercises

data State : (stateType : Type) -> Type -> Type where
  Get : State stateType stateType
  Put : stateType -> State stateType ()

  Pure : ty -> State stateType ty
  Bind : State stateType a -> (a -> State stateType b) -> State stateType b

mutual
  Functor (State stateType) where
    map func x = do val <- x
                    pure (func val)

  Applicative (State stateType) where
    pure = Pure
    (<*>) f a = do f' <- f
                   a' <- a
                   pure (f' a')

  Monad (State stateType) where
    (>>=) = Bind

get : State stateType stateType
get = Get

put : stateType -> State stateType ()
put = Put

runState : State stateType a -> (st : stateType) -> (a, stateType)
runState Get st = (st, st)
runState (Put newState) st = ((), newState)
runState (Pure x) st = (x, st)
runState (Bind cmd prog) st = let (val, nextState) = runState cmd st in
                                  runState (prog val) nextState

evalState : State stateType a -> (st : stateType) -> a
evalState x st = fst (runState x st)

addIfPositive : Integer -> State Integer Bool
addIfPositive val = do
  when (val > 0) $ do
    current <- get
    put (current + val)
  pure (val > 0)

addPositives : List Integer -> State Integer Nat
addPositives vals = do added <- traverse addIfPositive vals
                       pure (length (filter id added))

data Tree a = Empty | Node (Tree a) a (Tree a)

%name Tree tree

testTree : Tree String
testTree = Node (Node (Node Empty "Jim" Empty) "Fred"
                      (Node Empty "Sheila" Empty)) "Alice"
                (Node Empty "Bob" (Node Empty "Eve" Empty))

flatten : Tree a -> List a
flatten Empty = []
flatten (Node left val right) = flatten left ++ val :: flatten right

-- treeLabelWith : Stream labelType -> Tree a -> (Stream labelType, Tree (labelType, a))
-- treeLabelWith lbls Empty = (lbls, Empty)
-- treeLabelWith lbls (Node left val right) =
--   let (lblThis :: lblsLeft, leftLabeled) = treeLabelWith lbls left
--       (lblsRight, rightLabeled) = treeLabelWith lblsLeft right in
--       (lblsRight, Node leftLabeled (lblThis, val) rightLabeled)

-- treeLabel : Tree a -> Tree (Integer, a)
-- treeLabel tree = snd (treeLabelWith [1..] tree)

treeLabelWith : Tree a -> State (Stream labelType) (Tree (labelType, a))
treeLabelWith Empty = pure Empty
treeLabelWith (Node left val right) =
  do leftLabeled <- treeLabelWith left
     (this :: rest) <- get
     put rest
     rightLabeled <- treeLabelWith right
     pure (Node leftLabeled (this, val) rightLabeled)

treeLabel : Tree a -> Tree (Integer, a)
treeLabel tree = evalState (treeLabelWith tree) [1..]

update : (stateType -> stateType) -> State stateType ()
update f = do st <- get
              put (f st)

increase : Nat -> State Nat ()
increase k = update (+k)

countEmpty : Tree a -> State Nat ()
countEmpty Empty = update (+1)
countEmpty (Node left val right) = do countEmpty left
                                      countEmpty right

countEmptyNode : Tree a -> State (Nat, Nat) ()
countEmptyNode Empty = update (\(e, n) => (e+1, n))
countEmptyNode (Node left val right) = do countEmptyNode left
                                          update (\(e, n) => (e, n+1))
                                          countEmptyNode right
