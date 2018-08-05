module Main

-- data EqNat : (num1 : Nat) -> (num2 : Nat) -> Type where
--   Same : (num : Nat) -> EqNat num num

-- sameS : (k : Nat) -> (j : Nat) -> (eq : EqNat k j) -> EqNat (S k) (S j)
-- sameS j j (Same j) = Same $ S j

-- checkEqNat : (num1 : Nat) -> (num2 : Nat) -> Maybe (EqNat num1 num2)
-- checkEqNat Z Z = Just $ Same Z
-- checkEqNat Z (S k) = Nothing
-- checkEqNat (S k) Z = Nothing
-- checkEqNat (S k) (S j) = case checkEqNat k j of
--                               Nothing => Nothing
--                               Just eq => Just (sameS _ _ eq)

-- checkEqNat : (num1 : Nat) -> (num2 : Nat) -> Maybe (num1 = num2)
-- checkEqNat Z Z = Just Refl
-- checkEqNat Z (S k) = Nothing
-- checkEqNat (S k) Z = Nothing
-- checkEqNat (S k) (S j) = case checkEqNat k j of
--                               Nothing => Nothing
--                               Just prf => Just (cong prf)

data Vect : Nat -> Type -> Type where
     Nil  : Vect Z a
     (::) : a -> Vect k a -> Vect (S k) a

-- exactLength : (len : Nat) -> (input : Vect m a) -> Maybe (Vect len a)
-- exactLength {m} len input = case checkEqNat m len of
--                                  Nothing => Nothing
--                                  Just Refl => Just input

sameCons : {xs : List a} -> {ys : List a} -> xs = ys -> x :: xs = x :: ys
sameCons prf = cong prf

sameLists : {xs : List a} -> {ys : List a} -> x = y -> xs = ys -> x :: xs = y :: ys
sameLists Refl Refl = Refl

data ThreeEq : a -> b -> c -> Type where
  SameThree : (v : ty) -> ThreeEq v v v

allSameS : (x, y, z : Nat) -> ThreeEq x y z -> ThreeEq (S x) (S y) (S z)
allSameS z z z (SameThree z) = SameThree (S z)

infixr 7 ++

(++) : Vect n elem -> Vect m elem -> Vect (n + m) elem
(++) [] y = y
(++) (x :: z) y = x :: z ++ y

myReverse : Vect n a -> Vect n a
myReverse [] = []
myReverse (x :: xs) = reverseProof (myReverse xs ++ [x])
  where reverseProof : Vect (k + 1) elem -> Vect (S k) elem
        reverseProof {k} result = rewrite plusCommutative 1 k in result

myAppend : Vect n elem -> Vect m elem -> Vect (m + n) elem
myAppend [] ys = append_nil ys
  where append_nil : Vect m elem -> Vect (m + 0) elem
        append_nil {m} xs = rewrite plusZeroRightNeutral m in xs
myAppend (x :: xs) ys = append_xs (x :: myAppend xs ys)
  where append_xs : Vect (S (m + len)) elem -> Vect (m + S len) elem
        append_xs {m} {len} xs = rewrite sym (plusSuccRightSucc m len) in xs

myPlusCommutes : (n : Nat) -> (m : Nat) -> n + m = m + n
myPlusCommutes Z m = rewrite plusZeroRightNeutral m in Refl
myPlusCommutes (S k) m = rewrite myPlusCommutes k m in
                                 rewrite plusSuccRightSucc m k in
                                         Refl

myReverse' : Vect n elem -> Vect n elem
myReverse' xs = myReverseHelper [] xs
  where myReverseHelper_nil : Vect n elem -> Vect (n + 0) elem
        myReverseHelper_nil {n} xs = rewrite plusZeroRightNeutral n in xs
        myReverseHelper_xs : Vect (S (n + m)) elem -> Vect (n + S m) elem
        myReverseHelper_xs {n} {m} result = rewrite sym (plusSuccRightSucc n m) in result
        myReverseHelper : Vect n elem -> Vect m elem -> Vect (n + m) elem
        myReverseHelper acc [] = myReverseHelper_nil acc
        myReverseHelper acc (x :: ys) = myReverseHelper_xs (myReverseHelper (x :: acc) ys)

twoPlusTwoIsNotFive : 2 + 2 = 5 -> Void
twoPlusTwoIsNotFive Refl impossible

valueNotSucc : (x : Nat) -> x = S x -> Void
valueNotSucc _ Refl impossible

zeroNotSucc : 0 = S k -> Void
zeroNotSucc Refl impossible

succNotZero : S k = 0 -> Void
succNotZero Refl impossible

noRec : (contra : k = j -> Void) -> S k = S j -> Void
noRec contra Refl = contra Refl

checkEqNat : (num1 : Nat) -> (num2 : Nat) -> Dec (num1 = num2)
checkEqNat Z Z = Yes Refl
checkEqNat Z (S k) = No zeroNotSucc
checkEqNat (S k) Z = No succNotZero
checkEqNat (S k) (S j) = case checkEqNat k j of
                              Yes prf => Yes (cong prf)
                              No contra => No (noRec contra)

exactLength : (len : Nat) -> (input : Vect m a) -> Maybe (Vect len a)
exactLength {m} len input = case decEq m len of
                                 Yes Refl => Just input
                                 No contra => Nothing

headUnequal : DecEq a => {xs : Vect n a} -> {ys : Vect n a} -> (contra : (x = y) -> Void) -> ((x :: xs) = (y :: ys)) -> Void
headUnequal contra Refl = contra Refl

tailUnequal : DecEq a => {xs : Vect n a} -> {ys : Vect n a} -> (contra : (xs = ys) -> Void) -> ((x :: xs) = (y :: ys)) -> Void
tailUnequal contra Refl = contra Refl

DecEq elem => DecEq (Vect n elem) where
  decEq [] [] = Yes Refl
  decEq (x :: y) (z :: w) =
    case decEq x z of
         Yes Refl => case decEq y w of
                          Yes Refl => Yes Refl
                          No contra => No (tailUnequal contra)
         No contra => No (headUnequal contra)
