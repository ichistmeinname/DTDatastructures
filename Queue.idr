module Queue
{-
  Reimplementation of a double-ended queue (as presented by Okasaki)
   with different explicit encodings of the invariant
-}

{-
---  Haskell code  ---
emptyQueue :: Queue a
emptyQueue = Q [] []

isEmptyQueue :: Queue a -> Bool
isEmptyQueue (Q xs _) = null xs

queue :: [a] -> [a] -> Queue a
queue [] ys = Q (reverse ys) []
queue xs ys = Q xs ys

enqueue :: a -> Queue a -> Queue a
enqueue x (Q xs ys) = queue xs (x:ys)

next :: Queue a -> a
next (Q (x:_) _) = x

dequeue :: Queue a -> Queue a
dequeue (Q (_:xs) ys) = queue xs ys
-}

{- Exact reimplementation of the Haskell version -}

data QueueH a = HQueue (List a) (List a)

total emptyH : QueueH a
emptyH = HQueue [] []

total isEmptyH : QueueH a -> Bool
isEmptyH (HQueue xs _) = isNil xs

total queueH : List a -> List a -> QueueH a
queueH [] ys = HQueue (reverse ys) []
queueH (x :: xs) ys = HQueue xs ys

total enqueueH : a -> QueueH a -> QueueH a
enqueueH x (HQueue xs ys) = queueH xs (x :: ys)

{- Cannot define next as total ... -}
nextH : QueueH a -> a
-- next (HQueue [] _) =
nextH (HQueue (x :: _) _) = x

{- ... as well as dequeue -}
dequeueH : QueueH a -> QueueH a
-- dequeue (HQueue [] ys) =
dequeueH (HQueue (_ :: xs) ys) = queueH xs ys


{- Representation with two constructors and explicit
    proof about non-empty first list argument for the
    second constructor
-}
data QueueEq : (a : Type) ->  List a -> Type where
   QNilEq : QueueEq a []
   QConsEq : (xs : List a) -> (ys : List a)
           -> {neq : Not (xs = [])} -> QueueEq a (xs ++ reverse ys)

total emptyQueue : QueueEq a []
emptyQueue = QNilEq

total isEmptyQueue : QueueEq a xs -> Bool
isEmptyQueue QNilEq = True
isEmptyQueue (QConsEq _ _) = False

total queueEq : (xs : List a) -> (ys : List a) -> QueueEq a (xs ++ reverse ys)
queueEq [] [] = QNilEq
queueEq [] (y :: ys) with (reverse (y :: ys))
  queueEq [] (y :: ys) | [] = QNilEq
  queueEq [] (y :: ys) | (z :: zs) =
    rewrite sym (appendNilRightNeutral (z :: zs))
    in QConsEq (z :: zs) [] {neq = funImpossible}
   where funImpossible Refl impossible
queueEq (x :: xs) ys = QConsEq (x :: xs) ys {neq = funImpossible}
 where funImpossible Refl impossible

{- We do acutally need to pattern match on `reverse (y :: ys)` in order to know that the
    resulting term cannot be empty

     - + Errors (1)
      `-- Queue.idr line 107 col 21:
          Queue.queueEq', funImpossible a y ys Refl is a valid case
-}
-- queueEq' : (xs : List a) -> (ys : List a) -> QueueEq a (xs ++ reverse ys)
-- queueEq' [] [] = QNilEq
-- queueEq' [] (y :: ys) =
--   rewrite sym (appendNilRightNeutral (reverse (y :: ys)))
--   in QConsEq (reverse (y :: ys)) [] {neq = funImpossible}
--  where funImpossible Refl impossible
-- queueEq' (x :: xs) ys = QConsEq (x :: xs) ys {neq = ?neq}

total enqueueEq : {xs : List a} -> (x : a) -> QueueEq a xs -> QueueEq a (x :: xs)
enqueueEq x QNilEq = QConsEq (x :: []) [] {neq = funImpossible}
 where funImpossible Refl impossible
enqueueEq x (QConsEq xs ys {neq = xsNotNil}) = QConsEq (x :: xs) ys {neq = funImpossible}
 where funImpossible Refl impossible

total nextEq : {xs : List a} -> {neq : Not (xs = [])} -> QueueEq a xs -> a
-- nextEq {neq = neq} QNilEq  with (neq Refl) -- = void (neq Refl)
--   nextEq {neq = neq} QNilEq | Refl impossible
nextEq {neq = neq} QNilEq = void (neq Refl)
nextEq (QConsEq [] ys {neq = neq}) = void (neq Refl)
nextEq (QConsEq (x :: xs) ys {neq = neq}) = x

-- {- {- Here, the used encoding is not usable, since the type-checker
--        does not know, if the constructor is even possible --
--        the same actually holds for the analogues definition of `nextN`
-- -}
-- dequeueEq' : QueueEq a (x :: xs) -> QueueEq a xs
-- dequeueEq' (QConsEq xs ys) = ?e

-- nextEq' : QueueEq a (x :: xs) -> a
-- nextEq' (QConsEq xs ys) = ?
-- -}

total dequeueEq : {xs : List a} -> {neq : Not (xs = [])}
          -> {ys : List a} -> {eqCons : y :: ys = xs}
          -> QueueEq a xs -> QueueEq a ys
dequeueEq {neq = neq} QNilEq = void (neq Refl)
dequeueEq (QConsEq [] ys {neq = neq}) = void (neq Refl)
dequeueEq {eqCons = Refl} (QConsEq (x :: xs) ys) = queueEq xs ys

{- Representaion with with two constructor, where the second constructor
    explicitely constructs a non-empty list as first argument of the queue
-}
data QueueC : (a : Type) -> List a -> Type where
   QNilC : QueueC a []
   QConsC : (x : a) -> (xs, ys : List a) -> QueueC a (x :: (xs ++ reverse ys))

total emptyQueueC : QueueC a []
emptyQueueC = QNilC

total isEmptyQueueC : QueueC a xs -> Bool
isEmptyQueueC QNilC = True
isEmptyQueueC (QConsC _ _ _) = False

total queueC : (xs : List a) -> (ys : List a) -> QueueC a (xs ++ reverse ys)
queueC [] [] = QNilC
queueC [] (y :: ys) with (reverse (y :: ys))
  queueC [] (y :: ys) | [] = QNilC
  queueC [] (y :: ys) | (z :: zs) =  rewrite sym (appendNilRightNeutral zs) in QConsC z zs []
queueC (x :: xs) ys = QConsC x xs ys

total enqueueC : (x : a) -> QueueC a xs -> QueueC a (x :: xs)
enqueueC x QNilC = QConsC x [] []
enqueueC x (QConsC z xs ys) = QConsC x (z :: xs) ys

total nextQueueC : QueueC a (x :: xs) -> a
nextQueueC (QConsC x xs ys) = x

total  dequeueC : QueueC a (x :: xs) -> QueueC a xs
dequeueC (QConsC x [] []) = QNilC
dequeueC (QConsC x xs ys) = queueC xs ys 

total nextQueueC' : {neq : Not (xs = [])} -> QueueC a xs -> a
nextQueueC' {neq = neq} QNilC = void (neq Refl)
nextQueueC' (QConsC x xs ys) = x

total dequeueC' : {neq : Not (xs = [])} -> {eqCons : y :: ys = xs}
                -> QueueC a xs -> QueueC a ys
dequeueC' {neq = neq} QNilC = void (neq Refl)
dequeueC' {eqCons = Refl} (QConsC x xs ys) = queueC xs ys
