{-
  Reimplementation of a double-ended queue (as presented by Okasaki)
   with different explicit encodings of the invariant
-}
open import Data.List
open import Data.Bool
open import Relation.Nullary
open import Agda.Builtin.Equality

postulate
  UNDEFINED : ∀ {ℓ} → {T : Set ℓ} → T

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

data QueueS (a : Set) : Set where
  AQueue : (xs ys : List a) -> QueueS a

emptyQS : {a : Set} -> QueueS a
emptyQS = AQueue [] []

isEmptyQS : {a : Set} -> QueueS a -> Bool
isEmptyQS (AQueue xs _) = null xs

queueS : {a : Set} -> List a -> List a -> QueueS a
queueS [] ys = AQueue (reverse ys) []
queueS (x ∷ xs) ys = AQueue xs ys

enqueueS : {a : Set} -> a -> QueueS a -> QueueS a
enqueueS x (AQueue xs ys) = queueS xs (x ∷ ys)

{- Cannot define partial functions next ... -}
next : {a : Set} -> QueueS a -> a
next (AQueue [] _) = UNDEFINED
next (AQueue (x ∷ _) _) = x

{- ... and dequeue -}
dequeue : {a : Set} -> QueueS a -> QueueS a
dequeue (AQueue [] ys) = UNDEFINED
dequeue (AQueue (_ ∷ xs) ys) = queueS xs ys


{- Representation with two constructors and explicit
    proof about non-empty first list argument for the
    second constructor
-}
data Queue (a : Set) : List a -> List a -> Set where
   QNil : Queue a [] []
   Q : forall (xs ys : List a) -> (¬ (xs ≡ [])) -> Queue a xs ys

emptyQueue : {a : Set} -> Queue a [] []
emptyQueue = QNil

isEmptyQueue : {a : Set} {xs ys : List a} -> Queue a xs ys -> Bool
isEmptyQueue QNil = true
isEmptyQueue (Q _ _ _) = false

data QueueN (a : Set) : List a -> Set where
   QEmpty : QueueN a []
   QCons : forall (xs ys : List a) -> (¬ (xs ≡ [])) -> QueueN a (xs ++ reverse ys)

emptyQueueN : {a : Set} -> QueueN a []
emptyQueueN = QEmpty

isEmptyQueueN : {a : Set} {xs : List a} -> QueueN a xs -> Bool
isEmptyQueueN QEmpty = true
isEmptyQueueN (QCons _ _ _) = false

sym : {A : Set} {a b : A} → a ≡ b → b ≡ a
sym refl = refl
  
append-nil : {a : Set} (as : List a) → as ++ [] ≡ as
append-nil [] = refl
append-nil (a ∷ as) rewrite append-nil as = refl

queueN : {a : Set} -> (xs : List a) -> (ys : List a) -> QueueN a (xs ++ reverse ys)
queueN [] [] = QEmpty
queueN [] (y ∷ ys) with reverse (y ∷ ys)
queueN [] (y ∷ ys) | [] = QEmpty
queueN [] (y ∷ ys) | z ∷ zs rewrite sym (append-nil (z ∷ zs)) = QCons (z ∷ zs) [] λ { ()}
queueN (x ∷ xs) ys = QCons (x ∷ xs) ys (λ {()})

{- We do acutally need to pattern match on `reverse (y :: ys)` in order to know that the
    resulting term cannot be empty

     "I'm not sure if there should be a case for the constructor refl,
      because I get stuck when trying to solve the following unification
      problems (inferred index ≟ expected index):
      reverse (y₁ ∷ ys₁) ≟ []
      when checking that the expression ? has type .Data.Empty.⊥"
-}
queueN' : {a : Set} -> (xs : List a) -> (ys : List a) -> QueueN a (xs ++ reverse ys) -- QCons (reverse ys) [] (reverse ys /= [])
queueN' [] [] = QEmpty
queueN' [] (y ∷ ys) rewrite sym (append-nil (reverse (y ∷ ys))) = QCons (reverse (y ∷ ys)) [] λ {x → UNDEFINED}
queueN' (x ∷ xs) ys = QCons (x ∷ xs) ys (λ {()})

enqueueN : {a : Set} {xs : List a} (x : a) -> QueueN a xs -> QueueN a (x ∷ xs)
enqueueN x QEmpty = QCons (x ∷ []) [] \ {()}
enqueueN x (QCons xs ys xsNotNil) = QCons (x ∷ xs) ys \ {()}

nextN : {a : Set} {xs : List a} {neq : ¬ (xs ≡ [])} -> QueueN a xs -> a
nextN {neq = neq} QEmpty with neq refl
nextN {neq = neq} QEmpty | ()
nextN (QCons [] ys neq) with neq refl
nextN (QCons [] ys neq) | ()
nextN (QCons (x ∷ xs) ys neq) = x

{- {- Here, the used encoding is not usable, since the type-checker
       does not know, if the constructor is even possible --
       the same actually holds for the analogues definition of `nextN`
-}
dequeueN' : {a : Set} {x : a} {xs : List a} -> QueueN a (x ∷ xs) -> QueueN a xs
dequeueN' (QCons xs ys neq) = ?

nextN' : {a : Set} {x : a} {xs : List a} -> QueueN a (x ∷ xs) -> a
nextN' (QCons xs ys neq) = ?
-}

dequeueN : {a : Set} {xs : List a} {neq : ¬ (xs ≡ [])} {ys : List a} {aCons : (y : a) -> y ∷ ys ≡ xs} -> QueueN a xs -> QueueN a ys
dequeueN {neq = neq} QEmpty with neq refl
dequeueN {neq = neq} QEmpty | ()
dequeueN (QCons [] ys neq) with neq refl
dequeueN (QCons [] ys neq) | ()
dequeueN {aCons = aCons} (QCons (x ∷ xs) ys neq) with aCons x
dequeueN {aCons = aCons} (QCons (x ∷ xs) ys neq) | refl = queueN xs ys


{- Representaion with with two constructor, where the second constructor
    explicitely constructs a non-empty list as first argument of the queue
-}
data Que (a : Set) : List a -> Set where
   QE : Que a []
   QNE : forall (x : a) (xs ys : List a) -> Que a (x ∷ (xs ++ reverse ys))

emptyQue : {a : Set} -> Que a []
emptyQue = QE

isEmptyQue : {a : Set} {xs : List a} -> Que a xs -> Bool
isEmptyQue QE = true
isEmptyQue (QNE _ _ _) = false

que : {a : Set} -> (xs : List a) -> (ys : List a) -> Que a (xs ++ reverse ys)
que [] [] = QE
que [] (y ∷ ys) with reverse (y ∷ ys)
que [] (y ∷ ys) | [] = QE
que [] (y ∷ ys) | z ∷ zs rewrite sym (append-nil zs) = QNE z zs []
que (x ∷ xs) ys = QNE x xs ys

enque : {a : Set} {xs : List a} (x : a) -> Que a xs -> Que a (x ∷ xs)
enque x QE = QNE x [] []
enque x (QNE z xs ys) = QNE x (z ∷ xs) ys

nextQue : {a : Set} {xs : List a} {neq : ¬ (xs ≡ [])} -> Que a xs -> a
nextQue {neq = neq } QE with neq refl
nextQue {neq = neq} QE | ()
nextQue (QNE x xs ys) = x

deque : {a : Set} {x : a} {xs : List a} -> Que a (x ∷ xs) -> Que a xs
deque (QNE x [] []) = QE
deque (QNE x xs ys) = que xs ys 
