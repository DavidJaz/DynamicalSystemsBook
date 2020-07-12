{-# OPTIONS --type-in-type #-}


infixl 4 _,_
record Σ (A : Set) (B : A -> Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B fst

syntax Σ A (λ a → B) = [ a ∈ A ]×[ B ]

Pair : Set -> Set -> Set
Pair A B = [ _ ∈ A ]×[ B ]

data Void : Set where


data Unit : Set where
  ⊤ : Unit

record Interface : Set where
   field
     pos : Set
     dis : pos -> Set
open Interface

data Either (A : Set) (B : Set) : Set where
  Left  : A -> Either A B
  Right : B -> Either A B



_+_ : Interface -> Interface -> Interface
pos (i + j) = Either (pos i) (pos j)
dis (i + j) (Left x) = dis i x
dis (i + j) (Right x) = dis j x

_×_ : Interface -> Interface -> Interface
pos (i × j) = Pair (pos i) (pos j)
dis (i × j) (x , y) = Pair (dis i x) (dis j y)

constant : Set -> Interface
pos (constant x) = x
dis (constant x) _ = Void

toFunctor : Interface -> Set -> Set
toFunctor i x = [ p ∈ pos i ]×[ (dis i p -> x) ]

