{-# OPTIONS --type-in-type #-}


infixl 4 _,_
record Σ (A : Set) (B : A -> Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B fst
open Σ

syntax Σ A (λ a → B) = [ a ∈ A ]×[ B ]

Pair : Set -> Set -> Set
Pair A B = [ _ ∈ A ]×[ B ]

data Nat : Set where
  zero : Nat
  succ : Nat -> Nat

data Fin : (n : Nat) -> Set where
  Fzero : Fin (succ zero)
  Fsucc : (n : Nat) -> Fin n -> Fin (succ n)

Void : Set
Void = Fin zero

One : Set
One = Fin (succ zero)

Two : Set
Two = Fin (succ (succ (zero)))

data Either (A : Set) (B : Set) : Set where
  Left  : A -> Either A B
  Right : B -> Either A B

record Interface : Set where
   field           
     pos : Set
     dis : pos -> Set
open Interface

yon : Set -> Interface
pos (yon A) = One
dis (yon A) FZero = A

constant : Set -> Interface
pos (constant x) = x
dis (constant x) _ = Void

infixl 4 _+_
_+_ : Interface -> Interface -> Interface
pos (i + j) = Either (pos i) (pos j)
dis (i + j) (Left x) = dis i x
dis (i + j) (Right x) = dis j x

infixl 5 _×_
_×_ : Interface -> Interface -> Interface
pos (i × j) = Pair (pos i) (pos j)
dis (i × j) (x , y) = Pair (dis i x) (dis j y)

toFunctor : Interface -> Set -> Set
toFunctor i x = [ p ∈ pos i ]×[ (dis i p -> x) ]

myInterface : Interface
myInterface = (yon Two) + (constant Two) × (yon One) + (constant One)

record Lens (i : Interface) (j : Interface) : Set where
   field 
     passfwd : (pos i) -> (pos j)
     passbck : (p : pos i) -> dis j (passfwd p) -> dis i p


module _ (I : Set) (J : I → Set) (X : (i : I) (j : J i) -> Set) where
  to : ((i : I) -> [ j ∈ J i ]×[ X i j ])
     → [ f ∈ ((i : I) → J i) ]×[ ((i : I) → X i (f i)) ]
  to C = ((λ i → fst (C i))) , (λ i → snd (C i))

  fro : [ f ∈ ((i : I) → J i) ]×[ ((i : I) → X i (f i)) ]
      → ((i : I) -> [ j ∈ J i ]×[ X i j ])
  fro (f , c) = λ i → (f i , c i)

