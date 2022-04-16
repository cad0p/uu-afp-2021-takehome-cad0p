{-# OPTIONS --allow-unsolved-metas #-}


module Exercise where

------------------------
-- RequiredStructures --
------------------------

data Bool : Set where
    true  : Bool
    false : Bool

data ℕ : Set where
    zero : ℕ
    succ : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

data Fin : ℕ → Set where
  fzero : ∀ {n} → Fin (succ n)
  fsucc : ∀ {n} → Fin n → Fin (succ n)


data _≡_ {a : Set} (x : a) : a → Set where
  refl : x ≡ x
{-# BUILTIN EQUALITY _≡_ #-}

cong : {a b : Set} {x y : a} → (f : a → b) → x ≡ y → f x ≡ f y
cong f refl = refl

-- data Unit : Set where
--   unit : Unit
record Unit : Set where
  constructor unit

data Empty : Set where


----------------------
------- Intro --------
----------------------

{-
    In the course of the lectures, 
    we saw how to define a universe for generic programming
    closed under products (pairs), coproducts (__Either__),
    and constant types. To do so, we defined a data type to
    represent the types in the universe U, and a function
    mapping elements of U to the pattern functor they represent.
        
        data U : Set where
            _⊕_ : U → U → U
            _⊗_ : U → U → U
             I  : U
            ...
        elU : U → Set → Set
        ... 
-}

{-
    In this question, we will explore an alternative
    representation of such types, namely as __finitely
    branching trees__. 
    We will begin by defining the following data type:
-}

data Tree (S : Set) (C : S → ℕ) : Set where
    Node : (s : S) → (Fin (C s) → Tree S C) → Tree S C


----------------------
-------- (a) ---------
----------------------

{-  (2 points)
    We will begin by modelling lists of natural numbers as Tree-types.
    Given the following data type:
-}

data ListS : Set where
    Nil : ListS
    Cons : ℕ → ListS

{-
    Define a function __ListC : ListS → ℕ__, such that
    __Tree ListS ListC__ is isomorphic to __List ℕ__

        data List (a : Set) : Set where
            nil : List a
            cons : a → List a → List a
-}

ListC : ListS → ℕ
ListC Nil = 0
ListC (Cons zero) = 1
ListC (Cons (succ x)) = succ (ListC (Cons x))

-- Also define the constructor functions:
nil : {C : ListS → ℕ } → Tree ListS C
nil = Node Nil {!   !}




{-
    to the following tree type:

        data Tree : Set where
            Node : Tree → Tree → Tree
            Leaf : ℕ → Tree
-}

