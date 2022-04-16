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

_+_ : ℕ → ℕ → ℕ
zero + b = b
succ a + b = succ (a + b)


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


forget : {n : ℕ} → Fin n → ℕ
forget fzero = succ zero
forget (fsucc fi) = succ (forget fi)

-- There are several ways to embed Fin n in Fin (Succ n).  Try to come
-- up with one that satisfies the correctness property below (and
-- prove that it does).
embed : {n : ℕ} → Fin n → Fin (succ n)
embed fzero = fzero
embed {n} (fsucc fi) = fsucc (embed fi)


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

data Tree (S : Set) (P : S → ℕ) : Set where
    Node : (s : S) → (Fin (P s) → Tree S P) → Tree S P


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
    Define a function __ListP : ListS → ℕ__, such that
    __Tree ListS ListC__ is isomorphic to __List ℕ__

        data List (a : Set) : Set where
            nil : List a
            cons : a → List a → List a
-}

ListP : ListS → ℕ
ListP Nil = 1
ListP (Cons zero) = 2
ListP (Cons (succ x)) = succ (ListP (Cons x))

-- to define the constructors we need a 
-- Fin (P Nil) → Tree ListS P
tlookup : {S : Set} {P : S → ℕ } {s : S} {t : Tree S P} → Fin (P s) → Tree S P
tlookup {S} {P} {s} {Node s₁ f} with P s
-- we have arrived
... | zero = λ _ → Node s₁ f
... | succ n = {! finToTree {S} {P} {s₁}  !}

-- tlookup : {S : Set} {P : S → ℕ} → ∀ {s : S}
--     → Tree S P → Fin (P s) → Tree S P
-- tlookup {S} {P} {s} (Node s₁ x) f = {!   !}

dec : (n : ℕ) {f : Fin n} → ℕ
dec (succ n) = n

-- Also define the constructor functions:
nil : {P : ListS → ℕ } {s : ListS} {t : Tree ListS P} → Tree ListS P
nil {P} {s} {Node s₁ f} with P s
nil {P} {s} {Node Nil f} | zero = Node Nil f
nil {P} {s} {Node (Cons zero) f} | zero 
    = Node Nil λ x → f {! embed   !}
nil {P} {s} {Node (Cons (succ x)) f} | zero 
    = nil {P} {s} {Node {!   !} {!   !}}
... | succ n = {!   !}
--tlookup {ListS} {P} {s} {t} {! fzero {P s}  !}

cons : {P : ListS → ℕ } → ℕ → Tree ListS P → Tree ListS P
cons x xs = {!   !}

----------------------
-------- (b) ---------
----------------------

{-  (2 points)
    Define a __TreeS__ and __TreeP__ such that __Tree TreeS TreeP__
    is isomorphic to the following tree type:

        data Tree : Set where
            Node : Tree → Tree → Tree
            Leaf : ℕ → Tree
-}

data TreeS : Set where
    -- this constructor might have one parameter more than it should
    -- judging from ListS
    -- see TestExer for examples
    Node : TreeS → TreeS → TreeS
    Leaf : ℕ → TreeS

-- For every shape s : S , there are P s recursive subtrees
TreeP : TreeS → ℕ
TreeP (Node ts ts₁) = TreeP ts + TreeP ts₁
TreeP (Leaf x) = 1

 -- how do you check isomorphism?



----------------------
-------- (c) ---------
----------------------

{- (4 points)
    Write a generic size function that counts the number of
    __Node__ constructors in its argument:
        gsize : Tree S P → ℕ
    You may find it helpful to define an auxiliary function of
    the following type:
        sumFin : (n : ℕ) → (Fin n → ℕ) → ℕ
    Such that __sumFin n f__ sums all the natural numbers in the 
    image of __f__
-}

-- it seems to work but I don't know why it needs
-- this useless implicit argument
-- other than for ruling out the n ≡ 0 case
craftFin : (n : ℕ) {f : Fin n} → Fin n
craftFin (succ zero) = fzero
craftFin (succ (succ n)) {f} = fsucc (craftFin (succ n) {fzero})

-- sums all the natural numbers in the image of f
sumFin : (n : ℕ) → (Fin n → ℕ) → ℕ
sumFin zero f = 0
sumFin (succ n) f = f (craftFin (succ n) {fzero}) 
    -- + sumFin n λ x → f (embed x)

gsize : {S : Set} {P : S → ℕ} → Tree S P → ℕ
gsize {S} {P} (Node s f) = sumFin (P s) forget
