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
ListP Nil = 0
-- it's got one subtree (no choice but continue with the list)
ListP (Cons n) = 1

TList = Tree ListS ListP

ListEnd : Fin (ListP Nil) → TList
ListEnd ()

-- this below was the old wrong approach

-- to define the constructors we need a 
-- Fin (P Nil) → Tree ListS P
-- tlookup : {S : Set} {P : S → ℕ } {s : S} {t : Tree S P} 
--     → Fin (P s) → Tree S P
-- tlookup {S} {P} {s} {Node s₁ f} with P s
-- -- we have arrived
-- ... | zero = λ _ → Node s₁ f
-- ... | succ n = {! finToTree {S} {P} {s₁}  !}

-- -- tlookup : {S : Set} {P : S → ℕ} → ∀ {s : S}
-- --     → Tree S P → Fin (P s) → Tree S P
-- -- tlookup {S} {P} {s} (Node s₁ x) f = {!   !}

-- dec : (n : ℕ) {f : Fin n} → ℕ
-- dec (succ n) = n

-- Also define the constructor functions:
-- nil : {P : ListS → ℕ } {s : ListS} {t : Tree ListS P} → Tree ListS P
-- nil {P} {s} {Node s₁ f} with P s
-- nil {P} {s} {Node Nil f} | zero = Node Nil f
-- nil {P} {s} {Node (Cons zero) f} | zero 
--     = Node Nil λ x → f {! embed   !}
-- nil {P} {s} {Node (Cons (succ x)) f} | zero 
--     = nil {P} {s} {Node {!   !} {!   !}}
-- ... | succ n = {!   !}
-- --tlookup {ListS} {P} {s} {t} {! fzero {P s}  !}



-- better approach
nil : TList
nil = Node Nil ListEnd

cons : ℕ → TList → TList
cons n t = Node (Cons n) (λ x → t)

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
    -- Node : TreeS → TreeS → TreeS

    Node : TreeS
    -- this also represents the actual value of the leaf
    Leaf : ℕ → TreeS

-- For every shape s : S , there are P s recursive subtrees
TreeP : TreeS → ℕ
TreeP (Leaf x) = 0
-- there are 2 recursive subtrees (left subtree and right subtree)
TreeP Node = 2

TTree = Tree TreeS TreeP

 -- how do you check isomorphism?
 -- answer: by creating constructors that look the same,
 -- just like for List (nil and cons)

TreeEnd : {x : ℕ} → Fin (TreeP (Leaf x)) → TTree
TreeEnd ()

TreeNodeSubTrees : TTree → TTree → Fin 2 → TTree
TreeNodeSubTrees l r fzero = l
TreeNodeSubTrees l r (fsucc f) = r

-- new attempt here very neat!

leaf : ℕ → TTree
leaf x = Node (Leaf x) (TreeEnd {x})


node : TTree → TTree → TTree
node l r = Node Node (TreeNodeSubTrees l r)

-- old attempt below:

-- now the node has a natural parameter 
-- that represents the order of the node 
-- since they are ordered according 
-- to pre-order traversal

-- node : {i : ℕ} → TTree → TTree → TTree
-- node {i} (Node (Leaf iₗ xₗ) x) r = Node (Node i) (λ x → {!   !})
-- node {i} (Node (Node iₗ) sₗ) r = Node (Node i) (λ x → {!   !})



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

-- craftFin is really useful, I used it in the final version

-- it seems to work but I don't know why it needs
-- this useless implicit argument
-- other than for ruling out the n ≡ 0 case
craftFin : (n : ℕ) {f : Fin n} → Fin n
craftFin (succ zero) = fzero
craftFin (succ (succ n)) = fsucc (craftFin (succ n) {fzero})


-- old approach, was just a hack..


-- sums all the natural numbers in the image of f
sumFin : (n : ℕ) → (Fin n → ℕ) → ℕ
sumFin zero f = 0
sumFin (succ n) f = f (craftFin (succ n) {fzero}) 
    + sumFin n λ x → f (embed x)

-- I think I need a function from TTree to ℕ
-- convertForSum : {S : Set} {P : S → ℕ} 

-- gsize : {S : Set} {P : S → ℕ} → Tree S P → ℕ
-- gsize {S} {P} (Node s f) = sumFin (P s) λ _ → P s


-- new approach:

{-# TERMINATING #-}
mutual
    -- i need some list comprehension here, will define here:
    gsubsize : (S : Set) (P : S → ℕ) → (n : ℕ)
        → (Fin n → Tree S P) → ℕ
    gsubsize S P zero f = zero
    gsubsize S P (succ n) f = gsize {S} {P} (f (craftFin (succ n) {fzero})) 
        + gsubsize S P n λ x → f (embed x)

    gsize : {S : Set} {P : S → ℕ} → Tree S P → ℕ
    gsize {S} {P} (Node s f) with P s
    -- an example of this case is nil = Node Nil ListEnd
    -- or leaf x = Node (Leaf x) (TreeEnd {x})
    ... | zero = 1
    -- simple example: cons nil is a Node Node (see tests), so gsize ≡ 2
    -- cons has P s ≡ 1, and nil has P s ≡ 0
    ... | succ n = succ n + gsubsize S P (succ n) f 
    -- + gsize {S} {P} (f (craftFin {! n  !}))
    -- this is what subsize does! for all the inhabitants of Fin n


----------------------
-------- (d) ---------
----------------------

{- (4 points)
    Let M : Set be a monoid, that is, we have a zero element z : M
    and `addition` operation _+M_ : M → M → M . 
    Define an analogue of Haskell's foldMap function on finitely 
    branching trees:

        foldMap : (S → M) → Tree S P → M
-}

data M : Set where
    z : M
    _+M_ : M → M → M


{-# TERMINATING #-}
mutual
    -- another list comprehension..
    -- i don't know, maybe this pattern could be generalized
    -- in a more general helper
    foldSubMap : (S : Set) (P : S → ℕ) → (S → M) → (n : ℕ)
        → (Fin n → Tree S P) → M
    foldSubMap S P f zero sub = z
    foldSubMap S P f (succ n) sub = 
        (foldMap {S} {P} f (sub (craftFin (succ n) {fzero}))) 
        +M foldSubMap S P f n (λ x → sub (embed x))

    foldMap : {S : Set} {P : S → ℕ} → (S → M) → Tree S P → M
    foldMap {S} {P} f (Node s sub) with P s
    ... | zero = f s
    ... | succ n = f s +M foldSubMap S P f (succ n) sub
        -- +M foldMap f (x {! fzero {P s}  !})



----------------------
-------- (e) ---------
----------------------


{- (5 points)
    Show that Tree types are closed under coproducts. 
    That is, define operations:
        
        _⊕ₛ_ : (S : Set) → (S₁ : Set) → Set
        _⊕ₚ_ : (P : S → ℕ) → (P₁ : S₁ → ℕ) → (S ⊕ₛ S₁ → ℕ)
        inl : Tree S P → Tree (S ⊕ₛ S₁) (P ⊕ₚ P₁)
        inr : Tree S₁ P₁ → Tree (S ⊕ₛ S₁) (P ⊕ₚ P₁)

-}

-- postulate
--   Level : Set

-- -- MAlonzo compiles Level to (). This should be safe, because it is
-- -- not possible to pattern match on levels.

-- {-# BUILTIN LEVEL Level #-}

-- postulate
--   lzero : Level
--   lsuc  : (n : Level) → Level
--   _⊔_   : (n m : Level) → Level

-- {-# BUILTIN LEVELZERO lzero #-}
-- {-# BUILTIN LEVELSUC  lsuc  #-}
-- {-# BUILTIN LEVELMAX  _⊔_   #-}

open import Agda.Primitive using (Level; _⊔_)

-- data _×_ {n m : Level} (A : Set n) (B : Set m) : Set (n ⊔ m)  where
--   _,_ : A → B → A × B

-- infixr 4 _,_
-- infixr 2 _×_


-- data _⊎_ (A : Set) (B : Set) : Set where
--   inj₁ : (x : A) → A ⊎ B
--   inj₂ : (y : B) → A ⊎ B
-- infixr 1 _⊎_


-- Set₁ != Set error
-- Set × Set should be a sort, but it isn't
-- _⊕ₛ_ : (S : Set) → (S₁ : Set) → Set × Set
-- S ⊕ₛ S₁ = S , S₁

_⊕ₛ_ : (S : Set) → (S₁ : Set) → Set
S ⊕ₛ S₁ = S

_⊕ₚ_ : {S S₁ : Set} → (P : S → ℕ) → (P₁ : S₁ → ℕ) → ((S ⊕ₛ S₁) → ℕ)
_⊕ₚ_  {S} {S₁} P  P₁ = {! λ (S ⊕ₛ S₁) → (P S) + (P₁ S₁) - elements in common   !}


-- elemToSets : {S S₁ : Set} 

inl : {S S₁ : Set} {P : S → ℕ} {P₁ : S₁ → ℕ} 
    → Tree S P → Tree (S ⊕ₛ S₁) (P ⊕ₚ P₁)
inl (Node s x) = Node {! an element of S in common with S₁  !} {!  !}



inr : {S S₁ : Set} {P : S → ℕ} {P₁ : S₁ → ℕ} 
    → Tree S₁ P₁ → Tree (S ⊕ₛ S₁) (P ⊕ₚ P₁)
inr (Node s x) = Node {! an element of S₁ in common with S  !} {!   !}




----------------------
-------- (f) ---------
----------------------


{- (5 points)
    Given a choice of S : Set and P : S → ℕ, we can compute the 
    pattern functor corresponding to Tree S P as follows:

        data DPair (S : Set) (B : S → Set) : Set where
            _,_ : (s : S) → B s → DPair S B
        toPF : (S : Set) → (P : S → ℕ) → Set → Set
        toPF S P a = DPair S (λ s → Fin (P s) → a)
-}

data DPair (S : Set) (B : S → Set) : Set where
    _,_ : (s : S) → B s → DPair S B

toPF : (S : Set) → (P : S → ℕ) → Set → Set
toPF S P a = DPair S (λ s → Fin (P s) → a)


-- since the previous definitions don't work,
-- there's no point trying to prove them
 