module Sets.Parametric where

open import Data.Nat

-- Type generic list
data List (A : Set) : Set where
  []   : List A
  _::_ : A -> List A -> List A

infixr 5 _::_


-- Ex. What is the connection between List ⊤ and Nat

-- Ex. Define a Maybe set (lists with 0 or 1 elements)!
data Maybe (A : Set) : Set where
  none : Maybe A
  some : A -> Maybe A

-- Ex. Define a parametric trees (various sorts)!
data Tree (A : Set) : Set where
  leaf : Tree A
  node : Tree A -> Tree A -> Tree A


-- Cartesian product
data _×_ (A B : Set) : Set where
  _,_ : A -> B -> A × B

infixr 4 _,_
infixr 2 _×_


-- Ex. How many elements are there in
-- ⊤ × ⊤ = { (tt, tt) }
-- ⊤ × ⊥ = { }
-- ⊥ × ⊤ = { }
-- ⊥ × ⊥ = { }

-- Ex. How should we define Top so that ∀ A : Set.
--     Top × A would be isomorphic to A (neutral element of _×_)
data Top : Set where
  t : Top


-- Disjoin union
data _⨄_ (A B : Set) : Set where
  inj₁ : A -> A ⨄ B
  inj₂ : B -> A ⨄ B


-- Ex. What are the elements of Bool ⨄ ⊤ ?
-- Bool* = { (true, 0), (false, 0) }
-- ⊤* = { (tt, 1) }
-- Bool ⨄ ⊤ = Bool* ∪ ⊤* = { (true, 0), (false, 0), (tt, 1) }

-- Ex. What are the elements of ⊤ ⨄ ( ⊤ ⨄ ⊤ )
-- ⊤ ⨄ ⊤ = { (tt, 0), (tt, 1) }
-- ⊤ ⨄ ( ⊤ ⨄ ⊤ ) = { (tt, 0), ((tt, 0), 1), ((tt, 1), 1) }

-- Ex. Name an already learned isomorphic type to ⊤ ⨄ ⊤
-- Bool

-- Ex. How should we define Bootom so that ∀ A: set.
--     Bottom ⨄ A would be isomorphic to A (Neutral element of _⨄_)?
-- Bottom = ⊥ = {}

-- Ex. Give an isomorpihic definition of Maybe A with the help of _⨄_ and ⊤!
-- maybe (A : Set) = A ⨄ ⊤


-- Ex. list the smallest first 5 elements of List₁ ⊤ Bool!
-- [] , true :: [] , tt :: true :: [] , true :: tt :: true :: [] , tt :: true :: tt :: true :: []


-- Mutually recursive sets
data List₁ (A B : Set) : Set
data List₂ (A B : Set) : Set

data List₁ (A B : Set) where
  []   : List₁ A B
  _::_ : A -> List₂ A B -> List₁ A B

data List₂ (A B : Set) where
  _::_ : B -> List₁ A B -> List₂ A B

data AlterList (A B : Set) : Set where
  []   : AlterList A B
  _::_ : A -> AlterList B A -> AlterList A B


-- Nested sets
data T4 (A : Set) : Set where
  quad : A -> A -> A -> A -> T4 A

data Square (A : Set) : Set where
  zero : A -> Square A
  suc  : Square (T4 A) -> Square A
