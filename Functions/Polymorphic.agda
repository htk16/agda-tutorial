module Functions.Polymorphic where

open import Data.Nat
open import Data.Unit using (⊤; tt)


-- Definition of List
data List (A : Set) : Set where
 [] : List A
 _∷_ : A -> List A -> List A

infixr 5 _∷_


_++_ : {A : Set} -> List A -> List A -> List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

infixr 5 _++_


-- Ex. Define two functions which define the isomorphism between List ⊤ and ℕ!
fromList : List ⊤ -> ℕ
fromList []       = zero
fromList (x ∷ xs) = suc (fromList xs)

toList : ℕ -> List ⊤
toList zero    = []
toList (suc n) = tt ∷ (toList n)

-- Ex. Show on a sheet of paper with equational reasoning that 
--     the fromList function is a bijection and it preserves the _+_ and _++_ operations
--     (that is, ∀ a, b ∈ List ⊤ . fromList (a ++ b) = fromList a + fromList b).

-- when a = []
--   fromList (a ++ b)
-- = fromList ([] ++ b)
-- = fromList b
-- = zero + fromList b
-- = fromList [] + fromList b
-- = formList a + fromList b
-- when fromList(n ++ b) = fromList n + fromList b,
--   fromList (tt ∷ n) + fromList b
-- = suc (fromList n) + fromList b
-- = suc (fromList n + fromList b)
-- = suc (fromList (n ++ b))
-- = fromList (tt ∷ (n ++ b))
-- = fromList ((tt ∷ n) ++ b)

-- Ex. Define a Maybe set (lists with 0 or 1 elements) and head and tail functions 
--     for the polymorphic List type with the help of Maybe.
data Maybe (A : Set) : Set where
  some : A -> Maybe A
  none : Maybe A

head : {A : Set} -> List A -> Maybe A
head [] = none
head (x ∷ _) = some x

tail : {A : Set} -> List A -> Maybe (List A)
tail [] = none
tail (_ ∷ xs) = some xs


-- Ex. Define the following functions on lists:
map : {A B : Set} -> (A -> B) -> List A -> List B
map _ []       = []
map f (x ∷ xs) = (f x) ∷ (map f xs)

maps : {A B : Set} -> List (A -> B) -> List A -> List B
maps _ [] = []
maps [] _ = []
maps (f ∷ fs) (x ∷ xs) = (f x) ∷ (maps fs xs)

[_] : {A : Set} -> A -> List A
[ x ] = x ∷ []


-- Plolymorphic id function
id : {A : Set} -> A -> A
id a = a

-- Ex. Define const : {A B : Set} -> A -> B -> A!
const : {A B : Set} -> A -> B -> A
const x _ = x

-- Ex. Define flip : {A B C : Set} -> (A -> B -> C) -> B -> A -> C!
flip : {A B C : Set} -> (A -> B -> C) -> B -> A -> C
flip f b a = f a b


-- _×_ : Cartesian Product
data _×_ (A B : Set) : Set where
  _,_ : A -> B -> A × B

infixr 4 _,_
infixr 2 _×_

-- Ex. Define a function which swaps the two elements
swap : {A B : Set} -> A × B -> B × A
swap (a , b) = b , a

-- Ex. Define the following functions:
proj₁ : {A B : Set} → A × B → A
proj₁ (a , b) = a


-- _⊎_: Disjoint Union (Sum)
data _⊎_ (A B : Set) : Set where
  inj₁ : A -> A ⊎ B
  inj₂ : B -> A ⊎ B

infixr 1 _⊎_

-- Ex. Define a function which swaps the two elements!
swap' : {A B : Set} -> A ⊎ B -> B ⊎ A
swap' (inj₁ a) = inj₂ a
swap' (inj₂ b) = inj₁ b
 
-- Ex. Define the eliminator function for disjoint union:
union : {A B C : Set} -> (A -> C) -> (B -> C) -> A ⊎ B -> C
union f _ (inj₁ a) = f a
union _ g (inj₂ b) = g b

[_,_] : {A B C : Set} → (A → C) → (B → C) → (A ⊎ B → C)
[ f , g ] = union f g
