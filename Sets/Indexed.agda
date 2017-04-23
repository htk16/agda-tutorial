module Sets.Indexed where

open import Data.Empty    using (⊥)
open import Data.Unit     using (⊤; tt)
open import Data.Sum      using (_⊎_; inj₁; inj₂)
open import Data.Bool     using (Bool; true; false)
open import Data.Nat      using (ℕ; zero; suc)



data Fin : ℕ -> Set where
  zero : (n : ℕ) -> Fin (suc n)
  suc  : (n : ℕ) -> Fin n -> Fin (suc n)


-- Ex. Define Bool indexed family of sets such that the set indexed by false
--     contains no elements and the set indexed by true contains one element!
data Fin2 : Bool -> Set where
  zero : Fin2 true

fin2_zero : Fin2 true
fin2_zero = zero


-- Ex. Define a ℕ indexed family of sets such that the sets indexed
--     by even numbers contain one element and the others are empty
data Fin3 : ℕ -> Set where
  zero : Fin3 zero
  suc  : (n : ℕ) -> Fin3 n -> Fin3 (suc (suc n))


fin3_zero : Fin3 0
fin3_zero = zero

fin3_zero2 : Fin3 2
fin3_zero2 = suc 0 zero


data Vec (A : Set) : ℕ -> Set where
  []  : Vec A zero
  cons : (n : ℕ) -> A -> Vec A n -> Vec A (suc n)


-- Ex. Define a Bool indexed family of sets with two parameters, A and B,
--     such that the set indexed by false contains an A element
--     and the set indexed by true contains a B element!
data Either (A B : Set) : Bool -> Set where
  left  : A -> Either A B false
  right : B -> Either A B true
