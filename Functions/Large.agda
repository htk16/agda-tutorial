module Functions.Large where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)


-- Inductive _≤_ definition
data _≤_ : ℕ -> ℕ -> Set where
  z≤n : {n : ℕ} -> zero ≤ n
  s≤s : {m n : ℕ} -> m ≤ n -> suc m ≤ suc n


-- Recursive _≤_ definition
_≤'_ : ℕ -> ℕ -> Set
zero  ≤' n = ⊤
suc m ≤' zero = ⊥
suc m ≤' suc n = m ≤' n


-- Ex. Give recursive definitions for _≡_ and _≇_ on natural numbers!
_≡_ : ℕ -> ℕ -> Set
zero ≡ zero = ⊤
zero ≡ (suc _) = ⊥
(suc _) ≡ zero = ⊥
(suc m) ≡ (suc n) = m ≡ n

_≢_ : ℕ -> ℕ -> Set
zero ≢ (suc _) = ⊤
(suc _) ≢ zero = ⊤
zero ≢ zero = ⊥
(suc m) ≢ (suc n) = m ≢ n


-- Macro-like Set definitions
_<_ : ℕ -> ℕ -> Set
n < m = suc n ≤ m

Maybe : Set -> Set
Maybe A = ⊤ ⊎ A


-- Ex. Define _>_ and _≥_ on top of _≤_!
_>_ : ℕ -> ℕ -> Set
n > m = suc m ≤ n

_≥_ : ℕ -> ℕ -> Set
n ≥ m = m ≤ n

-- Another example
¬ : Set -> Set
¬ A = A -> ⊥

-- Another example: recursive Fin
Fin₀ : ℕ -> Set
Fin₀ zero = ⊥
Fin₀ (suc n) = ⊤ ⊎ Fin₀ n
