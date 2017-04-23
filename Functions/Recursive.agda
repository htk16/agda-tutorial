module Functions.Recursive where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; suc; zero)


-- _+_ : Addition
_+_ : ℕ -> ℕ -> ℕ
zero + n = n
suc m + n = suc (m + n)

infixr 6 _+_

-- Ex. pred, _*_, _⊔_, _⊓_ and ⌊_/2⌋
pred : ℕ -> ℕ
pred zero = zero
pred (suc n) = n


_∸_ : ℕ → ℕ → ℕ
n ∸ 0 = n
(suc m) ∸ (suc n) = m ∸ n
zero ∸ _ = zero

infixl 6 _∸_


_*_ : ℕ -> ℕ -> ℕ
n * (suc zero) = n
m * (suc n) = m + (m * n)
n * zero = zero

infixl 7 _*_


_⊔_ : ℕ -> ℕ -> ℕ
zero ⊔ n = n
n ⊔ zero = n
(suc m) ⊔ (suc n) = suc (m ⊔ n)

infixl 6 _⊔_


_⊓_ : ℕ -> ℕ -> ℕ
zero ⊓ n = zero
n ⊓ zero = zero
(suc m) ⊓ (suc n) = suc (m ⊓ n)

infixl 7 _⊓_


⌊_/2⌋ : ℕ → ℕ
⌊ suc (suc n) /2⌋ = suc ⌊ n /2⌋
⌊ suc zero /2⌋ = zero
⌊ zero /2⌋ = zero


-- Ex. even, odd
odd : ℕ -> Bool
odd zero = false
odd (suc zero) = true
odd (suc (suc n)) = odd n

even : ℕ -> Bool
even zero = true
even (suc zero) = false
even (suc (suc n)) = even n

-- Mutual definitions
odd' : ℕ -> Bool
even' : ℕ -> Bool

odd' zero = false
odd' (suc n) = even' n
even' zero = true
even' (suc n) = odd' n


-- Ex. _≡?_, _≤?_
_≡?_ : ℕ → ℕ → Bool
zero ≡? zero = true
(suc m) ≡? (suc n) = m ≡? n
_ ≡? _ = false

_≤?_ : ℕ -> ℕ -> Bool
zero ≤? _ = true
_ ≤? zero = false
(suc m) ≤? (suc n) = m ≤? n


-- Binary representation of ℕ
open import Sets.Recursive using (ℕ⁺; one; double; double+1; ℕ₂; zero; id)

-- Ex. define the conversion function
from : ℕ₂ -> ℕ
from (zero) = zero
from (id one) = suc zero
from (id (double n)) = from (id n) * from (id n)
from (id (double+1 n)) = from (id n) * from (id n) + 1

ℕ0 : ℕ
ℕ0 = from (zero)

ℕ1 : ℕ
ℕ1 = from (id one)

ℕ4 : ℕ
ℕ4 = from (id (double (double one)))

ℕ5 : ℕ
ℕ5 = from (id (double+1 (double one)))


-- Ex. Define ℤ and some operations on it (_+_, _-_, _*_)!
data ℤ : Set where
  zero : ℤ
  suc : ℤ -> ℤ
  pre : ℤ -> ℤ


_ℤ+_ : ℤ -> ℤ -> ℤ
n ℤ+ zero = n
m ℤ+ suc n = suc (m ℤ+ n)
m ℤ+ pre n = pre (m ℤ+ n)

infixr 6 _ℤ+_

_ℤ-_ : ℤ -> ℤ -> ℤ
n ℤ- zero = n
m ℤ- suc n = pre (m ℤ- n)
m ℤ- pre n = suc (m ℤ- n)

infixr 6 _ℤ-_

_ℤ*_ : ℤ -> ℤ -> ℤ
n ℤ* zero = zero
n ℤ* suc (zero) = n
m ℤ* suc n = (m ℤ* n) ℤ+ m
n ℤ* pre (zero) = zero ℤ- n
m ℤ* pre n = (m ℤ* n) ℤ- m


-- Bnary trees
data BinTree : Set where
  leaf : BinTree
  node : BinTree -> BinTree -> BinTree

-- Ex. define (recursive) mirroring of binary trees!
clone : BinTree -> BinTree
clone leaf = leaf
clone (node l r) = node (clone l) (clone r)
