module Functions.Dependent where

open import Data.Nat using (ℕ; zero; suc; _+_; z≤n; s≤s; _<_)
open import Data.Fin using (Fin; zero; suc)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Product using (_×_; _,_)


-- Ependently typed functions
-- Example
fromℕ : (n : ℕ) -> Fin (suc n)
fromℕ zero = zero
fromℕ (suc n) = suc (fromℕ n)


-- Ex. Define a subtraction with restarted domain:
_-_ : (n : ℕ) -> Fin (suc n) -> ℕ
zero - _ = zero
n - zero = n
(suc m) - (suc n) = m - n

-- Ex. Define toℕ :
toℕ : ∀ {n} -> Fin n -> ℕ
toℕ zero = zero
toℕ (suc n) = suc (toℕ n)

-- Ex. fromℕ≤ : ∀ {m n} -> m < n -> Fin n
fromℕ≤ : ∀ {m n} -> m < n -> Fin n
fromℕ≤ (s≤s z≤n) = zero
fromℕ≤ (s≤s (s≤s cmp)) = suc (fromℕ≤ (s≤s cmp))

-- Ex. Define inject+ such that toℕ (inject+ n i) is the same as toℕ i:
inject+ : ∀ {m} n -> Fin m -> Fin (m + n)
inject+ _ zero = zero
inject+ n (suc v) = suc (inject+ n v)

-- Ex. Define four such that toℕ four is 4
four : Fin 66
four = suc (suc (suc (suc zero)))

-- Ex. Define raise such that toℕ (raise n i) is the same as n + toℕ i:
raise : ∀ {m} n -> Fin m -> Fin (n + m)
raise zero i = i
raise (suc n) i = suc (raise n i)


-- Exercises

-- Ex. Define head and tail
head : ∀ {n}{A : Set} -> Vec A (suc n) -> A
head (h ∷ _) = h

tail : ∀ {n}{A : Set} -> Vec A (suc n) -> Vec A n
tail (_ ∷ t) = t

-- Ex. Define concatennation for vectors
_++_ : ∀ {n m}{A : Set} -> Vec A n -> Vec A m -> Vec A (n + m)
[] ++ xs = xs
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

-- Ex. Define maps. (Note that two cases will be enough!)
maps : ∀ {n}{A B : Set} -> Vec (A -> B) n -> Vec A n -> Vec B n
maps [] [] = []
maps (f ∷ fs) (x ∷ xs) = (f x) ∷ (maps fs xs)

-- Ex. Define replicate.
replicate : ∀ {n}{A : Set} -> A -> Vec A n
replicate {zero} _ = []
replicate {suc _} x = x ∷ (replicate x)

-- Ex. Define map with the help of maps and replicate
map : ∀ {n}{A B : Set} -> (A -> B) -> Vec A n -> Vec B n
map f xs = maps (replicate f) xs

-- Ex. Define zip whith the help of map and maps
zip : ∀ {n}{A B : Set} -> Vec A n -> Vec B n -> Vec (A × B) n
zip xs ys = maps (map _,_ xs) ys

-- Ex. Define safe element indexing
_!_ : ∀ {n}{A : Set} -> Vec A n -> Fin n -> A
(x ∷ _) ! zero = x
(_ ∷ xs) ! (suc n) = xs ! n
