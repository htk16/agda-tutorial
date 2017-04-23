module Sets.Parameters_vs_Indices where

open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.List using (List; []; _∷_)


-- Example 1
-- data _≤′_ : ℕ -> ℕ -> Set where
--   ≤′-refl : {m : ℕ} -> m ≤′ m
--   ≤′-step : {m : ℕ} -> {n : ℕ} -> m ≤′ n -> m ≤′ suc n

-- The first index can be turned into a new parameter
-- if each constructor has the same variable on the first index position (in the result type).
data _≤′_ (m : ℕ) : ℕ -> Set where
  ≤′-refl : m ≤′ m
  ≤′-step : {n : ℕ} -> m ≤′ n -> m ≤′ suc n

-- The parameter can be fixed to get a simpler definition, for example
data 10≤′ : ℕ -> Set where
  10≤′-refl : 10≤′ 10
  10≤′-step : {n : ℕ} -> 10≤′ n -> 10≤′ (suc n)


-- Example 2
data _+_≡_ : ℕ -> ℕ -> ℕ -> Set where
  0+n≡n : ∀ {n} -> zero + n ≡ n
  m+n≡k : ∀ {m n k} -> m + n ≡ k -> suc m + n ≡ suc k

-- data _≤″_ : ℕ -> ℕ -> Set where
--   ≤+ : ∀ {m n k} -> m + n ≡ k -> m ≤″ k

-- data _≤″_ (m : ℕ) : ℕ -> Set where
--   ≤+ : ∀ {n k} -> m + n ≡ k -> m ≤″ k

data _≤″_ (m : ℕ) (k : ℕ) : Set where
  ≤+ : ∀ {n} -> m + n ≡ k -> m ≤″ k


-- General equality
data _≡_ {A : Set} (x : A) : A -> Set where
  refl : x ≡ x

infix 4 _≡_

0≡0 : 0 ≡ 0
-- 0≡0 = refl {ℕ} {0}
0≡0 = refl {ℕ} {0}


-- _∈_ proposition
data _∈_ {A : Set} (x : A) : List A -> Set where
  first : ∀ {xs} -> x ∈ x ∷ xs
  later : ∀ {y xs} -> x ∈ xs -> x ∈ y ∷ xs

infix 4 _∈_


1∷2∷nil : List ℕ
1∷2∷nil = 1 ∷ 2 ∷ []

1∈1∷2∷nil : 1 ∈ 1∷2∷nil
1∈1∷2∷nil = first

2∈1∷2∷nil : 2 ∈ 1∷2∷nil
2∈1∷2∷nil = later first

data ⊥ : Set where

3∈1∷2∷nil : 3 ∈ 1∷2∷nil -> ⊥
3∈1∷2∷nil (later (later ()))


-- Ex. Define _⊆_ {A : Set} : List A → List A → Set!
data _⊆_ {A : Set} : List A -> List A -> Set where
  ⊆-zero : ∀ {xs} -> [] ⊆ xs
  ⊆-step : ∀ {x xs ys} -> xs ⊆ ys -> x ∷ xs ⊆ x ∷ ys

infix 4 _⊆_


-- Ex. Prove that 1 ∷ 2 ∷ [] ⊆ 1 ∷ 2 ∷ 3 ∷ []!
1∷2∷nil⊆1∷2∷3∷nil : 1 ∷ 2 ∷ [] ⊆ 1 ∷ 2 ∷ 3 ∷ []
1∷2∷nil⊆1∷2∷3∷nil = ⊆-step (⊆-step ⊆-zero)

-- Ex. Prove that 1 ∷ 2 ∷ 3 ∷ [] ⊆ 1 ∷ 2 ∷ [] is false!
1∷2∷3∷nil⊆1∷2∷nil : 1 ∷ 2 ∷ 3 ∷ [] ⊆ 1 ∷ 2 ∷ [] -> ⊥
1∷2∷3∷nil⊆1∷2∷nil (⊆-step (⊆-step ()))


-- Ex. Define a permutation predicate!
data _isPermutationOf_ {A : Set} : List A -> List A -> Set where
  eq : ∀ {xs} -> xs isPermutationOf xs
  head : ∀ {x1 x2 xs} -> x1 ∷ x2 ∷ xs isPermutationOf x2 ∷ x1 ∷ xs
  tail : ∀ {x xs ys} -> xs isPermutationOf ys -> x ∷ xs isPermutationOf x ∷ ys
  trans : ∀ {xs ys zs} -> xs isPermutationOf ys -> ys isPermutationOf zs 
            -> xs isPermutationOf zs

infix 4 _isPermutationOf_

[1,2,3] : List ℕ
[1,2,3] = 1 ∷ 2 ∷ 3 ∷ []

[2,3]-isPermutationOf-[3,2] : 2 ∷ 3 ∷ [] isPermutationOf 3 ∷ 2 ∷ []
[2,3]-isPermutationOf-[3,2] = head

[1,2,3]-isPermutationOf-[1,3,2] : 1 ∷ 2 ∷ 3 ∷ [] isPermutationOf 1 ∷ 3 ∷ 2 ∷ []
[1,2,3]-isPermutationOf-[1,3,2] = tail head

[1,3,2]-isPermutationOf-[3,1,2] : 1 ∷ 3 ∷ 2 ∷ [] isPermutationOf 3 ∷ 1 ∷ 2 ∷ []
[1,3,2]-isPermutationOf-[3,1,2] = head

[3,1,2]-isPermutationOf-[3,2,1] : 3 ∷ 1 ∷ 2 ∷ [] isPermutationOf 3 ∷ 2 ∷ 1 ∷ []
[3,1,2]-isPermutationOf-[3,2,1] = tail head

[1,2,3]-isPermutationOf-[3,2,1] : 1 ∷ 2 ∷ 3 ∷ [] isPermutationOf 3 ∷ 2 ∷ 1 ∷ []
[1,2,3]-isPermutationOf-[3,2,1] = trans
  [1,2,3]-isPermutationOf-[1,3,2]
  (trans [1,3,2]-isPermutationOf-[3,1,2] [3,1,2]-isPermutationOf-[3,2,1])


-- Ex. Define a sort predicate!
data _isSorted : List ℕ -> Set where
  zero : [] isSorted
  single : ∀ {n} -> (n ∷ []) isSorted
  ge : ∀ {x y ys} -> x ≤ y -> (y ∷ ys) isSorted -> (x ∷ y ∷ ys) isSorted


1∷2∷3::nil-isSorted : (1 ∷ 2 ∷ 3 ∷ []) isSorted
1∷2∷3::nil-isSorted = ge (s≤s z≤n) (ge (s≤s (s≤s z≤n)) single)

3∷2∷1∷nil-isSorted : (3 ∷ 2 ∷ 1 ∷ []) isSorted -> ⊥
3∷2∷1∷nil-isSorted (ge (s≤s (s≤s ())) (ge (s≤s ()) single))
