module Functions.Universal_Quantification where

open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _<_; z≤n; s≤s; _≤′_; ≤′-step; ≤′-refl)
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Function using (flip; _$_; _∘_)


-- Universal quantification
≤-refl : (n : ℕ) -> n ≤ n
≤-refl zero    = z≤n
≤-refl (suc n) = s≤s (≤-refl n)


-- Ex. Define the following functions (prove these properties)
≤-trans : ∀ {m n o} -> m ≤ n -> n ≤ o -> m ≤ o
≤-trans z≤n _ = z≤n
≤-trans (s≤s m≤n) (s≤s n≤o) = s≤s (≤-trans m≤n n≤o)

total : ∀ m n -> m ≤ n ⊎ n ≤ m
total zero _ = inj₁ z≤n
total _ zero = inj₂ z≤n
total (suc m) (suc n) = [_,_]′ (inj₁ ∘ s≤s) (inj₂ ∘ s≤s) (total m n)

≤-pred : ∀ {m n} -> suc m ≤ suc n -> m ≤ n
≤-pred (s≤s z≤n) = z≤n
≤-pred (s≤s m≤n) = m≤n

≤-mono : ∀ {m n k} -> n ≤ m -> k + n ≤ k + m
≤-mono {m} {n} {zero} n≤m = n≤m
≤-mono {m} {n} {suc k} n≤m = s≤s (≤-mono {m} {n} {k} n≤m)


-- Ex. Define the following functions
≤-step : ∀ {m n} -> m ≤ n -> m ≤ 1 + n
≤-step z≤n = z≤n
≤-step (s≤s m≤n) = s≤s (≤-step m≤n)

{-
data _≤′_ (m : ℕ) : ℕ → Set where
  ≤′-refl :                          m ≤′ m
  ≤′-step : ∀ {n} (m≤′n : m ≤′ n) → m ≤′ suc n
-}

≤′⇒≤ : ∀ {a b} -> a ≤′ b -> a ≤ b
≤′⇒≤ {zero} {_} _ = z≤n
≤′⇒≤ {suc a} {_} ≤′-refl = s≤s (≤′⇒≤ {a} {a} ≤′-refl)
≤′⇒≤ (≤′-step a≤′b) = ≤-step (≤′⇒≤ a≤′b)

z≤′n : ∀ n -> zero ≤′ n
z≤′n zero = ≤′-refl
z≤′n (suc n) = ≤′-step (z≤′n n)

s≤′s : ∀ {m n} -> m ≤′ n -> suc m ≤′ suc n
s≤′s ≤′-refl = ≤′-refl
s≤′s (≤′-step m≤′n) = ≤′-step (s≤′s m≤′n)

≤⇒≤′ : ∀ {a b} -> a ≤ b -> a ≤′ b
≤⇒≤′ {_} {n} z≤n = z≤′n n
≤⇒≤′ (s≤s a≤′b) = s≤′s (≤⇒≤′ a≤′b)


-- Ex. Define fin≤
fin≤ : ∀ {n}(m : Fin n) -> toℕ m < n
fin≤ zero = s≤s z≤n
fin≤ (suc i) = s≤s (fin≤ i)
