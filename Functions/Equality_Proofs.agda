module Functions.Equality_Proofs where

open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_)
open import Function using (_$_)


-- Proprositional equality: _≡_
data _≡_ {A : Set} (x : A) : A → Set  where
  refl : x ≡ x

infix 4 _≡_


-- _≡_ is an equivalence and a congruence
refl′ : ∀ {A} (a : A) -> a ≡ a
refl′ a = refl

sym : ∀ {A} {a b : A} -> a ≡ b -> b ≡ a
sym refl = refl


-- Ex. Define trans and cong
trans : ∀ {A} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans refl refl = refl

cong : ∀ {A B} {m n : A} -> (f : A -> B) -> m ≡ n -> f m ≡ f n
cong f refl = refl


-- Proof of a + 0 ≡ a
-- n + 0 ≡ n is not trivial (zero + n = n, suc n + m = suc (n + m))
+-right-identity : ∀ n -> n + 0 ≡ n
+-right-identity zero = refl
+-right-identity (suc n) = cong suc (+-right-identity n)


-- Ex. Finish the ingredients of the proof that (ℕ, _+_) is a commutative monoid!
+-left-identity : ∀ a → 0 + a ≡ a
+-left-identity _ = refl

+-assoc : ∀ a b c -> a + (b + c) ≡ (a + b) + c
+-assoc zero _ _ = refl
+-assoc (suc a) b c = cong suc (+-assoc a b c)

m+1+n≡1+m+n : ∀ m n -> m + suc n ≡ suc (m + n)
m+1+n≡1+m+n zero _ = refl
m+1+n≡1+m+n (suc m) n = cong suc (m+1+n≡1+m+n m n)


-- Exercise: List ⊤ ~ ℕ
-- Let's prove that fromList and toList are inverses of each other and that they preserve the operations _++_ and _+_!
fromList : List ⊤ → ℕ
fromList [] = zero
fromList (x ∷ xs) = suc (fromList xs)

toList : ℕ → List ⊤
toList zero = []
toList (suc n) = tt ∷ toList n


from-to : ∀ a -> fromList (toList a) ≡ a
from-to zero = refl
from-to (suc n) = cong suc (from-to n)

to-from : ∀ a -> toList (fromList a) ≡ a
to-from [] = refl
to-from (tt ∷ t) = cong (_∷_ tt) (to-from t)

fromPreserves++ : ∀ (a b : List ⊤) -> fromList (a ++ b) ≡ fromList a + fromList b
fromPreserves++ [] _ = refl
fromPreserves++ (tt ∷ xs) ys = cong suc (fromPreserves++ xs ys)

toPreserves+ : ∀ (a b : ℕ) -> toList (a + b) ≡ toList a ++ toList b
toPreserves+ zero _ = refl
toPreserves+ (suc m) n = cong (_∷_ tt) (toPreserves+ m n)


-- Equational reasoning
_≡⟨_⟩_ : ∀ {A : Set} (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ refl ⟩ refl = refl

infixr 2 _≡⟨_⟩_

_∎ : ∀ {A : Set} (x : A) → x ≡ x
x ∎ = refl

-- infix  2 _∎
infix  3 _∎

-- Usage example
+-comm' : (n m : ℕ) → n + m ≡ m + n
+-comm' zero n = sym (+-right-identity n)
+-comm' (suc m) n =
      suc m + n
    ≡⟨ refl ⟩
      suc (m + n)
    ≡⟨ cong suc (+-comm' m n) ⟩
      suc (n + m)
    ≡⟨ sym (m+1+n≡1+m+n n m) ⟩
      n + suc m
    ∎


-- Properties of _*_
distribʳ-*-+ : ∀ a b c → (a + b) * c ≡ a * c + b * c
distribʳ-*-+ zero    _ _ = refl
distribʳ-*-+ (suc a) b c =
      ((suc a) + b) * c
    ≡⟨ refl ⟩
      (suc (a + b)) * c
    ≡⟨ refl ⟩
      c + (a + b) * c
    ≡⟨ cong (_+_ c) (distribʳ-*-+ a b c) ⟩
      c + (a * c + b * c)
    ≡⟨ +-assoc c (a * c) (b * c) ⟩
      (c + a * c) + b * c
    ≡⟨ refl ⟩
      ((suc a) * c) + b * c
    ∎


-- Ex. define the following functions:
*-assoc : ∀ a b c -> a * (b * c) ≡ (a * b) * c
*-assoc zero _ _ = refl
*-assoc (suc a) b c =
        (suc a) * (b * c)
      ≡⟨ refl ⟩
        (b * c) + a * (b * c)
      ≡⟨ cong (_+_ (b * c)) (*-assoc a b c) ⟩
        b * c + (a * b) * c
      ≡⟨ sym (distribʳ-*-+ b (a * b) c) ⟩
        (b + (a * b)) * c
      ≡⟨ refl ⟩
        ((suc a) * b) * c
      ∎

*-left-identity : ∀ a → 1 * a ≡ a
*-left-identity a = 
                1 * a
              ≡⟨ refl ⟩
                a + (0 * a)
              ≡⟨ refl ⟩
                a + 0
              ≡⟨  +-right-identity a ⟩
                a
              ∎

-- Ex. define *-comm and helper functions
n*0≡0 : ∀ n → n * 0 ≡ 0
n*0≡0 zero = refl
n*0≡0 (suc n) =
      (suc n) * 0
    ≡⟨ refl ⟩
      0 + n * 0
    ≡⟨ refl ⟩
      n * 0
    ≡⟨ n*0≡0 n ⟩
      0
    ∎

*-suc : ∀ n m → n + n * m ≡ n * suc m
*-suc 0 m = refl
*-suc (suc n) m =
      (suc n) + (suc n) * m
    ≡⟨ refl ⟩
      suc (n + (suc n) * m)
    ≡⟨ cong suc (+-assoc n m (n * m)) ⟩
      suc (n + m + n * m)
    ≡⟨ cong (λ x -> suc (x + n * m)) (+-comm' n m) ⟩
      suc (m + n + n * m)
    ≡⟨ cong suc (sym (+-assoc m n (n * m))) ⟩
      (suc m) + (n + n * m)
    ≡⟨ cong (_+_ (suc m)) (*-suc n m) ⟩
      (suc m) + n * (suc m)
    ≡⟨ refl ⟩
      (suc n) * (suc m)
    ∎

*-comm : ∀ m n → m * n ≡ n * m
*-comm m 0 =
       m * 0 
     ≡⟨ n*0≡0 m ⟩
       0
     ≡⟨ refl ⟩
       0 * m
     ∎
*-comm m (suc n) =
       m * (suc n)
     ≡⟨  sym (*-suc m n) ⟩
       m + m * n
     ≡⟨ cong (_+_ m) (*-comm m n) ⟩
       m + n * m
     ≡⟨ refl ⟩
       (suc n) * m
     ∎
