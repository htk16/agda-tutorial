module Sets.Propositions where

open import Data.Nat using (ℕ; zero; suc)


-- true proposition
data ⊤ : Set where
  tt : ⊤

-- false proposition
data ⊥ : Set where

-- conjunction
data _×_ (A B : Set) : Set where
  _,_ : A -> B -> A × B

infixr 4 _,_
infixr 2 _×_

-- disjunction
data _⨄_ (A B : Set) : Set where
  inj₁ : A -> A ⨄ B
  inj₂ : B -> A ⨄ B

infixr 1 _⨄_


-- Ex. Construct one proof for each proposition if possible
⊤×⊤ : ⊤ × ⊤
⊤×⊤ = tt , tt

-- ⊤ × ⊥  can't proof it
-- ⊥ × ⊥  can't proof it

⊤⨄⊤ : ⊤ ⨄ ⊤
⊤⨄⊤ = inj₁ tt

⊤⨄⊥ : ⊤ ⨄ ⊥
⊤⨄⊥ = inj₁ tt

-- ⊥ ⨄ ⊥  can't proof it

-- ⊥ ⨄ ⊤ ⨄ ⊤ × (⊥ ⨄ ⊥) ⨄ ⊤  can't proof it


-- Less-or-equal predicate
data _≤_ : ℕ -> ℕ -> Set where
  z≤n : {n : ℕ} -> zero ≤ n
  s≤s : {m : ℕ} -> {n : ℕ} -> m ≤ n -> suc m ≤ suc n

0≤1 : 1 ≤ 10
0≤1 = s≤s z≤n
-- 0≤1 = s≤s {0} {9} (z≤n {9})

-- Ex. Prove that 3 ≤ 7!
3≤7 : 3 ≤ 7
3≤7 = s≤s (s≤s (s≤s z≤n))


7≰3 : 7 ≤ 3 -> ⊥
7≰3 (s≤s (s≤s (s≤s ())))

8≰4 : 8 ≤ 4 -> ⊥
8≰4 (s≤s x) = 7≰3 x

-- Ex. prove that 4 ≤ 2 is empty!
4≰2 : 4 ≤ 2 -> ⊥
4≰2 (s≤s (s≤s ()))

-- Ex. Define an indexed set _isDoubleOf_ : ℕ -> ℕ -> Set such that 
--     m isDoubleOf n is non-empty iff m is the double of n!
data _isDoubleOf_ : ℕ -> ℕ -> Set where
  0D0 : zero isDoubleOf zero
  2D1 : (suc (suc zero)) isDoubleOf (suc zero)
  ssDs : {m : ℕ} -> {n : ℕ} -> m isDoubleOf n -> (suc (suc m)) isDoubleOf (suc n)

-- Ex. Prove that 8 isDoubleOf 4 is non-empty
8D4 : 8 isDoubleOf 4
8D4 = ssDs (ssDs (ssDs 2D1))

-- Ex. Prove that 9 isDoubleOf 4 is empty
9D4 : 9 isDoubleOf 4 -> ⊥
9D4 (ssDs (ssDs (ssDs (ssDs ()))))


-- Ex. Define an indexed set Odd: ℕ -> Set such that odd n is non-empty iff n is odd!
data Odd'_ : ℕ -> Set where
  1isOdd : Odd' 1
  ssisOdd : {n : ℕ} -> Odd' n -> Odd' (suc (suc n))

-- Ex. Prove that Odd 9 is non-empty
9isOdd' : Odd' 9
9isOdd' = (ssisOdd (ssisOdd (ssisOdd (ssisOdd 1isOdd))))

-- Ex. Prove that Odd 8 is non-empty
8isOdd' : Odd' 8 -> ⊥
8isOdd' (ssisOdd (ssisOdd (ssisOdd (ssisOdd ()))))


-- Ex. Define Even : ℕ -> Set add Odd : ℕ -> Set!
data Even_ : ℕ -> Set
data Odd_ : ℕ -> Set

data Even_ where
  0isEven : Even 0
  even : {n : ℕ} -> Odd n -> Even (suc n)

data Odd_ where
  odd : {n : ℕ} -> Even n -> Odd (suc n)


9isOdd : Odd 9
9isOdd = (odd (even (odd (even (odd (even (odd (even (odd 0isEven)))))))))

8isOdd : Odd 8 -> ⊥
8isOdd (odd (even (odd (even (odd (even (odd (even ()))))))))


-- Ex. Define equality _≡_ : ℕ -> ℕ -> Set!
data _≡_ : ℕ -> ℕ -> Set where
  0eq0 : 0 ≡ 0
  seqs : {m : ℕ} -> {n : ℕ} -> m ≡ n -> (suc m) ≡ (suc n)


3eq3 : 3 ≡ 3
3eq3 = seqs (seqs (seqs 0eq0))

4eq3 : 4 ≡ 3 -> ⊥
4eq3 (seqs (seqs (seqs ())))


-- Ex. Define non-equality _≠_ : ℕ -> ℕ -> Set!
data _≠_ : ℕ -> ℕ -> Set where
  0neqn : {n : ℕ} -> zero ≠ suc n
  nneq0 : {n : ℕ} -> suc n ≠ zero
  sneqs : {m : ℕ} -> {n : ℕ} -> m ≠ n -> suc m ≠ suc n

4neq3 : 4 ≠ 3
4neq3 = (sneqs (sneqs (sneqs nneq0)))

3neq3 : 3 ≠ 3 -> ⊥
3neq3 (sneqs (sneqs (sneqs ())))


-- Altanative representation of Less-or-equal predicate
data _≤'_ : ℕ -> ℕ -> Set where
  ≤'-refl : {m : ℕ} -> m ≤' m
  ≤'-step : {m : ℕ} -> {n : ℕ} -> m ≤' n -> m ≤' suc n


-- Syntactic abbreviations
data _≤''_ : ℕ -> ℕ -> Set where
  z≤n : ∀ {n} -> zero ≤'' n
  s≤s : ∀ {m n} -> m ≤'' n -> suc m ≤'' suc n


-- Addition predicate
data _+_≡_ : ℕ -> ℕ -> ℕ -> Set where
  0+n≡n : ∀ {n} -> zero + n ≡ n
  m+n≡k : ∀ {m n k} -> m + n ≡ k -> suc m + n ≡ suc k

2+2≡4 : 2 + 2 ≡ 4
2+2≡4 = m+n≡k (m+n≡k 0+n≡n)

-- Ex. Prove that 5 + 5 = 10!
5+5≡ : 5 + 5 ≡ 10
5+5≡ = m+n≡k (m+n≡k (m+n≡k (m+n≡k (m+n≡k 0+n≡n))))

-- Ex. Prove that 2 + 2 ≠ 5!
2+2≡5 : 2 + 2 ≡ 5 -> ⊥
2+2≡5 (m+n≡k (m+n≡k ()))


-- Ex. Define _⊓_ : ℕ → ℕ → Set such that
--     n ⊓ m ≡ k iff k is the minimum of n and m
data _⊓_ : ℕ -> ℕ -> Set where
  -- TODO: Define this!

-- Ex. Define _⊔_ : ℕ → ℕ → Set such that
--     n ⊔ m ≡ k iff k is the maximum of n and m!
data _⊔_ : ℕ -> ℕ -> Set where
  -- TODO: Define this!


-- Another definition of _≤_
data _≤'''_ : ℕ -> ℕ -> Set where
  ≤+ : ∀ {m n k} -> m + n ≡ k -> m ≤''' k

-- Ex. Define _isDoubleOf_ : ℕ -> ℕ -> Set on top of _+_≡_!
data _isDoubleOf'_ : ℕ -> ℕ -> Set where
  double : ∀ {m n} -> m + m ≡ n -> n isDoubleOf' m

-- Ex. Prove that 8 isDoubleOf' 4 is non-empty
4+4≡8 : 4 + 4 ≡ 8
4+4≡8 = m+n≡k (m+n≡k (m+n≡k (m+n≡k 0+n≡n)))

8=4*2 : 8 isDoubleOf' 4
8=4*2 = double 4+4≡8

-- Ex. Prove that 9 isDoubleOf' 4 is empty!
4+4≡9 : 4 + 4 ≡ 9 -> ⊥
4+4≡9 (m+n≡k (m+n≡k (m+n≡k (m+n≡k ()))))

9=4*2 : 9 isDoubleOf' 4 -> ⊥
9=4*2 (double (m+n≡k (m+n≡k (m+n≡k (m+n≡k ())))))
-- 9=4*2 (double 4+4≡9)


-- Ex. Define _*_≡_ : ℕ → ℕ → Set with the help of _+_≡_!
data _*_≡_ : ℕ → ℕ → ℕ → Set where
  n*0≡0 : ∀ {n} -> n * 0 ≡ 0
  m*n≡k : ∀ {m n k l} -> m + k ≡ l -> m * n ≡ k -> m * (suc n) ≡ l
  
-- Ex. Prove that 3 * 3 ≡ 9 is non-empty!
3+0=3 : 3 + 0 ≡ 3
3+0=3 = m+n≡k (m+n≡k (m+n≡k 0+n≡n))

3*1=3 : 3 * 1 ≡ 3
3*1=3 = m*n≡k 3+0=3 n*0≡0

3+3=6 : 3 + 3 ≡ 6
3+3=6 = m+n≡k (m+n≡k (m+n≡k 0+n≡n))

3*2=6 : 3 * 2 ≡ 6
3*2=6 = m*n≡k 3+3=6 3*1=3

3+6=9 : 3 + 6 ≡ 9
3+6=9 = m+n≡k (m+n≡k (m+n≡k 0+n≡n))

3*3=9 : 3 * 3 ≡ 9
3*3=9 = m*n≡k 3+6=9 3*2=6

-- Ex. Prove that 3 * 3 ≡ 8 is empty!
3+2=5 : 3 + 2 ≡ 5
3+2=5 = m+n≡k (m+n≡k (m+n≡k 0+n≡n))

3+5=8 : 3 + 5 ≡ 8
3+5=8 = m+n≡k (m+n≡k (m+n≡k 0+n≡n))

3+0=2 : 3 + 0 ≡ 2 -> ⊥
3+0=2 (m+n≡k (m+n≡k ()))

3*1=2 : 3 * 1 ≡ 2 -> ⊥
3*1=2 (m*n≡k (m+n≡k (m+n≡k ())) (n*0≡0))


3*2=5 : 3 * 2 ≡ 5 -> ⊥
3*2=5 (m*n≡k (m+n≡k (m+n≡k (m+n≡k 0+n≡n))) (m*n≡k (m+n≡k (m+n≡k ())) n*0≡0))


3*3=8 : 3 * 3 ≡ 8 -> ⊥
3*3=8 (m*n≡k 
        (m+n≡k (m+n≡k (m+n≡k 0+n≡n)))
        (m*n≡k
          (m+n≡k (m+n≡k (m+n≡k 0+n≡n)))
          (m*n≡k 
            (m+n≡k (m+n≡k ()))
            n*0≡0)))


-- Ex. Define _≈_ : ℕ → ℕ⁺ → Set which 
--     represents the (canonical) isomorphism between ℕ and ℕ⁺!
data ℕ⁺ : Set where
  one      : ℕ⁺
  double   : ℕ⁺ -> ℕ⁺
  double+1 : ℕ⁺ -> ℕ⁺

data _≈_ : ℕ -> ℕ⁺ -> Set where
  1≈1 : suc zero ≈ one
  *2 : ∀ {m n k} -> m + m ≡ k -> m ≈ n -> k ≈ double n
  *2+1 : ∀ {m n k} -> m + m ≡ k -> m ≈ n -> suc k ≈ double+1 n

-- Ex. Prove that 5 ≈ double+1 (double one) is non-empty!
5≈5 : 5 ≈ double+1 (double one)
5≈5 = *2+1 (m+n≡k (m+n≡k 0+n≡n)) (*2 (m+n≡k 0+n≡n) 1≈1)

-- Ex. Prove that 4 ≈ double+1 (double one) is empty!
4≈5 : 4 ≈ double+1 (double one) -> ⊥
4≈5 (*2+1 (m+n≡k (m+n≡k ())) (*2 (m+n≡k 0+n≡n) 1≈1))
