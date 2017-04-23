module Sets.Recursive where

open import Sets.Enumerated using (Bool; true; false)

data ℕ : Set where
  zero : ℕ
  suc  : ℕ -> ℕ

data ℕ⁺ : Set where
  one      : ℕ⁺
  double   : ℕ⁺ -> ℕ⁺
  double+1 : ℕ⁺ -> ℕ⁺

data ℕ₂ : Set where
  zero : ℕ₂
  id   : ℕ⁺ -> ℕ₂

-- Ex. How 9 is represented in ℕ₂? Type-check the expression!
nine : ℕ₂
nine = id (double+1 (double (double one)))

-- Ex. define ℤ!

data BinTree : Set where
  leaf : BinTree
  node : BinTree -> BinTree -> BinTree

-- Ex. define binary trees according to the following shapes!
bin_tree1 : BinTree
bin_tree1 = leaf

bin_tree2 : BinTree
bin_tree2 = node leaf leaf

bin_tree3 : BinTree
bin_tree3 = node bin_tree2 bin_tree2

bin_tree4 : BinTree
bin_tree4 = node (node (node leaf leaf) leaf) leaf

-- Ex. Define binary trees with natural number data attached to the leafs
data BinTree2 : Set where
  leaf2 : ℕ -> BinTree2
  node2 : BinTree2 -> BinTree2 -> BinTree2

-- Ex. Define binary trees with natural number data attached to the nodes
data BinTree3 : Set where
  leaf3 : BinTree3
  node3 : ℕ -> BinTree3 -> BinTree3 -> BinTree3

-- Ex. Define binary trees with Booleans in the nodes and natural numbers in the leafs
data BinTree4 : Set where
  leaf4 : ℕ -> BinTree4
  node4 : Bool -> BinTree4 -> BinTree4 -> BinTree4


-- Ex. Define the lists (finite sequences) of natural numbers
data List : Set where
  cons : ℕ -> List -> List
  nil : List

-- Ex. Define the non-empty lists of natural numbers
data List2 : Set where
  cons2 : ℕ -> List2 -> List2
  nil2 : ℕ -> List2
