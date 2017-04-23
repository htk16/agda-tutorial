module Sets.Mutual where

open import Sets.Enumerated using (Bool; true; false)
open import Syntax.Decimal_Naturals using (ℕ; zero; suc)

data L : Set
data M : Set

data L where
  nil : L
  _::_ : ℕ -> M -> L

data M where
  _::_ : Bool -> L -> M


-- Ex. What are the elements of L and M ?
l_elem1 : L
l_elem1 = nil

m_elem1 : M
m_elem1 = true :: l_elem1


-- Ex. Define trees with nodes with finite children (0, 1, 2, ...)!
data Tree : Set
data Children : Set


data Tree where
  node : Children -> Tree

data Children where
  nil : Children
  _,_ : Tree -> Children -> Children

infixr 5 _,_


root : Tree
root = node nil

tree1 : Tree
tree1 = node (node nil , node nil , nil)

tree2 : Tree
tree2 = node (tree1 , node nil , tree1 , nil)
