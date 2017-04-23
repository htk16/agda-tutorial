module Sets.Enumerated where

-- The Bool set
data Bool : Set where
  true  : Bool
  false : Bool

-- Ex. A. Define a set named Answer with three elements, yes, no and maybe.
data Answer : Set where
  yes : Answer
  no : Answer
  maybe : Answer

-- Ex. B. Define a set named Quarter with four elements, east, west, north and south
data Quarter : Set where
  east : Quarter
  west : Quarter
  north : Quarter
  south : Quarter


data Bool' : Set where
  true'  : Bool'
  false' : Bool'

data ⊥ : Set where

data ⊤ : Set where
  tt : ⊤
