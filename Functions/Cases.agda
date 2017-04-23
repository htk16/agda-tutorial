module Functions.Cases where

open import Sets.Enumerated using (Bool; true; false)


-- Negation as a function
not : Bool -> Bool
not true = false
not false = true

-- Logical AND
_∧_ : Bool -> Bool -> Bool
true ∧ x = x
false ∧ _ = false

infixr 6 _∧_


-- Ex. Define logical OR:
_∨_ : Bool -> Bool -> Bool
true ∨ _ = true
false ∨ x = x

infixr 5 _∨_


-- Ex. Define logical OR with one alternative, 
--     with the help of not and _∧_!
_∨'_ : Bool -> Bool -> Bool
x ∨' y = not (not x ∧ not y)


-- Ex. Define a set named Answer with three elements, yes, no and maybe.
data Answer : Set where
  yes : Answer
  no : Answer
  maybe : Answer

-- Ex. Define logical operations on Answer!
notA : Answer -> Answer
notA yes = no
notA no = yes
notA maybe = maybe

_∧A_ : Answer -> Answer -> Answer
yes ∧A x = x
no ∧A _ = no
maybe ∧A no = no
maybe ∧A x = x

infixr 6 _∧A_

_∨A_ : Answer -> Answer -> Answer
yes ∨A _ = yes
no ∨A x = x
maybe ∨A yes = yes
maybe ∨A x = x


-- Ex. Define a set named Quarter with four elements, east, west, north and south.
data Quarter : Set where
  east : Quarter
  west : Quarter
  north : Quarter
  south : Quarter

-- Ex. Define a function turnLeft : Quarter → Quarter.
turnLeft : Quarter -> Quarter
turnLeft east = north
turnLeft west = south
turnLeft north = west
turnLeft south = east

-- Ex. Define the functions turnBack and turnRight with the help of turnLeft!
-- (By either pattern matching or defining a specific function composition function.)
turnRight : Quarter -> Quarter
turnRight east = south
turnRight west = north
turnRight north = east
turnRight south = west

turnBack : Quarter -> Quarter
turnBack q = turnLeft (turnLeft q)
