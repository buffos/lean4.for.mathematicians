def α : Type := Nat
def β : Type := Bool
def F : Type → Type := List
def G : Type → Type → Type := Prod

#check α        -- Type
#check F α      -- Type
#check F Nat    -- Type
#check G α      -- Type → Type
#check G α β    -- Type
#check G α Nat  -- Type


/-
structure Prod (α : Type) (β : Type) : Type where
  fst : α
  snd : β

inductive Sum (α : Type) (β : Type) : Type where
  | inl : α → Sum α β
  | inr : β → Sum α β
-/
#check Nat
#check Prod α β       -- Type
#check α × β          -- Type

#check Prod Nat Nat   -- Type
#check Nat × Nat      -- Type

#check List α    -- Type
#check List Nat  -- Type


-- Universes of Types

#check Type     -- Type 1
#check Type 1   -- Type 2
#check Type 2   -- Type 3
#check Type 3   -- Type 4
#check Type 4   -- Type 5

/-
Prop (Propositions) - Sort 0 - They are either True or False
Type (Type 0) - Sort 1 - The world of Variables
Type 1 - Sort 2 - The world of functions within variables
Type 2 - Sort 3 -- The world of functions within Type 1 and below  etc..
-/


#check List    -- List.{u} (α : Type u) : Type u
#check Prod    -- Prod.{u, v} (α : Type u) (β : Type v) : Type (max u v)


/-
universe u
def F (α : Type u) : Type u := Prod α α
#check F    -- Type u → Type u
-/
def FF.{u} (α : Type u) : Type u := Prod α α
#check F    -- Type u → Type u
