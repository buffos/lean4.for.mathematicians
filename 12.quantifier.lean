/-
We are going to talk about ∀ x : α, p x
This is:
  >Given a proof of p x, in a context where x : α is arbitrary, we obtain a proof ∀ x : α, p x.
So by elimination
  >Given a proof ∀ x : α, p x and any term t : α, we obtain a proof of p t.

Remember that we had constructions of the type (fun x : α => t) : (x : α) → β x.
If we name the function s : (x : α) → β x. and any term t : α, we have s t : β t.
If  β x has type Prop , it like saying ∀ x : α, p x

So
 > ∀ x : α, p
is like saying
 > (x : α) → p

Here is an example of how the propositions-as-types correspondence gets put into practice.
-/

def kk := Type -> Prop
#check kk -- this is type 1 object

example (α : Type) (p q : α → Prop) : (∀ x : α, p x ∧ q x) → ∀ y : α, p y :=
  fun h : ∀ x : α, p x ∧ q x =>
  fun y : α => show p y from (h y).left

/-
We want to prove
> ∀ y : α, p y
this means we take an arbitrary y and we prove p y
`h` has type `∀ x : α, p x ∧ q x` this means `h y` has type `p y ∧ q y` and by elimination we get `p y`

assume h : ∀x, p x ∧ q x
assume y : α
have h_y : p y ∧ q y := h y    -- Universal elimination
show p y from h_y.left         -- Conjunction elimination
-/

/- View as traditional composition of functions
the second function is the outer of course so we have
> example (α : Type) (p q : α → Prop) : (∀ x : α, p x ∧ q x) → ∀ y : α, p y := And.left ∘ ·
· is a placeholder for the argument h (Lean's explicit function application syntax)
This is equivalent to: `fun h => fun y => (h y).left`
We can also write it as :
> example (α : Type) (p q : α → Prop) : (∀ x : α, p x ∧ q x) → ∀ y : α, p y :=  fun h => And.left ∘ h
-/

/- Note on naming
`expressions which differ up to renaming of bound variables are considered to be equivalent`
so the following is equivalent
-/

example (α : Type) (p q : α → Prop) : (∀ x : α, p x ∧ q x) → ∀ x : α, p x :=
  fun h : ∀ x : α, p x ∧ q x =>
  fun z : α =>
  show p z from And.left (h z)

-- here is how we can express that a relation is transitive

variable (α : Type) -- a is just a Type
variable (r : α → α → Prop) -- this means r is a binary relationship on type α
variable (a b c : α) --  a b and c are of type α
variable (hab : r a b) (hbc : r b c)

variable (trans_r : ∀ x y z, r x y → r y z → r x z)
-- this says for if we have a proof of r x y and a proof of r y z and we apply it to trans_r
-- it will get a proof of r x z

#check trans_r    -- ∀ (x y z : α), r x y → r y z → r x z
#check trans_r a b c -- r a b → r b c → r a c
#check trans_r a b c hab -- r b c → r a c
#check trans_r a b c hab hbc -- r a c

-- we can also make the arguments implicit

variable (trans_rr : ∀ {x y z}, r x y → r y z → r x z)
#check trans_rr
#check trans_rr hab
#check trans_rr hab hbc
