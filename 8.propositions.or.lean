-- MyOr can be defined as an inductive type and not as a structure because we need
-- multiple constructors

inductive MyOr: Prop -> Prop -> Prop
| inl {a: Prop} (b: Prop) (h : a)  : MyOr a b -- Left introduction
| inr {b: Prop} (a: Prop) (h : b) : MyOr a b -- Right introduction

-- MyOr is a type constructor: MyOr : Prop → Prop → Prop
-- It needs parameters to become a concrete type

variable (p q r : Prop) (hp : p) (hq : q)
-- we have p and q are propositions and hp and hq are proofs for p and q

#check MyOr.inl q hp -- Lean infers the type automatically
#check (MyOr.inl q hp : MyOr p q)  -- Explicit type annotation

def MyOr.elim {a b c : Prop} (h : MyOr a b) (ha : a → c) (hb : b → c) : c :=
  match h with
  | MyOr.inl b h => ha h
  | MyOr.inr a h => hb h

/-
Let's explain it

Inputs:
h : Proof of MyOr a b (either a or b is true)
ha : Function converting proof of a to proof of c  (this is a construction proof of a → c)
hb : Function converting proof of b to proof of c  (this is a construction proof of b → c)

Output: Proof of c

Explaining MyOr.inl h => ha h
MyOr.inl h is of proof of a. So ha (proof of a) = (proof of c)
-/

example (hp : p) : p ∨ q := Or.intro_left q hp
example (hq : q) : p ∨ q := Or.intro_right p hq


example (h : p ∨ q) : q ∨ p := -- start with a proof of p ∨ q
  Or.elim h
    (fun hp: p => show q ∨ p from Or.intro_right q hp) -- the same as fun hp: p => Or.intro_right q hp which creates q ∨ p
    (fun hq: q => show q ∨ p from Or.intro_left p hq)

/-
How show from works
- Purpose:
  - Explicitly states "I'm proving proposition T using expression expr"
  - Verifies that expr has type T
- Equivalent to: Just writing expr (the show is documentation + type check)
- Components:
 - T: The target type/proposition (q ∨ p in your case)
 - expr: The proof term that inhabits type T

 we use show for
 - Documentation: Makes the proof more readable
 - Debugging: Helps isolate type errors
 - Guidance: Clarifies the goal at each proof step
 - Annotation: Helps when type inference needs hints

alternatively we can write
example (h : p ∨ q) : q ∨ p :=  Or.elim h Or.inr Or.inl
-/

-- NEGATION
-- Negation, ¬p, is actually defined to be p → False, so we obtain ¬p by deriving a contradiction from p.

-- lets proof (p → q) → ¬q → ¬p

example (hpq: p → q) (hnq : ¬q) : ¬p :=
  fun hp:p => show False from hnq (hpq hp)

-- how this works?
-- fun gets a proof of p
-- then hpq gets this hp and returns hq , which is a proof of q
-- feeds it to hnq(proof of q) -> False
-- so we got p -> False which is the definition of ¬p

-- ¬p isn't "p is false" but "p implies contradiction"

example (hp : p) (hnp : ¬p) : q := False.elim (hnp hp)

/-
How is False.elim defined?

inductive False : Prop  -- false is an empty type with no possible inhabitants

False.elim : {C : Sort u} → False → C
This means: "Given any type `C` (in any universe `u`) and a proof of `False`, return a value of type `C`."

And how is this implemented? (its really amazing)
def False.elim {C : Sort u} (h : False) : C :=
  match h with

Since False has no values, match has zero cases
So we have the following
Proof of False -> Pattern Match -> No Cases -> No Code Needed -> Result is any Type C

During compilation it is transformed as follows
def False.elim {C : Sort u} (h : False) : C :=
  False.rec (fun _ => C) h

where False.rec : {C : False → Sort u} → (h : False) → C h
-/

example (hp : p) (hnp : ¬p) : q := absurd hp hnp
/-
absurd is a tactic
def absurd {a : Prop} {C : Sort u} (h₁ : a) (h₂ : ¬a) : C :=
  False.elim (h₂ h₁)
-/
