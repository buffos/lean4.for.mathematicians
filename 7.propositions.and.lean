def Implies (p q : Prop) : Prop := p → q -- the arrow is with \ + imp or to
#check And     -- Prop → Prop → Prop
#check Or      -- Prop → Prop → Prop
#check Not     -- Prop → Prop
#check Implies -- Prop → Prop → Prop

variable (p q r : Prop)
#check And p q                      -- Prop
#check Or (And p q) r               -- Prop
#check Implies (And p q) (And q p)  -- Prop


#print And

structure myAnd (a b : Prop) where
  intro ::  -- This changes the constructor name to 'intro'
  left: a
  right: b

/-
Suppose you want to construct myAnd (1 = 1) (2 = 2):
def ex : myAnd (1 = 1) (2 = 2) :=
  myAnd.intro rfl rfl

You can also use Lean’s “record update” style:

def ex2 : myAnd (1 = 1) (2 = 2) :=
  { left := rfl, right := rfl }


-/

#print myAnd

-- Towards a Proof System
structure Proof (p : Prop) : Type where
  proof : p
#check Proof   -- Proof : Prop → Type

-- axiom that AND is commutative
axiom and_comm1 (p q : Prop) : Proof (Implies (And p q) (And q p))

variable (p q : Prop)
#check and_comm1 p q     -- Proof (Implies (And p q) (And q p))

-- then build proofs From a proof of Implies p q and a proof of p, we obtain a proof of q.
axiom modus_ponens : (p q : Prop) → Proof (Implies p q) → Proof p → Proof q
-- if we have a proof p as a hypothesis and we find a proof then we created a proof of p → q
axiom implies_intro : (p q : Prop) → (Proof p → Proof q) → Proof (Implies p q)

/- if we combine p:Prop  and interpret it as a type of its proof, then t:p means t is a proof of p
This is the approach followed in the Calculus of Constructions, and hence in Lean as well

 The fact that the rules for implication in a proof system for natural deduction correspond exactly to the rules governing abstraction and application for functions is an instance of the Curry-Howard isomorphism sometimes known as the propositions-as-types paradigm.

 To create a proof we need to create a term t : p

 -/

theorem t1 : p → q → p := fun hp : p => fun _ : q => hp
/-
What we did here

Imaging we have
fun x: a => fun y : b => x   this is (x,y) -> x
and this is a type of a -> b -> a
where a and b are TYPES

In our case p and q are Prop (which is the lowest type == Sort 0)

-/

/-
How this works?

Propositions = Types
p and q aren't booleans – they're types representing logical statements.

Proofs = Terms/Programs
A proof of p → q → p is a function that converts any proof of p into a proof of q → p.

Verification = Type Checking
Lean checks if your function's type signature matches the theorem's type.

We created a function, with input p and q (proofs of p and q) and it returns a proof of p which is what we want

-/

-- we can also write it as
theorem t1' (hp : p) (_ : q) : p := hp

axiom hh_poly : ∀ (p : Prop), p

theorem t2_poly : q → p := fun _ => hh_poly p

-- example is a theorem without a name
#check And p q
example (hp : p) (hq : q) : p ∧ q := And.intro hp hq
-- what the example says.
-- if we get a proof of p (hp) and a proof of q (hq) then we can proof p and q by using
-- And.intro hp hq which build a proof of a and b

#check fun (hp : p) (hq : q) => And.intro hp hq

-- prove p ∧ q → q ∧ p
example (h: p ∧ q) : q ∧ p := And.intro (And.right h) (And.left h)

-- prove if we now p ∧ q then we can prove q ∧ p ∧ q
example (h: p ∧ q) : q ∧ p ∧ q :=
   ⟨h.right, ⟨h.left, h.right⟩⟩
   /-
this is equivalent to:
example (h : p ∧ q) : q ∧ p ∧ q :=
  And.intro
    h.right
    (And.intro
        h.left
        h.right)

lean infers the constructor to use from the signature
   -/

variable (xs : List Nat)

#check List.length xs
#check xs.length

-- what happened here?
-- when Foo has a function bar, so Foo.bar is a thing and we apply Foo.bar to e like Foo.bar e
-- then we are able to write e.bar
-- this is why previously instead of And.right h (we want the right part of h) we write h.right
