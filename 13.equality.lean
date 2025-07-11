/-
We will explain later HOW equality is defined from the primitives of Lean's logical framework.
Now we will explain only how to use it.
-/

-- * a fundamental property of equality is that it is an equivalence relation
-- we see that equality is reflective, symmetric and transitive

#check Eq.refl
#check Eq.symm
#check Eq.trans

-- We can make the output easier to read by telling Lean not to insert the implicit arguments (which are displayed here as metavariables)
/-
In Lean 4, the @ symbol is used for explicitly specifying arguments to functions or constructors, particularly when dealing with functions
 or constructors that have implicit arguments or are defined with type classes. It essentially tells the Lean compiler to treat the subsequent
argument as a regular, explicit argument, rather than inferring it implicitly

Here's a more detailed explanation:

**Implicit Arguments:**
Lean 4 often uses implicit arguments, which are automatically inferred by the compiler based on the context.

**Explicit Arguments:**
When you use the @ symbol before an argument, you are telling Lean to treat that argument
 as an explicit argument, even if it would normally be implicit.

**Type Classes:**
Type classes in Lean 4 are a way to group types based on shared properties. When using functions or constructors defined within a type class,
 you might need to explicitly specify which instance of the type class you are referring to, and this is often done with the @ symbol.

**Example:**
Let's say you have a function f with an implicit argument α and an explicit argument x:

```lean
def f {α : Type} (x : α) : α := x
```

If you want to call f with a specific type for α, you would use the @ symbol:

```lean
#eval f @Int 10  -- Explicitly specifies Int as the type for α
```

Without the @ symbol, Lean might infer the type based on the context, or it might give an error if it can't be inferred.
The @ symbol removes any ambiguity and allows you to precisely control the arguments passed to the function.
-/

universe u

#check @Eq.refl.{u}
#check @Eq.symm.{u}
#check @Eq.trans.{u}

-- The inscription .{u} tells Lean to instantiate the constants at the universe u.
-- Thus, for example, we can specialize the example from the previous section to the equality relation:

variable (α : Type) (a b c d : α)
variable (hab : a = b) (hcb : c = b) (hcd : c = d)

example : a = d :=
  Eq.trans (Eq.trans hab (Eq.symm hcb)) hcd


-- We can also use the projection notation:
example : a = d := (hab.trans hcb.symm).trans hcd


/- Reflexivity is more powerful than it looks. Recall that terms in the Calculus of Constructions have a computational interpretation,
and that the logical framework treats terms with a common reduct as the same.
 As a result, some nontrivial identities can be proved by reflexivity:
-/
variable (α β : Type)

example (f : α → β) (a : α) : (fun x => f x) a = f a := Eq.refl _
example (a : α) (b : β) : (a, b).1 = a := Eq.refl _
example : 2 + 3 = 5 := Eq.refl _

-- This feature of the framework is so important that the library defines a notation rfl for Eq.refl _:

example (f : α → β) (a : α) : (fun x => f x) a = f a := rfl
example (a : α) (b : β) : (a, b).1 = a := rfl
example : 2 + 3 = 5 := rfl

/-
Equality is much more than an equivalence relation, however. It has the important property that every assertion respects the equivalence,
in the sense that we can substitute equal expressions without changing the truth value.
That is, given h1 : a = b and h2 : p a, we can construct a proof for p b using substitution: Eq.subst h1 h2.
-/
example (α : Type) (a b : α) (p : α → Prop)
        (h1 : a = b) (h2 : p a) : p b :=
  Eq.subst h1 h2

example (α : Type) (a b : α) (p : α → Prop)
    (h1 : a = b) (h2 : p a) : p b :=
  h1 ▸ h2


/-
The triangle in the second presentation is a macro built on top of Eq.subst and Eq.symm, and you can enter it by typing \t.

The rule Eq.subst is used to define the following auxiliary rules, which carry out more explicit substitutions.
They are designed to deal with applicative terms, that is, terms of form s t.
 Specifically, congrArg can be used to replace the argument, congrFun can be used to replace the term that is being applied,
 and congr can be used to replace both at once.
-/

variable (α : Type)
variable (a b : α)
variable (f g : α → Nat)
variable (h₁ : a = b)
variable (h₂ : f = g)

example : f a = f b := congrArg f h₁
example : f a = g a := congrFun h₂ a
example : f a = g b := congr h₂ h₁

-- Lean's library contains a large number of common identities, such as these:

variable (a b c : Nat)

example : a + 0 = a := Nat.add_zero a
example : 0 + a = a := Nat.zero_add a
example : a * 1 = a := Nat.mul_one a
example : 1 * a = a := Nat.one_mul a
example : a + b = b + a := Nat.add_comm a b
example : a + b + c = a + (b + c) := Nat.add_assoc a b c
example : a * b = b * a := Nat.mul_comm a b
example : a * b * c = a * (b * c) := Nat.mul_assoc a b c
example : a * (b + c) = a * b + a * c := Nat.mul_add a b c
example : a * (b + c) = a * b + a * c := Nat.left_distrib a b c
example : (a + b) * c = a * c + b * c := Nat.add_mul a b c
example : (a + b) * c = a * c + b * c := Nat.right_distrib a b c

/- Note that Nat.mul_add and Nat.add_mul are alternative names for Nat.left_distrib and Nat.right_distrib, respectively.
The properties above are stated for the natural numbers (type Nat).
-/


-- Here is an example of a calculation in the natural numbers that uses substitution combined with associativity and distributivity.
example (x y : Nat) :
    (x + y) * (x + y) =
    x * x + y * x + x * y + y * y :=
  have h1 : (x + y) * (x + y) = (x + y) * x + (x + y) * y :=
    Nat.mul_add (x + y) x y
  have h2 : (x + y) * (x + y) = x * x + y * x + (x * y + y * y) :=
    (Nat.add_mul x y x) ▸ (Nat.add_mul x y y) ▸ h1
  h2.trans (Nat.add_assoc (x * x + y * x) (x * y) (y * y)).symm

/-
Notice that the second implicit parameter to Eq.subst, which provides the context in which the substitution is to occur, has type α → Prop.
Inferring this predicate therefore requires an instance of higher-order unification.
In full generality, the problem of determining whether a higher-order unifier exists is undecidable, and Lean can at best provide imperfect
 and approximate solutions to the problem. As a result, Eq.subst doesn't always do what you want it to.
  The macro h ▸ e uses more effective heuristics for computing this implicit parameter, and often succeeds in situations where applying
Eq.subst fails.

Because equational reasoning is so common and important, Lean provides a number of mechanisms to carry it out more effectively.
The next section offers syntax that allow you to write calculational proofs in a more natural and perspicuous way. But, more importantly,
equational reasoning is supported by a term rewriter, a simplifier, and other kinds of automation. The term rewriter and simplifier are
described briefly in the next section, and then in greater detail in the next chapter.
-/
