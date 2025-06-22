variable (p q r: Prop)

structure MyIff (a b : Prop) : Prop where
  /-- If `a → b` and `b → a`, then `a ↔ b`. -/
  intro ::
  mp : a → b  -- Forward direction (modus ponens)
  mpr : b → a -- Reverse direction (modus ponens reverse)

-- so iff keeps to proofs a->b and b->a and is actually syntactic sugar for a ↔ b
-- MyIff a b is if and only if

example (hpq: p → q) (hqp : q → p) : p ↔ q := Iff.intro hpq hqp

theorem and_swap_short : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (fun h => ⟨h.right, h.left⟩)
    (fun h => ⟨h.right, h.left⟩)

-- or in the long from

theorem and_swap : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (fun h : p ∧ q => -- if h is of this form
     show q ∧ p from And.intro (And.right h) (And.left h)) -- which is the same as And.intro h.right h.left
    (fun h : q ∧ p =>
     show p ∧ q from And.intro (And.right h) (And.left h)) -- which is the same as And.intro h.left h.right

section example1
  variable (h : p ∧ q)  -- h is a proof of p ∧ q
  #check and_swap p q
  #check Iff.mp (and_swap p q)
  example : q ∧ p := Iff.mp (and_swap p q) h
  -- and_swap will take h and produce p ∧ q ↔ q ∧ p
  -- we get Iff.mp which gives the -> part  meaning p ∧ q →r q ∧ p
  -- and since the argument is  p ∧ q we get as a result q ∧ p
end example1
