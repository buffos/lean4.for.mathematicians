
-- Anonymous Functions

#check fun (x : Nat) => x + 5   -- Nat → Nat
#check λ (x : Nat) => x + 5     -- λ and fun mean the same thing
#check fun x => x + 5     -- Nat inferred
#check λ x => x + 5       -- Nat inferred
-- evaluate
#eval (λ x : Nat => x + 5) 10    -- 15
#check fun x : Nat => fun y : Bool => if not y then x + 1 else x + 2
#check fun (x : Nat) (y : Bool) => if not y then x + 1 else x + 2
#check fun x y => if not y then x + 1 else x + 2   -- Nat → Bool → Nat

-- defining functions

def f (n : Nat) : String := toString n -- parametric version (no pattern matching)
def g (s : String) : Bool := s.length > 0

-- pass functions as parameters

#check fun (g : String → Bool) (f : Nat → String) (x : Nat) => g (f x)

-- this is polymorphic function composition
#check fun (α β γ : Type) (g : β → γ) (f : α → β) (x : α) => g (f x)
