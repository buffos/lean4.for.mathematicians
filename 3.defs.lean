-- this is defining double with parameters
def double (x : Nat) : Nat :=  x + x
#eval double 3    -- 6

-- alternative way of defining

def double2 : Nat → Nat :=  fun x => x + x

#eval double2 3    -- 6


-- another way with inferred types

def double3 := fun (x : Nat) => x + x

-- define constants

def pi := 3.141592654

-- multiple input parameters

def add (x y : Nat) :=
  x + y

#eval add 3 2               -- 5

-- but we can also separate them

def add2 (x : Nat) (y : Nat) :=
  x + y

#eval add2 (double 3) (7 + 9)  -- 22

-- use if then else
def greater (x y : Nat) :=
  if x > y then x
  else y


-- functions that take a function
def doTwice (f : Nat → Nat) (x : Nat) : Nat :=
  f (f x)

#eval doTwice double 2

-- polymorphic function

def comp (α β γ : Type) (g : β → γ) (f : α → β) (x : α) : γ := g (f x)
def square (x : Nat) : Nat := x * x

#eval comp Nat String Bool (fun s => s.length > 3) (fun n => n.repr) 42
#eval comp Nat Nat Nat double square 3
