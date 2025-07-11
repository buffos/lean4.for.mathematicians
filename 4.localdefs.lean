-- Lean also allows you to introduce "local" definitions using the let keyword.
#check let y := 2 + 2; y * y   -- Nat
#eval  let y := 2 + 2; y * y   -- 16

def twice_double (x : Nat) : Nat :=
  let y := x + x; y * y

#eval twice_double 2   -- 16


-- chaining assignments

#check let y := 2 + 2; let z := y + y; z * z   -- Nat
#eval  let y := 2 + 2; let z := y + y; z * z   -- 64

-- the ; can be ommited when we use a line break

def t (x : Nat) : Nat :=
  let y := x + x
  y * y

/-
although it looks like
let a := t1; t2 is similar to (fun a => t2) t1
they are not the same.
The first is an abbreviation. It says, where ever you see a, replace it with t1
-/

def foo := let a := Nat; fun x : a => x + 2

/-
def bar := (fun a => fun x : a => x + 2) Nat
does not type check because x + 2 is not defined for every type
but if we add a type class constraint as follows it does
def bar := (fun (a : Type) [Add a] => fun x : a => x + 2) Nat
 which says that bar should follow the Add interface
-/
