/- Define constants-/

def m: Nat := 1 -- m is a natural number

inductive MyNat where
    | zero : MyNat
    | succ : MyNat → MyNat -- the arrow is →

def m1: MyNat := MyNat.succ (MyNat.succ MyNat.zero)

#eval m1

#check MyNat.rec -- atomatically generated function

-- Ninth Peano axiom of Natural Numbers. If K is a set that 0 is in K
-- and for every natural number n, n ∈ K implies that S(n) also is in K then K === Nat

/-  This is the induction principle for Nat
Nat.rec.{u} {motive : Nat → Sort u}
  (zero : motive zero)
  (succ : (n : Nat) → motive n → motive n.succ) -- this tells how to construct the successor
  (t : Nat) :
  motive t
  -/


/-
"No confusion" is the principle that:
 - Different constructors of an inductive type build distinct values (disjointedness)
 - If two values built with the same constructor are equal, their fields/arguments must also be equal (injectivity)

For Nat (natural numbers), this means:
 - 0 ≠ succ n (disjointness)
 - succ n₁ = succ n₂ implies n₁ = n₂ (injectivity)
-/
def NoConfusion : Nat → Nat → Prop
  | 0, 0 => True -- only one zero
  | 0, _ + 1 | _ + 1, 0 => False -- 0 does not have a successor
  | n + 1, k + 1 => n = k -- if two number have the same successor then they are equal.


theorem noConfusionDiagonal (n : Nat) :
    NoConfusion n n :=  -- this is what we want to prove
  Nat.rec True.intro (fun _ _ => rfl) n -- True.intro is True constructor

-- how the proof works:
-- Nat.rec os the induction principle for Natural numbers
-- for the zero case NoConfusion 0 0 is true by definition , so we use True.intro to express that
-- the next argument is the successor n
-- for succ case in Nat.rec we have to arguments (n: Nat) and (motive n)
-- the first in our case in n, and the second is NoConfusion n n (which is motive n)
-- then we need to prove the for n+1. Son NoConfusion (n+1) (n+1) => n = n.
-- This last proposition is proven by equality reflexivity. rfl

-- Now we prove the more general

theorem noConfusion (n k : Nat) (eq : n = k) :
    NoConfusion n k :=
  eq ▸ noConfusionDiagonal n

-- What does eq ▸ noConfusionDiagonal n mean?
-- This uses Lean’s substitution/rewrite operator ▸ (you may also see eq.mp or eq.subst elsewhere).
-- what it does, it takes a proof of Pn and using the eq it rewrites for Pk
-- in our case noConfusionDiagonal n : NoConfusion n n and with the substitution
-- it makes NoConfusion n n to No confusion n k

theorem succ_injective : n + 1 = k + 1 → n = k :=
  noConfusion (n + 1) (k + 1)

  theorem succ_not_zero : ¬n + 1 = 0 :=
  noConfusion (n + 1) 0


-- define addition and subtraction in MyNats

def MyNat.add : MyNat → MyNat → MyNat
    | .zero , m => m
    | .succ n , m => succ (MyNat.add n m)

def MyNat.sub : MyNat → MyNat → MyNat
    | n , .zero => n
    | .zero , _ => .zero
    | succ n , succ m => sub n m

def MyNat.mul : MyNat → MyNat → MyNat
  | .zero,      _ => .zero
  | .succ n, m => .add (.mul n m)  m

def MyNat.leq : MyNat → MyNat → Bool
  | .zero,     _         => true
  | .succ _,   .zero      => false
  | .succ n,   .succ m    => leq n m

#eval MyNat.leq MyNat.zero (MyNat.succ (MyNat.succ MyNat.zero))
#eval MyNat.leq (MyNat.succ (MyNat.succ MyNat.zero)) MyNat.zero

partial def MyNat.div (n m : MyNat) : MyNat :=
  let rec aux (n acc : MyNat) : MyNat :=
    match MyNat.leq m n with
      | true  => aux (MyNat.sub n m) (MyNat.succ acc)
      | false => acc
  aux n MyNat.zero

def myTwo := MyNat.succ (MyNat.succ MyNat.zero)
def myFour := MyNat.succ (MyNat.succ (MyNat.succ (MyNat.succ MyNat.zero)))

#eval MyNat.div myFour myTwo
#eval MyNat.div myTwo myTwo
