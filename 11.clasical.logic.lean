/-
The passage explains a key distinction in Lean 4 between **constructive logic** (default in Lean) and **classical logic** (optional, added via the `classical` namespace). Here's a breakdown:

---

### **1. Constructive Logic in Lean**
Lean is based on **constructive type theory**, where proofs are computational procedures. This aligns with the **propositions-as-types correspondence** (Curry-Howard isomorphism):
- **Propositions** = Types
- **Proofs** = Programs (values inhabiting those types)

**Examples**:
- A proof of `P ∧ Q` is a pair `(p, q)` where `p : P` and `q : Q`.
- A proof of `P → Q` is a function that transforms a proof of `P` into a proof of `Q`.
- A proof of `P ∨ Q` is either `inl(p)` (left disjunct) or `inr(q)` (right disjunct).

**Elimination rules** (e.g., case analysis on `P ∨ Q`) have computational meaning:
```lean
example (P Q : Prop) (h : P ∨ Q) : ... :=
  match h with
  | inl p => ...  -- Use proof of P
  | inr q => ...  -- Use proof of Q
```
This ensures every proof has "computational content"—you can extract values or algorithms from it.

---

### **2. Classical Logic Adds Non-Constructive Principles**
Classical logic introduces principles like the **law of excluded middle (LEM)**:
`p ∨ ¬p` (for any proposition `p`).

- **Constructive issue**: To prove `p ∨ ¬p`, you must either provide a proof of `p` or a proof of `¬p`. LEM asserts this disjunction without specifying which side holds, making it non-constructive.
- **Computational problem**: There’s no program that decides `p` or `¬p` for arbitrary `p` (this would solve the halting problem, etc.).

In Lean, classical logic is **not built-in**. You enable it by opening the `classical` namespace:
```lean
open classical

example (p : Prop) : p ∨ ¬p :=
  em p  -- Proof of excluded middle
```
This adds axioms like `em` (excluded middle) and `dne` (double-negation elimination), allowing classical reasoning (e.g., proof by contradiction).

---

### **3. Why the Distinction Matters**
- **Constructive proofs** are "executable": They can be used to compute values or algorithms.
  Example: A constructive proof of `∃x, P x` gives an explicit `x` and a proof of `P x`.
- **Classical proofs** may lack computational content.
  Example: Using LEM to prove `∃x, P x` might not tell you how to find `x`.

Lean prioritizes constructivity by default, but you can opt into classical reasoning when needed (e.g., for traditional mathematical proofs where computation isn’t the goal).

---

### **4. Practical Implications**
- **Default mode**: Lean’s tactics (like `intro`, `apply`, `cases`) enforce constructive reasoning.
- **Classical mode**: Use `open classical` and tactics like `by_contra` (proof by contradiction) or `em` to invoke LEM.
- **Trade-offs**:
  - Constructive: Ensures computational meaning, but some proofs become harder.
  - Classical: Simplifies proofs but sacrifices algorithmic extraction guarantees.

---

### **Summary**
Lean’s core logic is constructive, reflecting its foundation in type theory and computation. Classical principles like LEM are optional, requiring `open classical` to avoid polluting constructive developments. This design balances flexibility (supporting both styles) with rigor (enforcing computational accountability).
-/

open Classical

variable (p : Prop)
#check em p
-- Diaconescu's theorem: excluded middle from choice, Function extensionality and propositional extensionality.

theorem dne {p: Prop} (h: ¬¬p ) : p :=
  Or.elim (em p)
    (fun hp:p => hp)
    (fun hnp: ¬p => absurd hnp h)

-- using classical reasoning , with byCases (we have 2 cases for p ∨ ¬p)
example (h : ¬¬p) : p :=
  byCases
    (fun h1 : p => h1) -- case p
    (fun h1 : ¬p => absurd h1 h) -- case ¬p (if h1 is a proof of not p, then we have proofs of ¬p = h1 and ¬(¬p)=¬h1)

-- using classical reasoning and contradiction
open Classical
variable (p : Prop)

example (h : ¬¬p) : p :=
  byContradiction
    (fun h1 : ¬p => show False from h h1)

example (h : ¬(p ∧ q)) : ¬p ∨ ¬q :=
  Or.elim (em p)
    (fun hp : p => Or.inr (show ¬q from fun hq : q => h ⟨hp, hq⟩))
    (fun hp : ¬p => Or.inl hp)

/-  Explanation
 fun hq : q => h ⟨hp, hq⟩ tells us,
 if we have a proof of q (and since we already have a proof of p in the outer context)
 ⟨hp, hq⟩ will create the p ∧ q and h ⟨hp, hq⟩
 Note that h : ¬(p ∧ q) is equivalent to h : (p ∧ q) → False.
 so the function gets q → (p ∧ q) → False so q → False and this is the definition ¬q
 and since we want it on the right side of the Or, we Create an or with the right side set as such

 So here is an example that we use `constructive logic` to create the `contradictions` BUT
 `classical logic` to split the problem in two cases.
-/
