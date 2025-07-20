-- A brief intermezzo of what Trans type class is

/-
## What is a type class in lean4?

In **Lean4**, a **type class** is a way to define interfaces for polymorphic functions. It groups types based on shared operations (like `Add` for types with `+`). Instances provide implementations for specific types.

### Key Points:
1. **Ad-hoc Polymorphism**: Enables different implementations for different types.
2. **Inference**: Lean automatically finds the right instance.
3. **Hierarchy**: Can extend other type classes (e.g., `Ring` extends `Add`).

### Imperative Analog (e.g., Java/C#):
- **Interfaces**: Similar but lack ad-hoc polymorphism (must be implemented explicitly per type).
- **No Inference**: Manual passing/instantiation required.
- **Less Flexible**: No automatic instance resolution or hierarchy like type classes.

### Example (Lean4):
```lean
class Add (α : Type) where
  add : α → α → α

instance : Add Nat where
  add := Nat.add
```

Now we will make it specific for Trans type class
-/

/-
Absolutely! The `Trans` type class in Lean is a **key ingredient** in how `calc` proofs and many other forms of *chaining* are automated.

---

## **What is the `Trans` type class?**

It’s a way to encode the **transitivity property** of relations in Lean.
If you have a relation `R` (for example, equality, ≤, <),
`Trans R` tells Lean that if `a R b` and `b R c`, then `a R c`.

---

### **Definition (Simplified):**

In Lean 4’s core libraries, the class is essentially:

```lean
class Trans (R : α → α → Prop) where
  trans : ∀ {a b c : α}, R a b → R b c → R a c
```

* **`R`**: a binary relation (like `=`, `<`, `≤`)
* **`trans`**: a function that, given proofs of `a R b` and `b R c`, produces a proof of `a R c`.

---

## **How is `Trans` used?**

* Lean’s `calc` block **relies on `Trans` instances** for chaining steps:

  * When you write

    ```lean
    calc
      a = b := h1
      _ = c := h2
      _ = d := h3
    ```

    Lean looks for a `Trans` instance for `=` (equality) to justify the steps.

* Many standard relations have `Trans` instances, e.g.:

  * Equality: If `a = b` and `b = c`, then `a = c`.
  * Less-than: If `a < b` and `b < c`, then `a < c`.
  * Less-than-or-equal: If `a ≤ b` and `b ≤ c`, then `a ≤ c`.

---

### **Example: The `Trans` instance for equality**

```lean
instance : Trans (@Eq α) where
  trans := Eq.trans
```

* `@Eq α` is the equality relation on type `α`.
* `Eq.trans` is the usual transitivity of equality.

### **Example: The `Trans` instance for less-than**

```lean
instance : Trans (@LT.lt α _) where
  trans := lt_trans
```

* `lt_trans` is a lemma: `a < b → b < c → a < c`.

---

## **How do you use `Trans`?**

* Usually, you **don’t use it directly**.
* It’s used **behind the scenes** in `calc` and in tactics that chain relations.
* If you define your own relation and want to use it with `calc`, you can provide a `Trans` instance:


## **Summary Table**

| Relation | `Trans` instance definition     | What it means                        |
| -------- | ------------------------------- | ------------------------------------ |
| `=`      | `instance : Trans (@Eq α)`      | If `a = b` and `b = c`, then `a = c` |
| `<`      | `instance : Trans (@LT.lt α _)` | If `a < b` and `b < c`, then `a < c` |
| `≤`      | `instance : Trans (@LE.le α _)` | If `a ≤ b` and `b ≤ c`, then `a ≤ c` |

---

## **In short:**

> **`Trans` is a type class that provides the “chaining” (transitivity) law for relations. It powers `calc` proofs and makes equational and order chaining automatic.**

-/

-- Example of a custom transitive relationship

-- ## defining divisibility
def divides (x y : Nat) : Prop := ∃ k, k * x = y -- We say x divides y if there exists a k such that k * x = y

-- ## Transitivity of divides
def divides_trans (h₁ : divides x y) (h₂ : divides y z) : divides x z :=
  let ⟨k₁, d₁⟩ := h₁
  -- **The brackets `⟨k₁, d₁⟩ := h₁` mean “unpack the existential proof `h₁` into its witness `k₁` and the associated property/proof `d₁`**
  let ⟨k₂, d₂⟩ := h₂ -- same as before
  -- so we have k₁ * x = y from h1 and k₂ * y = z from h2
  ⟨k₁ * k₂, by rw [Nat.mul_comm k₁ k₂, Nat.mul_assoc, d₁, d₂]⟩
-- the goal says, We claim k₁ * k₂ is the multiplier so that x divides z; here’s a chain of rewrites to prove (k₁ * k₂) * x = z
-- We start from the left side (k₁ * k₂) * x
-- Rewrite using Nat.mul_comm k₁ k₂ this changes **(k₁ * k₂) * x to (k₂ * k₁) * x**
-- Rewrite using Nat.mul_assoc changes **(k₂ * k₁) * x to k₂ * (k₁ * x)**
-- Rewrite using d₁ which is **k₁ * x = y** so **k₂ * (k₁ * x)** becomes **k₂ * y**
-- Rewrite using d₂  which is the proof of **k₂ * y = z** so **k₂ * y** becomes **z**

def divides_mul (x : Nat) (k : Nat) : divides x (k*x) := ⟨k, rfl⟩
/-
### **What is this function saying?**

* For any two natural numbers `x` and `k`,
* The number `x` **divides** `k * x`.

So, to prove `divides x (k * x)`, you must:

* Exhibit a witness `k : Nat`
* Such that `k * x = k * x` (which is obviously true)

---

## **Step by Step:**

1. **The witness:**
   * Here, `k` is exactly the multiplier you used to get `k * x`.
2. **The proof:**
   * `rfl` stands for **reflexivity** of equality, i.e., `k * x = k * x` is always true.
3. **The angle brackets `⟨k, rfl⟩`:**
   * This is Lean's way of **constructing an existential proof**:
     "There exists a `k` such that `k * x = k * x`."
-/

instance : Trans divides divides divides where
  trans := divides_trans

  /-
## **What is `Trans`?**

Recall Trans in general is:

```lean
class Trans (R₁ : α → β → Prop) (R₂ : β → γ → Prop) (R₃ : α → γ → Prop) where
  trans : ∀ {a : α} {b : β} {c : γ}, R₁ a b → R₂ b c → R₃ a c
```

This general definition allows **mixed transitivity**

So instance : Trans divides divides divides where ... says
“If divides x y and divides y z, then divides x z by this transitivity law.”
## trans := divides_trans

This tells Lean that the method to prove transitivity is divides_trans

  -/

#check @Trans

/-
@Trans : {α : Sort u_4} →
  {β : Sort u_5} →
    {γ : Sort u_6} →
      (α → β → Sort u_1) →
        (β → γ → Sort u_2) →
          outParam (α → γ → Sort u_3) → Sort (max (max (max (max (max (max 1 u_1) u_4) u_5) u_6) u_2) u_3)
-/
