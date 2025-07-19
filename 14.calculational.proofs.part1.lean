/-
We will discuss calculational proofs.


 **Calculational proofs** (`calc` blocks in Lean) are not necessary for proving things, but they offer important practical and educational benefits. Here’s a summary of **why you might want to use them**:

---

## **Benefits of calculational (`calc`) proofs:**

### 1. **Readability**

* **Calculational proofs mirror mathematical style:**
  They look almost exactly like “equational reasoning” in textbooks:

  ```
  a = b    [by ...]
    = c    [by ...]
    = d    [by ...]
  ```
* This helps others (and your future self!) **quickly follow the flow of equalities**.

---

### 2. **Less Boilerplate**

* No need to nest `trans` calls (which get unwieldy for long chains).
* No need to invent lots of intermediate lemma names (`have h1`, `have h2`, ...).

---

### 3. **Fewer Parentheses and Transpositions**

* No need to carefully order parentheses as with `.trans(.trans(...))`.
* The proof reads as a straightforward sequence.

---

### 4. **Direct alignment with the “mathematical narrative”**

* Especially helpful for beginners and for formalizing textbook proofs.
* When collaborating or teaching, it’s easier for others to verify your reasoning.

---

### 5. **Simplicity in Chaining**

* Each step states **exactly which justification/hypothesis** is used.
* The `_` placeholder makes it easy to chain from the previous line.

---

### **Are there any drawbacks?**

* For very complex proofs, you might need intermediate `have` steps anyway.
* For proofs with case splits or complex rewrites, tactics or `have` may be more flexible.

---

## **Summary Table**

| Proof Style            | Pros                             | Cons                                     |
| ---------------------- | -------------------------------- | ---------------------------------------- |
| `calc` (calculational) | Readable, concise, textbook-like | Less flexible for complex branching      |
| `have`/`trans` chain   | Fine-grained control, flexible   | Verbose, less readable for simple chains |

---

## **In short:**

> **Calculational proofs make simple equational chains easier to read, easier to write, and closer to math as seen in textbooks.**
> They’re not mandatory—but are very handy for many proofs!
-/

-- simple example without calculational proof

section
variable (a b c d e : Nat)

example
    (h1 : a = b)
    (h2 : b = c + 1)
    (h3 : c = d)
    (h4 : e = 1 + d) :
    a = e :=

  have h5 : c + 1 = d + 1 := congrArg Nat.succ h3
  have h6 : d + 1 = 1 + d := Nat.add_comm d 1
  have h7 : 1 + d = e := Eq.symm h4
  h1.trans (h2.trans (h5.trans (h6.trans h7)))
end

-- the same example with calculational proof
section
variable (a b c d e : Nat)

theorem T1
    (h1 : a = b)
    (h2 : b = c + 1)
    (h3 : c = d)
    (h4 : e = 1 + d) :
    a = e :=
  calc
    a = b      := h1
    _ = c + 1  := h2
    _ = d + 1  := congrArg Nat.succ h3
    _ = 1 + d  := Nat.add_comm d 1
    _ = e      := Eq.symm h4

end

-- the same example using rewrites

section

variable (a b c d e : Nat)

theorem T2
    (h1 : a = b)
    (h2 : b = c + 1)
    (h3 : c = d)
    (h4 : e = 1 + d) :
    a = e :=
  calc
    a = b      := by rw [h1]
    _ = c + 1  := by rw [h2]
    _ = d + 1  := by rw [h3]
    _ = 1 + d  := by rw [Nat.add_comm]
    _ = e      := by rw [h4]

end

/-
Let's break down what `rw` does in Lean and why it's so powerful.

---

## **What does `rw` mean in Lean?**

* **`rw`** stands for **rewrite**.
* It is a tactic used to **replace** one side of an equality (or other rewrite rule) with the other, everywhere it matches in the current goal.

---

## **How does `rw` work?**

Given a goal like `a = e`, and a fact `h1 : a = b`,

* `rw [h1]` **replaces every occurrence of `a` with `b`** in the goal (because `h1` says `a = b`).

### **What does it actually do?**

* **Searches** the current goal for terms that match the left side of your lemma/equality.
* **Replaces** those terms with the right side, using the equality as justification.

**It can also work in reverse** if you add `←` (e.g., `rw [← h1]` rewrites using `b = a`).

---

### **Example step in your proof:**

```lean
a = b      := by rw [h1]        -- uses h1 : a = b
_ = c + 1  := by rw [h2]        -- uses h2 : b = c + 1
_ = d + 1  := by rw [h3]        -- uses h3 : c = d (so c + 1 = d + 1)
_ = 1 + d  := by rw [Nat.add_comm] -- uses commutativity: d + 1 = 1 + d
_ = e      := by rw [h4]        -- uses h4 : e = 1 + d (so 1 + d = e)
```

---

## **What is happening in the background?**

* Each `rw` call applies the lemma/equality as a **substitution rule** to the current goal.
* Lean checks for matching subexpressions and substitutes accordingly.
* The goal is updated after each rewrite.

---

## **Why is this useful?**

* **Automation:**
  `rw` can chain through complicated equalities and is much faster than doing it all by hand.
* **Clarity:**
  You explicitly state which facts/lemmas you are using at each step.
* **Consistency:**
  You avoid mistakes in substitution; Lean handles the logic.

---

## **In summary:**

| Command    | What it does                                            |
| ---------- | ------------------------------------------------------- |
| `rw [h]`   | Replaces lhs of `h : lhs = rhs` with `rhs` in your goal |
| `rw [← h]` | Replaces rhs with lhs (uses equality in the reverse)    |

---

## **In plain words:**

> **`rw [h]`** means:
> "Rewrite the current goal using the equality (or lemma) `h` as a substitution rule, wherever it fits."

---
-/

-- we can use sequential rewrites

variable (a b c d e : Nat)

theorem T3
    (h1 : a = b)
    (h2 : b = c + 1)
    (h3 : c = d)
    (h4 : e = 1 + d) :
    a = e :=
  calc
    a = d + 1  := by rw [h1, h2, h3]
    _ = 1 + d  := by rw [Nat.add_comm]
    _ = e      := by rw [h4]

-- or even more compact
variable (a b c d e : Nat)

theorem T4
    (h1 : a = b)
    (h2 : b = c + 1)
    (h3 : c = d)
    (h4 : e = 1 + d) :
    a = e :=
  by rw [h1, h2, h3, Nat.add_comm, h4]

  /-
  Absolutely! Let’s break down the **`simp`** tactic in Lean—what it does, how it’s used, and how it works step by step, especially in your example.

---

## **What does `simp` do?**

* **`simp`** stands for **simplify**.
* It is a tactic that **automatically rewrites the goal** using:

  * *All* lemmas marked with `@[simp]` in the environment,
  * Any *equalities* or lemmas you list explicitly in `[ ... ]`.

**Its goal:** Reduce your goal to something Lean can solve, typically by rewriting and simplifying equalities, arithmetic, and logical connectives.

---

## **How is it used?**

* **`simp`** alone uses all `@[simp]` lemmas.
* **`simp [h1, h2, ...]`** uses the provided equalities/lemmas in addition to built-in simplifications.
* **`simp only [h1, ...]`** restricts to only the listed rules (ignoring global simp lemmas).

---

## **Step-by-step: What happens in your example?**

```lean
variable (a b c d e : Nat)

theorem T
    (h1 : a = b)
    (h2 : b = c + 1)
    (h3 : c = d)
    (h4 : e = 1 + d) :
    a = e :=
  by simp [h1, h2, h3, Nat.add_comm, h4]
```

### **Let’s see how Lean proceeds:**

1. **Goal:**
   `a = e`

2. **Available facts:**

   * `h1 : a = b`
   * `h2 : b = c + 1`
   * `h3 : c = d`
   * `h4 : e = 1 + d`
   * `Nat.add_comm`: For all `m n`, `m + n = n + m`

3. **What does `simp [h1, h2, h3, Nat.add_comm, h4]` do?**

   * **First,** it **rewrites `a` to `b`** (by `h1`):
     Now the goal is `b = e`
   * **Then,** it **rewrites `b` to `c + 1`** (by `h2`):
     Now the goal is `c + 1 = e`
   * **Then,** it **rewrites `c` to `d`** (by `h3`):
     Now the goal is `d + 1 = e`
   * **Then,** it **rewrites `d + 1` to `1 + d`** (by `Nat.add_comm`):
     Now the goal is `1 + d = e`
   * **Finally,** it **rewrites `e` to `1 + d`** (by `h4`, which is `e = 1 + d`).
     Since both sides are now `1 + d`, Lean recognizes this is trivial and closes the goal.

**Note:**
If the left and right sides become definitionally equal (`1 + d = 1 + d`), Lean automatically accepts the proof as finished.

---

## **What’s special about `simp`?**

* It **tries all possible combinations** (up to a reasonable depth) to find a sequence of rewrites that solves the goal.
* It’s much more powerful than `rw`, as it can use many lemmas and try different combinations automatically.
* If you add the `!` flag (`simp!`), it’s even more aggressive.

---

## **Summary Table**

| Tactic                | What it does                                        |
| --------------------- | --------------------------------------------------- |
| `simp`                | Uses all `[simp]` lemmas                            |
| `simp [h1, ...]`      | Adds the given lemmas to the simp set for this goal |
| `simp only [h1, ...]` | *Restricts* to just these lemmas                    |


Order of lemmas inside the brackets does not matter.
---

## **In short:**

> **`simp` automatically rewrites and simplifies your goal using all relevant facts and lemmas you give it, making proof steps much shorter and easier for straightforward equational or logical reasoning.**

  -/
