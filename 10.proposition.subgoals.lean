variable (p q : Prop)

example (h : p ∧ q) : q ∧ p :=
  have hp : p := h.left -- this is hp <-- h.left or (fun (hp: p) => .....) h.left
  have hq : q := h.right
  show q ∧ p from And.intro hq hp

-- making proofs easier to read
-- have h : p := s; t is the same as (fun (h:p) => t) s
-- in words s will be applied to the fun (h:p) , this means s is a proof of p and takes the place of h
-- t is a consequence of the proof of p

--  reasoning backwards

variable (p q : Prop)

example (h : p ∧ q) : q ∧ p :=
  have hp : p := h.left
  suffices hq : q from And.intro hq hp -- this says it enough to show no w that hq is a proof o f q
  show q from And.right h -- we now show q has a proof which is derived from the right part of h
