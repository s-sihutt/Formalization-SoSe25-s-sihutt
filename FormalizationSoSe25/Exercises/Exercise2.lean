import Mathlib.Tactic

-- Let's do some basic tactics exercises.

section rw

/-
In this section, only use the `rw` tactic.
You will also need the following functions: -/
#check mul_comm
#check mul_assoc

example (a b c : ℝ) : a * b * c = b * (a * c) := by
  rw [mul_comm a b]
  rw [mul_assoc]


example (a b c : ℝ) : c * b * a = b * (a * c) := by
  rw [mul_comm c b]
  rw [mul_comm a c]
  rw [mul_assoc]

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  ring

example (a b c : ℝ) : a * b * c = b * c * a := by
  ring

example (a b c : ℝ) : a * (b * c) = b * (c * a) := by
  ring

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  ring

example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h']
  rw [← mul_assoc]
  rw [h]
  rw [mul_assoc]



example (a b c d e f : ℝ) (h : b * c = e * f) : a * b * c * d = a * e * f * d := by
  rw [mul_assoc a b c]
  rw [h]
  rw [← mul_assoc]

-- For this next exercise, you should also need:
#check sub_self

example (a b c d : ℝ) (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 := by
  rw [hyp]
  rw [hyp']
  rw [mul_comm a b]
  rw [sub_self]

end rw

section logic

/-
For the following exercises, use the tactics:
- `intro`
- `exact`
- `constructor`
- `left`
- `right`
- `apply`
- `obtain`
- `rcases`
- `rw`
-/

example (P Q R S : Prop) (h : P → R) (h' : Q → S) : P ∧ Q → R ∧ S := by
  intro h2
  obtain ⟨pq, rs⟩ := h2
  constructor
  · exact h pq
  · exact h' rs


example (α : Type) (P Q : α → Prop) : (∃ x, P x ∧ Q x) → ∃ x, Q x ∧ P x := by
  intro h3
  obtain ⟨x, hP, hQ⟩ := h3
  use x

-- For the next exercise you also need the function
#check le_trans

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
  exact le_trans h₀ h₁

-- For the next exercise, you can also use `ring`.
-- You will also need the following:
#check add_zero

example (a b : ℝ) : a = b ↔ b - a = 0 := by
  constructor
  · intro h1
    rw[h1]
    rw[sub_self b]
  · intro h1
    rw[← add_zero b]
    rw[← sub_self a]
    rw[← add_sub_assoc b a a]
    rw[add_comm b a]
    rw[add_sub_assoc a b a]
    rw[h1]
    rw[add_zero]


example (P Q R : Prop) : P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := by
  sorry




example (α : Type) (P Q : α → Prop) : (∀ x, P x ∧ Q x) ↔ ((∀ x, Q x) ∧ (∀ x, P x)) := by
 sorry

end logic
