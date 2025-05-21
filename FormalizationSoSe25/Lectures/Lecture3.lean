import Mathlib.Tactic

def zz : ℝ → ℝ := fun _ => 0

section review


/-
Here is what we saw last time:

1. We can use functions, pairs, ... to construct proofs, but that's really hard.
2. We instead use tactics to be more efficient.
3. We saw the `rfl` tactic to close goals that are literally equal.
4. We saw the `rw` tactic to rewrite terms along equalities.
-/

end review

section review_algebra

-- We also reviewed some basic algebraic rules.
variable (a b c : ℝ)

#check a
#check a + b
#check (a : ℝ)
#check mul_comm a b
#check (mul_comm a b : a * b = b * a)
#check mul_assoc a b c
#check mul_comm a
#check mul_comm

end review_algebra

section tactics_basics

/-
Basic tactics allows us to implement standard manipulation of proof steps and goals.
The following are (most of) the basic tactics we will use:
* `rfl`
* `rw`
* `intro`
* `exact`
* `apply`
* `have`
* `constructor`
* `obtain`
* `left`
* `right`
* `rcases`
* `use`
-/

-- `rfl` is the reflexivity tactic. It only works when things are literally equal.
example : (2 * 3) + 4 = 10 := by
  rfl

-- Usually we don't write `rfl`, cause it is applied automatically.
-- So `rfl` will not be very relevant for us.

-- `rw` is the rewrite tactic. It replaces one term with another *equal* term.

example {n} (hn : n = 2) : n + 3 = 7 - 2 := by
  rw [hn]

-- To get 2 + 3 = 7 -2 a `rfl` is applied automatically.

-- Very important: `rw` has direction.

example {n} (hn : 2 = n) : n + 3 = 7 - 2 := by
  rw [← hn]

-- We use `←` to rewrite in the other direction.

-- We can also rewrite in the assumption with `at`.

example {n m k} (hn : n = m  + 2 * k)  (hm : m = 3 * k) :  n = 5 * k := by
  rw [hm] at hn
  rw [← add_mul] at hn
  rw [hn]

-- Applying `rw` to algebraic rules allows us to prove basic algebraic properties.
example (a b c : ℝ) (ha : a = b * c) : b * a * c = a * a := by
  rw [mul_comm]
  rw [← mul_assoc]
  rw [mul_comm c b]
  rw [ha]


-- `intro` is the introduction tactic. It introduces a variable into the context.
-- We use it when we have an implication `→` .

example {n} : n = 2 → n + 3 = 5 := by
  intro hn
  rw [hn]

example (a b : ℝ) : a > 0 → b > 0 → a + b > 0 := by
  intro ha hb
  exact add_pos ha hb

example (P Q R : Prop) : (P → Q) → (P → Q → R) → P → R := by
  intros ha hb hc
  exact hb hc (ha hc)

-- For universal quantifiers `∀` we also apply  `intro`

example : ∀ a b : ℝ, a + b = b + a := by
  intro a b
  rw [add_comm]

/-
From the perspective of the system, ∀ is also just a function, however,
the codomain of the value of the function depends on the input.
Here the codomain of an input pair (a,b) is inside the type a + b = b + a
-/

-- `exact` is the exact tactic. It closes the goal with an explicit term.
-- exact means here that we are providing the exact term.
example (P Q : Prop) (h : P) (k : P → Q): Q := by
  exact k h

-- In particular if we have a `∀` in the assumption,
-- we can plug in the desired value and use `exact`
example (P : ℝ → Prop) (h : ∀ x, P x): P 2 := by
  exact h 2

-- Note in these cases `exact` is redundant. However, it is useful as part of larger proofs.

-- `apply` is the application tactic. It applies a function to the goal.
-- It is a *backwards* tactic, that reduces the goal.

example (P R Q : Prop) (h : P) (k : P → Q) (l : Q → R): R := by
  apply l
  apply k
  exact h

-- Note, again here we can do things more directly.

example (P R Q : Prop) (h : P) (k : P → Q) (l : Q → R): R := l (k h)

-- But this won't be the case later on.

-- `have` is the have tactic. It introduces a new assumption into the context.
-- It is a  *forwards* tactic.

example (P R Q : Prop) (h : P) (k : P → Q) (l : Q → R): R := by
  have q := k h
  have r := l q
  exact r

-- We can use tactics inside `have`.
example (P Q R S: Prop) (f : P → Q) (g : Q → R) (h : (P → R) → S) : S := by
  have gf : P → R := by {
    intro p
    apply g
    apply f
    exact p
  }
  exact h gf

-- To prove a conjunction i.e. *and* we use the `constructor` tactic.
example (P Q : Prop) (f : P → Q) : P → P ∧ Q := by
  intro p
  constructor
  · exact p
  · exact f p


-- This in particular applies to  *if and only if*, we use `constructor`
-- to decompose and then prove it separately.
example (a b : ℝ) : a = b ↔ b = a := by
  constructor
  · intro h
    rw [h]
  · intro h
    rw [h]

/-
To use a conjunction, we use .1 or .2
We can also use the `obtain` tactic to split the assumption.
-/

example (P Q : Prop) : P ∧ Q → Q := by
  intro h
  obtain ⟨hP, hQ⟩ := h
  exact hQ

example (P Q : Prop) : P ∧ Q → Q := by
  intro h
  exact h.2

example (P Q : Prop) : P ∧ Q → Q ∧ P := by
  intro h
  constructor
  · exact h.2
  · exact h.1


/-
To prove disjunction i.e. *or* we use the `left` or `right` tactic.
Depending on which side we want to prove.
-/

example (P Q : Prop) : P → P ∨ Q := by
  intro h
  left
  exact h

/-
On the other side, if we want to assume a disjunction, then we have to be more careful.
Here we use `rcases` to separate the cases.
-/

example (P Q : Prop) : P ∨ Q → Q ∨ P := by
  intro h
  rcases h with hP | hQ
  · right
    exact hP
  · left
    exact hQ

/-
To prove an existential quantifier, we use `use` and then provide a witness.
If we assume extensional quantifiers, we can use `obtain` to split the assumption.
-/

example (P : ℝ → Prop) (h : ∀ x, P x) : ∃ x, P x := by
  use 2
  exact h 2

-- The `use` tactic automatically tries to use available assumptions.

example (P : ℝ → Prop) (h : ∀ x, P x) : ∃ x, P x := by
  have h2 : P 2 := h 2
  use 2

example (P Q : ℝ → Prop) (h : ∃ x, P x ∧ Q x) : ∃ x, P x := by
  obtain ⟨x, hP, hQ⟩ := h
  use x

end tactics_basics

section advanced_combined_tactics
/-
There is a collection of combined tactics, which do not make a single step,
rather they try several proof steps at once, but usually in a particular mathematical domain.

We will look at the following examples:
* `specialize`
* `calc`
* `ring`
* `linarith`
* `decide`
* `tauto`
* `norm_num`
-/

-- `specialize` is a tactic that allows us to specialize a function to a particular input.
example (P : ℝ → Prop) (h : ∀ x, P x) : P 2 := by
  specialize h 2
  exact h

-- You can replace the `specialize` with `have`, but requires more details and keeps the original assumption.
example (P : ℝ → Prop) (h : ∀ x, P x) : P 2 := by
  have h' := h 2
  exact h'

-- `calc` is a tactic that allows us to do calculations step by step.
example (a b c : ℝ) (ha : a = b * c) : b * a * c = a * a := by
  calc b * a * c = c * (b * a) := by rw [mul_comm]
        _ = c * b * a  := by rw [← mul_assoc]
        _ = b * c * a := by rw [mul_comm c b]
        _ = a * a := by rw [ha]

example ( a b c d e : ℝ) (h₀ : a = b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by
  calc a
      = b := h₀
    _ < c := h₁
    _ ≤ d := h₂
    _ < e := h₃

-- `ring` is the ring tactic. It simplifies computational expressions in rings.

example (a b c : ℝ) : a * (b - c) = b * a - a * c := by
  ring

-- `linarith` is a tactic that solves linear inequalities and/or contradictions.

example (a b : ℤ) (h₁ : a + b ≥ 7) (h₂ : a ≤ 2) : b ≥ 5 := by
  linarith

-- `decide` is a tactic that solves decidable propositions.
example : 1 ≤ 3 := by
  decide

example : x ≤ 3 → x + 2 ≤ 6 := by
  revert x
  decide

-- `tauto` is a tactic that solves tautologies.

example (P: Prop) : P ∨ ¬ P := by
  tauto

example (P Q R S : Prop) (h : P → R) (h' : Q → S) : P ∧ Q → R ∧ S := by
  tauto


-- `norm_num` is a tactic that solves numerical equations.

example : 2*3 - 3 < 14 := by
  norm_num

-- This in particular includes divisibility.
example : 15 ∣ 60 := by
  norm_num

-- Again this example is not yet very impressive.
example : 15 ∣ 60 := by
  use 4

-- `gcongr` is a tactic that solves congruences.
example (a b c d : ℕ) (h₁ : a ≤ b) (h₂ : d ≤ c) :
    a + d ≤ b + c := by
  gcongr

-- Here is the standard Lean example:
example {a b x c d : ℝ} (h1 : a + 1 ≤ b + 1) (h2 : c + 2 ≤ d + 2) :
    x ^ 2 * a + c ≤ x ^ 2 * b + d := by
  gcongr
  · linarith
  · linarith

end advanced_combined_tactics

section advanced_proof_tactics

/-
There are some tactics that are more advanced in nature.

One important example is `simp`, which somewhat automatically simplifies expressions.
-/

example (a b c : ℝ) : a * (b + c) = a * c + b * a  := by
  rw [mul_add]
  rw [mul_comm]
  rw [add_comm]

example (a b c : ℝ) : a * (b + c) = a * c + b * a := by
  simp [mul_add]
  simp [mul_comm]
  simp [add_comm]

example (a b c : ℝ) : a * (b + c) = a * c + b * a := by
  simp only [mul_add, mul_comm, add_comm]

-- Here is an example we saw before:
example {a b c : ℝ} (ha : a = b * c) : b * a * c = a * a := by
  rw [mul_comm]
  rw [← mul_assoc]
  rw [mul_comm c b]
  rw [ha]

-- Here is a possible version with `simp`:
example {a b c : ℝ} (ha : a = b * c) : b * a * c = a * a := by
  rw [mul_comm, ← mul_assoc]
  simp only [mul_comm, ha]
-- Notice we do *not* need to specify `mul_comm c b` here.

-- However, `simp` also involves risks.
-- example {a b c : ℝ} (ha : a = b * c) : b * a * c = a * a := by
--   simp only [mul_comm, ← mul_assoc]

/- Another crucial example is `refine`.
This is also a powerful backwards tactic.
It allows creating gaps that can be filled later on.
-/

#check le_antisymm
#check Nat.zero_le

example ( n : ℕ) (ineq : n ≤ 0) : n = 0 := by
  exact le_antisymm ineq (Nat.zero_le n)

example ( n : ℕ) (ineq : n ≤ 0) : n = 0 := by
  refine le_antisymm ?_ ?_
  · exact ineq
  · exact Nat.zero_le n

/- Another useful tactic for us is `unfold`.
This tactic allows us to unfold definitions.
It usually has no implications for the proof itself.
-/

example : Continuous zz := by
  unfold zz
  apply continuous_const

-- Inside proofs we can also ue the `unfold` tactic, to better understand definitions.

example (a b : ℕ) : Even a → Even b → Even (a + b) := by
  intro ha hb
  -- Let's say I don't know what `Even` means.
  unfold Even
  unfold Even at ha
  unfold Even at hb
  -- Now I can see very explicitly what `Even` means and can continue.
  obtain ⟨k, hk⟩ := ha
  obtain ⟨l, hl⟩ := hb
  use k + l
  rw [hk, hl]
  ring

end  advanced_proof_tactics

section summary

/-
Here is a summary of all the tactics we just saw:

1. `rfl` - to close goals that are literally equal.
2. `rw` - to rewrite terms along equalities.
3. `intro` - to introduce assumptions.
4. `exact` - to provide exact matches for goals.
5. `apply` - to apply functions to goals.
6. `have` - to introduce new assumptions.
7. `constructor` - to prove equivalences and conjunctions.
8. `obtain` - to split assumptions in conjunctions and existential quantifiers.
9. `left` - to prove disjunctions.
10. `right` - to prove disjunctions.
11. `rcases` - to split disjunctions.
12. `use` - to provide witnesses for existential quantifiers.
13. `specialize` - to specialize a function to a particular input.
14. `calc` - to do calculations step by step.
15. `ring` - to simplify computational expressions in rings.
16. `linarith` - to solve linear inequalities and contradictions.
17. `decide` - to solve decidable propositions.
18. `tauto` - to solve tautologies.
19. `norm_num` - to solve numerical equations.
20. `simp` - to simplify expressions.
21. `simp only` - to simplify expressions with specific rules.
22. `refine` - to break down goals into smaller steps.
23. `unfold` - to unfold definitions.
-/

end summary

section help

/-
We now saw some basic tactics.

If we know the steps of a proof and the relevant lemmas, theorems, ...
then tactics are very powerful.

What if we don't even know the relevant input?

Here are some tricks for that:

* `#check` to check the type of a term
* Press `F12` on relevant definition to go to source file
* `#loogle`
* `#moogle`
* `#check`
* `unfold`
* `simp?`
* `apply?`
* `exact?`
-/

-- `#check` tells us what the term of a type is, giving us its behavior.
#check Nat.zero_le
-- I can see from the definition that `Nat.zero_le` is a function.
#check Nat.zero_le 3

-- Pressing `F12` on a definition takes us to the source file.

-- Moogle and loogle search the internet for suggestions.
#moogle "The sum of two even numbers is even."

#loogle "Existential"

/-
One can also directly check the relevant websites:
https://loogle.lean-lang.org/
https://www.moogle.ai/
-/


/-
`simp?`,  is a tactic that tries to suggest simplifications.
`apply?` similarly suggests apply
`exact?` suggests exact
-/

example (P Q : Prop) (p : P) (f : P → Q) : Q := by
  exact?
  -- exact f p

example (a b : ℝ) : (a + b = b + a) := by
  exact?
  -- exact AddCommMagma.add_comm a b

example ( x : ℝ)  : x - x + x = x := by
  simp?
  -- simp only [sub_self, zero_add]

example (xs ys : List ℕ) : (xs ++ ys).length = ys.length + xs.length := by
  simp?
  exact?
  -- simp only [List.length_append]
  -- exact Nat.add_comm xs.length ys.length

end help
