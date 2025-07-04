import Mathlib.Tactic

section continuity
/-
Here are some basic exercises about continuity.
-/

example (X : Type*) [MetricSpace X] : Continuous (fun x : X => x) := by
  apply Metric.continuous_iff.2
  sorry

/-
For this you want to use the fact that if `cg : Continuous g`, then
`cg.isOpen_preimage` is well-defined and gives the fact that inverse of an open is open.
-/

example (X Y Z: Type*) (f : X → Y) (g : Y → Z) [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] (cf: Continuous f) (cg: Continuous g) : Continuous (g ∘ f) := by
  apply continuous_def.2
  sorry

end continuity

section cofiniteTopology
/-
Let us define a new topology on `ℝ` where a set is open if one of the following hold:
- The complement is finite, or
- The set is empty.
This is known as the cofinite topology.
-/

instance : TopologicalSpace ℝ where
  IsOpen := fun s => (sᶜ).Finite ∨ s = ∅
  isOpen_univ := by sorry
  isOpen_inter := by
  -- Here you want to use `Set.compl_inter` and `Set.Finite.union`
    sorry
  isOpen_sUnion := by
    intro s h
    rw [Set.compl_sUnion]
    simp
    -- We separate into two cases
    by_cases hh : ∃ t ∈ s, tᶜ.Finite
    -- For the first case you want to use `Set.Finite.subset`
    · sorry
    · sorry

/-
Here is a definition of the convergence of a sequence.
-/
def convergent_sequence (s : ℕ → ℝ) (l : ℝ) : Prop :=
  ∀ U : Set ℝ, IsOpen U → l ∈ U → ∃ N : ℕ , ∀ n ≥ N, s n ∈ U

/-
Now, here is an example of a real-valued sequence.
It simply maps `n : ℕ` to `n : ℝ`.
-/

def d : ℕ → ℝ := fun n => n

/-
Now, let us prove explicitly the following result.
The sequence `d` converges to every real number.
-/


theorem d_converges_to_everything (a : ℝ) : convergent_sequence d a := by
  intro U hU hU0
  simp [IsOpen] at hU
  rcases hU with (UcFinite | Uempty)
  ·
  /-
  We break down the proof into two cases:
  - Case 1: `Uᶜ = ∅`
  - Case 2: `Uᶜ ≠ ∅`
  -/
    by_cases UcEmpty : Uᶜ = ∅
    -- The case `U = ∅`  is straightforward.
    · sorry
    -- The case `Uᶜ ≠ ∅` is the difficult step.
    · push_neg at UcEmpty
      /-
      We define `X` as the finite set with elements from `Uᶜ`.
      -/
      let X := Set.Finite.toFinset UcFinite
      /-
      We can use a proof by contradiction to show that `X` is non-empty.
      -/
      have Xnonempty : X.Nonempty := by
        sorry
      let m := Finset.max' X Xnonempty
      /-
      `m` is the maximum element of `X`.
      We need to explicitly see that it is larger than all elements in `Uᶜ`.
      -/
      have lessm : ∀ n ∈ Uᶜ, n ≤ m := by
        intro n nh
        refine Finset.le_max' X n ?_
        sorry
      /-
      We can now choose the anticipated `N`
      -/
      let m':= (Int.ceil |m|).toNat
      /-
      To finish the proof, we need to observe several equalities.
      -/
      have mleqm' : (m : ℝ) ≤ (m' : ℝ) := by
        simp [m']
        /-
        As we have an absolute value, we need to consider two cases:
        - `m ≥ 0`
        - `m < 0`
        -/
        by_cases mpos : m ≥ 0
        · rw [abs_of_nonneg mpos]
          /-
          Unfortunately, Lean has a hard time dealing with numbers in
          `ℕ`, `ℤ` and `ℝ` at the same time.
          So, we need some extra steps, and the tactic `norm_cast`.
          -/
          have ceil_eq : ((⌈m⌉ : ℤ).toNat) = (⌈m⌉ : ℝ) := by
            norm_cast
            simp
            exact Int.ceil_nonneg mpos
          /-
          Here you want to use `Int.le_ceil`, but it will not work directly.
          Hint: `ceil_eq` can help.
          -/
          sorry
        ·
          -- The case `m < 0` should be straightforward.
          sorry
      use m' + 1
      intro n hn
      simp [d]
      by_contra hc
      simp at hc
      -- We can use the previous step to finally show that `n < n`.
      have nlessn : (n: ℝ)  < n := by
      -- The tactics `linarith` and `norm_cast` should help.
        calc
          n ≤ m := sorry
          _ ≤ m' := sorry
          _ < m' + 1 := sorry
          _ ≤ n := sorry
      sorry
  · sorry

end cofiniteTopology
