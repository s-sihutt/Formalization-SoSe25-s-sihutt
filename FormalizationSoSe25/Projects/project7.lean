import Mathlib.Tactic

def epsilon_delta (x0 : ℝ) (f : ℝ → ℝ) : Prop := ∀ ε > 0, (∃ δ > 0 , ∀ x : ℝ, (|x - x0| < δ → |f x - f x0| < ε))

def is_derivative_at (x0 y0 : ℝ) (f : ℝ → ℝ) : Prop := epsilon_delta (1 : ℝ) (fun x : ℝ ↦ (f x - f x0) / (x - x0) - y0)

theorem testfun1 (x : ℝ) : is_derivative_at  (1 : ℝ) (5 : ℝ)
(fun x : ℝ ↦ x^3 - 2*x + 4) := by
    simp[is_derivative_at]
    simp[epsilon_delta]
    intro ε ε_is_larger_than_0
