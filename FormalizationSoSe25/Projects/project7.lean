import Mathlib.Tactic

def epsilon_delta (x0 : ℝ) (f : ℝ → ℝ) : Prop :=
    ∀ ε > 0, (∃ δ > 0 , ∀ x : ℝ, (|x - x0| < δ → |f x - f x0| < ε))

def is_derivative_at (x0 y0 : ℝ) (f : ℝ → ℝ) : Prop :=
    epsilon_delta (x0 : ℝ) (fun x : ℝ ↦ (f x - f x0) / (x - x0) - y0)


theorem polydivide (z1 z2 n1 n2 : ℝ) (nz: n1 + n2 ≠ 0) (nzz: n1 ≠ 0): (z1 + z2)/(n1 + n2) = z1/n1 + (z2 - z1 * n2/n1)/(n1 + n2) := by
    rw [← div_add_div_same z1 z2 (n1 + n2)]
    rw [← add_zero (z1/(n1 + n2))]
    rw [← sub_self ((z1 * n2/n1)/(n1 + n2))]
    rw [add_sub (z1 / (n1 + n2)) (z1 * n2 / n1 / (n1 + n2)) (z1 * n2 / n1 / (n1 + n2))]
    rw [← add_div z1 (z1 * n2/n1) (n1 + n2)]
    rw [← add_zero (z1 + z1 * n2/n1)]
    rw [add_comm z1 (z1 * n2/n1)]
    rw [add_assoc (z1 * n2/n1) z1 0]
    rw [← mul_one (z1 + 0)]
    rw [add_zero]
    rw [← mul_div z1 n2 n1]
    rw [← mul_add z1 (n2/n1) 1]
    rw [← div_add_same]
    rw [mul_div_left_comm z1 (n2 + n1) n1]
    rw [add_comm n2 n1]
    simp [nz]
    rw [← add_sub_right_comm]
    rw [← add_sub]
    rw [← sub_div z2 (z1 * (n2 / n1)) (n1 + n2)]
    simp [nzz]

theorem testfun1 (x : ℝ) : is_derivative_at  (1 : ℝ) (5 : ℝ)
    (fun x : ℝ ↦ x^3 + 2*x + 4) := by
    simp[is_derivative_at]
    simp[epsilon_delta]
    intro ε ε_is_larger_than_0
    use ε/4
    simp [ε_is_larger_than_0]
    intro x h1
    rw [sub_eq_add_neg x 1]
    rw [← add_sub]
    rw [polydivide (x^3) (2 * x - (1 + 2)) x (-1)]
