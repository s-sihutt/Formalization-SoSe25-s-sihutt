import Mathlib.Tactic

def epsilon_delta (X : Set ℝ) (x0 : ℝ) (y0 : ℝ) (f : ℝ → ℝ) : Prop :=
    ∀ ε > 0, (∃ δ > 0 , ∀ x : X, (|x.val - x0| < δ → |f x - y0| < ε))

def is_derivative_at (X : Set ℝ) (y0 : ℝ) (x0 : ℝ) (f : ℝ → ℝ) : Prop :=
    epsilon_delta X (x0 : ℝ) (y0 : ℝ) (fun x : ℝ ↦ (f x - f x0) / (x - x0))

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

theorem mul_mul_lt (a1 a2 b1 b2 : ℝ) (a1sb1: a1 < b1) (a2sb2: a2 < b2): (a1 * a2 < b1 * b2) ↔ (a1 < b1) := by
    constructor
    simp [a1sb1]
    sorry


theorem testfun1 : is_derivative_at {x1 : ℝ| (x1 ≠ 0) ∧ (x1 - 1 ≠ 0)} (5 : ℝ) (1 : ℝ)
    (fun x : ℝ ↦ x^3 + 2*x + 4) := by
    simp[is_derivative_at]
    simp[epsilon_delta]
    intro ε ε_is_larger_than_0
    use -3/2 + Real.sqrt (ε + 9/4)
    constructor
    · rw [← lt_add_iff_pos_left (3/2)]
      rw [add_comm (-3/2)]
      rw [add_assoc]
      rw [neg_div]
      rw [← sub_eq_neg_add (3/2) (3/2)]
      rw [sub_self]
      rw [add_zero]
      have epsIsAbs: |ε| = ε := by
        rw [abs_eq_self]
        linarith

      rw [← epsIsAbs]

      have div3a2isSqr: (3:ℝ)/(2:ℝ) = Real.sqrt ((9:ℝ)/(4:ℝ)) := by
        rw[Real.sqrt_div]
        norm_num
        norm_num

      rw [div3a2isSqr]
      have div9a4isAbsl0: 0 < |(9:ℝ)/(4:ℝ)| := by
        norm_num
      have div9a4isAbs: (9:ℝ)/(4:ℝ) = |(9:ℝ)/(4:ℝ)| := by
        rw[abs_div]
        rw[Nat.abs_ofNat]
        rw[Nat.abs_ofNat]
      rw [div9a4isAbs]
      rw [Real.sqrt_lt_sqrt_iff]
      rw [lt_add_iff_pos_left]
      rw [epsIsAbs]

      rotate_left
      rw [abs_div]
      rw[Nat.abs_ofNat]
      rw[Nat.abs_ofNat]
      norm_num

      simp [ε_is_larger_than_0]

    intro x h1 h2
    push_neg at h1 h2
    have add1a2: 3 = (1 : ℝ) + (2 : ℝ) := by ring
    have sub5a3: 2 = (5 : ℝ) - (3 : ℝ) := by ring
    have sub2a5: -3 = (2 : ℝ) - (5 : ℝ) := by ring
    have sub1a3: -2 = (1 : ℝ) - (3 : ℝ) := by ring
    have h3: 1 = (x - 1)/(x - 1) := by simp[h2]
    have h4: (x + (-1)) ≠ 0 := by
        rw[← sub_eq_add_neg]
        simp [h2]

    rw [← add1a2]
    rw [div_sub']
    rotate_left
    case h =>
        simp [h2]
    rw [sub_mul]
    rw [mul_comm 1 5]
    rw [mul_one]
    rw [← sub_add]
    rw [sub_add (x^3 + 2*x - 3) (x*5) 5]
    rw [sub_sub (x^3+2*x) 3 (x*5-5)]
    rw [← add_sub]
    rw [← sub_sub]
    rw [sub_right_comm]
    rw [← sub_add]
    rw [mul_comm x 5]
    rw [← sub_mul]
    rw [← add_sub]
    rw [← sub2a5]
    rw [← sub5a3]
    rw [sub_eq_add_neg]

    rw [polydivide (x^3) (-3*x+2) x (-1)]
    case h.right.nz =>
        simp [h4]
    case h.right.nzz =>
        simp [h1]
    rw [pow_three]
    rw [mul_comm x (x * x)]
    rw [mul_comm (x * x * x) (-1)]
    rw [← mul_assoc]
    rw [mul_div_assoc]
    rw [mul_div_assoc (-1 * (x*x))]
    simp [h1]
    rw [add_comm (-(3*x) + 2)]

    rw [polydivide (x*x) (-(3*x)+2) x (-1)]
    case h.right.nz =>
        simp [h4]
    case h.right.nzz =>
        simp [h1]
    rw[mul_comm (x * x) (-1)]
    rw[← mul_assoc]
    rw[← mul_div]
    rw[← mul_div (-1 * x) x x]
    simp[h1]
    rw[add_comm (-(3*x)+2) x]
    rw[← add_assoc]
    rw[← add_assoc]
    rw[← sub_eq_add_neg x (3*x)]
    rw[mul_comm 3 x]
    rw[← mul_one_sub]
    rw[← sub1a3]
    rw[← neg_neg (x*(-2) + 2)]
    rw[neg_add]
    rw[← neg_mul (x) (-2)]
    rw[neg_mul_neg x 2]
    rw[← sub_eq_add_neg (x*2) 2]
    rw[mul_comm x 2]
    rw[← mul_sub_one 2 x]
    rw[← neg_mul]
    rw[← sub_eq_add_neg]
    rw[← mul_div]
    simp [h2]
    rw[add_assoc]
    rw[← sub_eq_add_neg]
    rw[← mul_one (x*x + (x-2))]
    rw[h3]
    rw [mul_div]
    rw [mul_comm]
    rw [← mul_div]
    rw [← h3]
    rw [sub_eq_add_neg]

    rw [polydivide (x*x) (x-2) x (-1)]
    case h.right.nz =>
        simp [h4]
    case h.right.nzz =>
        simp [h1]
    rw[mul_comm (x * x) (-1)]
    rw[← mul_assoc]
    rw[← mul_div]
    rw[← mul_div (-1 * x) x x]
    simp[h1]
    rw[sub_add_eq_add_sub]
    rw[← two_mul]
    rw[← mul_sub_one 2 x]
    rw[← sub_eq_add_neg]
    rw[← mul_div]
    simp [h2]
    rw [abs_mul]

    rw[abs_lt]
    intro ha
    obtain ⟨ha1, ha2⟩ := ha

    have h0: |x-1| < -3/2 + Real.sqrt (ε + 9/4) := by
        rw[abs_lt]
        constructor
        · linarith
        · linarith

    have h00: |x+2| < -3/2 + Real.sqrt (ε + 9/4) + 3  := by
      rw[abs_lt]
      constructor
      · rw [← lt_neg_add_iff_lt]
        rw [add_comm]
        rw [← sub_add_cancel x 1]
        rw [neg_neg]
        rw [add_assoc]
        rw [add_assoc]
        rw [add_assoc]
        rw [← add_assoc 1 2]
        rw [← add1a2]
        rw [add_comm (Real.sqrt (ε + 9/4))]
        rw [← add_assoc]
        rw [← add_assoc (-3/2)]
        rw [add_comm (-3/2)]
        rw [add_assoc]
        rw [← add_assoc 3]
        rw [← add_assoc 3 3 (-3/2)]
        have add3a3: 6 = (3:ℝ) + (3:ℝ) := by ring
        rw [← add3a3]
        rw [← add_assoc]
        rw [← add_assoc]
        rw [add_assoc (x - 1)]
        rw [add_assoc]
        rw [← neg_neg (6 + (-3/2) + Real.sqrt (ε + 9/4) )]
        rw [add_comm (x-1)]
        rw [lt_neg_add_iff_lt]
        rw [add_assoc]
        rw [neg_add]
        linarith
      · rw [← lt_neg_add_iff_lt]
        rw [neg_add]
        rw [add_assoc]
        rw [add_assoc]
        rw [← add_comm 3]
        rw [← add_assoc (-3/2)]
        rw [← add_comm 3]
        rw [add_assoc 3]
        rw [← add_assoc (-2)]
        have addm2a3: -(-1)= (-(2:ℝ)) + (3:ℝ) := by ring
        rw [← addm2a3]
        rw [← add_assoc]
        rw [← neg_add]
        rw [← sub_eq_add_neg]
        rw [lt_neg_add_iff_lt]
        linarith

    have εMul: ε = (-3/2 + Real.sqrt (ε + 9/4))*(-3/2 + Real.sqrt (ε + 9/4) + 3) := by
        ring_nf
        rw[Real.sq_sqrt]
        rw[← add_assoc]
        rw[add_comm (-9/4)]
        rw[neg_div]
        rw[add_neg_cancel]
        rw[zero_add ε]
        linarith
    rw [εMul]
    rw [mul_mul_lt]
    simp[h0]
    simp[h0]
    simp[h00]


--    rw [lt_or_lt_of_mul_lt_mul (|x-1|) (-3/2 + Real.sqrt (ε + 9/4)) (|x+2|) (-3/2 + Real.sqrt (ε + 9/4) + 3)]
--    simp[mul_lt_mul_of_lt_of_le (|x-1|) (|x+2|) (-3/2 + Real.sqrt (ε + 9/4)) (-3/2 + Real.sqrt (ε + 9/4) + 3)]
