import ExactValue.SCModel

open scoped InnerProductSpace
set_option autoImplicit false
namespace ExactValue
noncomputable section

/-- At equal smoothness and strong convexity, every objective is an isotropic quadratic. -/
theorem sc_equal_parameters_quadratic {d : ℕ} {μ R : ℝ} {f : Euclid d → ℝ}
    (hf : SCObjective d μ μ R f) :
    ∃ b : Euclid d, ∀ x, f x = μ / 2 * ‖x‖ ^ 2 + ⟪b, x⟫_ℝ + f 0 := by
  obtain ⟨G, hder, hLip⟩ := hf.gradient_lipschitz
  refine ⟨G 0, ?_⟩
  intro x
  have hlo := strong_supporting hf.strong hder x 0
  have hup := smooth_remainder hder hLip 0 x
  simp only [sub_zero, zero_add] at hlo hup
  have hu := (le_abs_self _).trans hup
  linarith

/-- Exact coordinate recovery from the d+1 values in the endpoint proposition. -/
theorem isotropic_coordinate_recovery {d : ℕ} {μ h : ℝ} {f : Euclid d → ℝ} {b : Euclid d}
    (hh : h ≠ 0) (hf : ∀ x, f x = μ / 2 * ‖x‖ ^ 2 + ⟪b, x⟫_ℝ + f 0) (i : Fin d) :
    (f (h • EuclideanSpace.single i 1) - f 0) / h - μ * h / 2 = b i := by
  rw [hf (h • EuclideanSpace.single i 1)]
  simp only [norm_smul, EuclideanSpace.norm_single, norm_one, mul_one, Real.norm_eq_abs,
    sq_abs, inner_smul_right, EuclideanSpace.inner_single_right, mul_one]
  field_simp
  ring

end
end ExactValue
