import Nonsmooth.GaussianPolynomialEnvelope

open MeasureTheory Filter
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem potential_vector_weighted_bound (V : ℝ → ℝ) (F : ℝ → G)
    {a B C : ℝ} {m : ℕ} (hV : ∀ x, a * x ^ 2 - B ≤ V x)
    (hF : ∀ x, ‖F x‖ ≤ C * (1 + |x| ^ m)) (x : ℝ) :
    ‖Real.exp (-V x) • F x‖ ≤
      (Real.exp B * C) * (1 + |x| ^ m) * Real.exp (-a * x ^ 2) := by
  have he : Real.exp (-V x) ≤ Real.exp B * Real.exp (-a * x ^ 2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith [hV x]
  calc
    _ = Real.exp (-V x) * ‖F x‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    _ ≤ Real.exp (-V x) * (C * (1 + |x| ^ m)) := mul_le_mul_of_nonneg_left (hF x) (Real.exp_pos _).le
    _ ≤ (Real.exp B * Real.exp (-a * x ^ 2)) * (C * (1 + |x| ^ m)) :=
      mul_le_mul_of_nonneg_right he ((norm_nonneg _).trans (hF x))
    _ = _ := by ring

theorem potential_vector_weighted_integrable (V : ℝ → ℝ) (F : ℝ → G)
    (hm : AEStronglyMeasurable (fun x => Real.exp (-V x) • F x))
    {a B C : ℝ} {m : ℕ} (ha : 0 < a)
    (hV : ∀ x, a * x ^ 2 - B ≤ V x) (hF : ∀ x, ‖F x‖ ≤ C * (1 + |x| ^ m)) :
    Integrable (fun x => Real.exp (-V x) • F x) :=
  (gaussian_polynomial_envelope_integrable ha (Real.exp B * C) m).mono' hm
    (Eventually.of_forall (potential_vector_weighted_bound V F hV hF))

end
end Nonsmooth
