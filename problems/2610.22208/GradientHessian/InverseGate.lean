import GradientHessian.InverseGateOperator
import GradientHessian.InverseGateFunctions

/-! The manuscript's numerical activation lemma for the literal objective.
The inverse is constructed from I ≤ A; no inverse contraction or positivity
property is assumed. The upper bound A ≤ M I is not needed for this lemma.
-/

noncomputable section
namespace GradientHessian.InverseGate

open Filter
open scoped Topology InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem small_gradient_norm_y (A : E →L[ℝ] E) (hA : LowerBound A)
    (hsym : ∀ x z, ⟪A x, z⟫_ℝ = ⟪x, A z⟫_ℝ) (b a y : E)
    (hb : ‖b‖ = H₀) (ha : ‖a‖ = 1) {d : ℝ} (hd0 : 0 ≤ d) (hd56 : d ≤ 56)
    (hg : ‖gradient (objective A b a d) y‖ ≤ 1) : ‖y‖ < 2 * H₀ := by
  have he : A y = gradient (objective A b a d) y + gradient (forcing b) y +
      d • gradient (gate a) y := by
    rw [(objective_hasGradientAt A hsym b a y d).gradient]
    abel
  have hf := forcing_gradient_norm_le b y
  rw [hb] at hf
  have hc := gate_gradient_norm_le a y ha
  have hd := mul_le_mul hd56 hc (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 56)
  have hdn : ‖d • gradient (gate a) y‖ ≤ 56 * (12 / alpha) := by
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hd0] using hd
  have hsum1 := norm_add_le (gradient (objective A b a d) y + gradient (forcing b) y)
    (d • gradient (gate a) y)
  have hsum2 := norm_add_le (gradient (objective A b a d) y) (gradient (forcing b) y)
  rw [← he] at hsum1
  have hlow := lowerBound_norm A hA y
  have hconst : 1 + H₀ + 56 * (12 / alpha) < 2 * H₀ := by norm_num [H₀, alpha]
  linarith

theorem forcing_gradient_inside (b y : E) (hb : ‖b‖ = H₀) (hy : ‖y‖ < 2 * H₀) :
    gradient (forcing b) y = b := by
  have hi : |⟪b, y⟫_ℝ| ≤ H₀ * ‖y‖ := by
    simpa only [Real.norm_eq_abs, hb] using norm_inner_le_norm (𝕜 := ℝ) b y
  have harg : |forcingArg b y| ≤ 8 := by
    rw [forcingArg, abs_div, abs_of_pos (sq_pos_of_pos H₀_pos),
      div_le_iff₀ (sq_pos_of_pos H₀_pos)]
    have hm := mul_le_mul_of_nonneg_left hy.le H₀_pos.le
    nlinarith [sq_nonneg H₀]
  rw [(forcing_hasGradientAt b y).gradient, (IntegralProfiles.theta_derivative _).deriv]
  rw [Profiles.step_nonpos (by linarith : |forcingArg b y| - 8 ≤ 0)]
  simp

theorem small_gradient_argument (A : E →L[ℝ] E) (hA : LowerBound A)
    (hsym : ∀ x z, ⟪A x, z⟫_ℝ = ⟪x, A z⟫_ℝ) (b a y : E)
    (hb : ‖b‖ = H₀) (ha : ‖a‖ = 1)
    (hcert : H₀ / 4 ≤ ⟪a, inverse A hA b⟫_ℝ)
    {d : ℝ} (hd0 : 0 ≤ d) (hd56 : d ≤ 56)
    (hg : ‖gradient (objective A b a d) y‖ ≤ 1) :
    ‖y‖ < B₀ ∧ 1 / 2 < ⟪a, y⟫_ℝ / alpha := by
  have hsmall := small_gradient_norm_y A hA hsym b a y hb ha hd0 hd56 hg
  have hB : ‖y‖ < B₀ := by
    have hnum : 2 * H₀ < B₀ := by norm_num [H₀, B₀]
    linarith
  let v := gradient (objective A b a d) y
  let c := d * deriv Profiles.chi (⟪a, y⟫_ℝ / alpha) / alpha
  have hc : 0 ≤ c := by
    exact div_nonneg (mul_nonneg hd0 (chi_derivative_nonneg _)) alpha_pos.le
  have hv : v = A y - b - c • a := by
    dsimp [v, c]
    rw [(objective_hasGradientAt A hsym b a y d).gradient,
      forcing_gradient_inside b y hb hsmall, (gate_hasGradientAt_inside a y hB).gradient,
      smul_smul]
    congr 2
    ring
  have he : inverse A hA v = y - inverse A hA b - c • inverse A hA a := by
    rw [hv, map_sub, map_sub, map_smul, inverse_apply]
  have hy : y = inverse A hA b + c • inverse A hA a + inverse A hA v := by
    rw [he]
    abel
  have hnoise : -1 ≤ ⟪a, inverse A hA v⟫_ℝ := by
    have hin : ‖inverse A hA v‖ ≤ 1 := (inverse_norm_le A hA v).trans hg
    have hinner := norm_inner_le_norm (𝕜 := ℝ) a (inverse A hA v)
    rw [Real.norm_eq_abs, ha, one_mul] at hinner
    exact (abs_le.mp (hinner.trans hin)).1
  have hpositive := mul_nonneg hc (inverse_quadratic_nonneg A hA a)
  have hl : H₀ / 4 - 1 ≤ ⟪a, y⟫_ℝ := by
    rw [hy, inner_add_right, inner_add_right, real_inner_smul_right]
    linarith
  refine ⟨hB, ?_⟩
  rw [lt_div_iff₀ alpha_pos]
  have hnum : (1 / 2 : ℝ) * alpha < H₀ / 4 - 1 := by norm_num [H₀, alpha]
  linarith

/-- Numerical activation, including the actual complete second jet of the gate. -/
theorem numerical_activation (A : E →L[ℝ] E) (hA : LowerBound A)
    (hsym : ∀ x z, ⟪A x, z⟫_ℝ = ⟪x, A z⟫_ℝ) (b a y : E)
    (hb : ‖b‖ = H₀) (ha : ‖a‖ = 1)
    (hcert : H₀ / 4 ≤ ⟪a, inverse A hA b⟫_ℝ)
    {d : ℝ} (hd0 : 0 ≤ d) (hd56 : d ≤ 56)
    (hg : ‖gradient (objective A b a d) y‖ ≤ 1) :
    gate a y = 1 ∧ JetLocality.richJet (gate a) y = (1, 0, 0) ∧ ‖A y - b‖ ≤ 1 := by
  obtain ⟨hB, harg⟩ := small_gradient_argument A hA hsym b a y hb ha hcert hd0 hd56 hg
  have hnear := gate_flat_near_of_argument a y hB harg
  have hjet : JetLocality.richJet (gate a) y = (1, 0, 0) := by
    simpa [JetLocality.richJet] using JetLocality.richJet_congr_of_eventuallyEq hnear
  have hfirst : fderiv ℝ (gate a) y = 0 := by simpa using hnear.fderiv_eq (𝕜 := ℝ)
  have hc : gradient (gate a) y = 0 := by simp [gradient, hfirst]
  have hsmall := small_gradient_norm_y A hA hsym b a y hb ha hd0 hd56 hg
  have hres : gradient (objective A b a d) y = A y - b := by
    rw [(objective_hasGradientAt A hsym b a y d).gradient,
      forcing_gradient_inside b y hb hsmall, hc, smul_zero, sub_zero]
  refine ⟨hnear.self_of_nhds, hjet, ?_⟩
  rwa [← hres]

/-- Source-shaped version retaining the upper spectral inequality A ≤ M I.
The stronger core theorem above shows that this upper inequality is unnecessary
for numerical activation itself. -/
theorem source_numerical_activation (A : E →L[ℝ] E) (M : ℝ)
    (hlower : ∀ x, ‖x‖ ^ 2 ≤ ⟪A x, x⟫_ℝ)
    (_hupper : ∀ x, ⟪A x, x⟫_ℝ ≤ M * ‖x‖ ^ 2)
    (hsym : ∀ x z, ⟪A x, z⟫_ℝ = ⟪x, A z⟫_ℝ) (b a y : E)
    (hb : ‖b‖ = H₀) (ha : ‖a‖ = 1)
    (hcert : H₀ / 4 ≤ ⟪a, inverse A hlower b⟫_ℝ)
    {d : ℝ} (hd0 : 0 ≤ d) (hd56 : d ≤ 56)
    (hg : ‖gradient (fun x => g A b x - d * gate a x) y‖ ≤ 1) :
    gate a y = 1 ∧ JetLocality.richJet (gate a) y = (1, 0, 0) ∧ ‖A y - b‖ ≤ 1 :=
  numerical_activation A hlower hsym b a y hb ha hcert hd0 hd56 hg

end GradientHessian.InverseGate
