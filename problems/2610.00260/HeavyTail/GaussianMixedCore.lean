import HeavyTail.GaussianMixedExp

noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace
namespace HeavyTail.GaussianEstimates

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

def coreExp (ξ : Ω → E) (t₀ : ℝ) (d v₀ : E) (a ε : ℝ) (w : Ω × E) : ℝ :=
  Real.exp (ε * (HeavyTail.clip
    ((t₀ + ⟪d, w.2⟫_ℝ) + ⟪v₀, ξ w.1⟫_ℝ + a * ⟪ξ w.1, w.2⟫_ℝ) - (t₀ + ⟪d, w.2⟫_ℝ)))

theorem coreExp_integrable {ξ : Ω → E} (hξ : Measurable ξ) (t₀ : ℝ)
    (d v₀ : E) (a ε : ℝ) (hε : ε = -1 ∨ ε = 1) :
    Integrable (coreExp E ξ t₀ d v₀ a ε) (P.prod (euclideanGaussianLaw E)) := by
  have hi : Integrable (fun w : Ω × E => Real.exp (1 + |t₀|) * Real.exp |⟪d, w.2⟫_ℝ|)
      (P.prod (euclideanGaussianLaw E)) := by
    simpa only [one_mul] using (integrable_const (Real.exp (1 + |t₀|)) (μ := P)).mul_prod
      (gaussian_exp_abs_inner_integrable E d 1)
  apply hi.mono'
  · apply Measurable.aestronglyMeasurable
    unfold coreExp HeavyTail.clip
    fun_prop
  · exact ae_of_all _ fun w => by
      unfold coreExp
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply (clipped_exp_le _ _ _ _ hε).trans
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have := abs_add_le t₀ ⟪d, w.2⟫_ℝ
      linarith

theorem gaussian_core_exp {ξ : Ω → E} (hξ : Measurable ξ)
    (h2 : Integrable (fun ω => ‖ξ ω‖ ^ 2) P) (hcenter : (∫ ω, ξ ω ∂P) = 0)
    {p t₀ : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) (ht : |t₀| ≤ 1 / 8)
    (d v₀ : E) (hd : 4 * ‖d‖ ^ 2 ≤ 1) (a ε : ℝ) (hε : ε = -1 ∨ ε = 1)
    (hpint : Integrable (fun ω => |⟪v₀, ξ ω⟫_ℝ| ^ p) P) :
    (∫ w, coreExp E ξ t₀ d v₀ a ε w ∂P.prod (euclideanGaussianLaw E)) ≤
      Real.exp (100 * (mixedWeakConstant * (∫ ω, |⟪v₀, ξ ω⟫_ℝ| ^ p ∂P) +
        mixedQuadraticConstant * a ^ 2 * (∫ ω, ‖ξ ω‖ ^ 2 ∂P) +
        4 * mixedQuadraticConstant * ‖d‖ ^ 2)) := by
  let T : Ω × E → ℝ := fun w => t₀ + ⟪d, w.2⟫_ℝ
  let U : Ω × E → ℝ := fun w => ⟪v₀, ξ w.1⟫_ℝ
  let V : Ω × E → ℝ := fun w => a * ⟪ξ w.1, w.2⟫_ℝ
  have hξi := noise_integrable_of_second E hξ h2
  have hui : Integrable U (P.prod (euclideanGaussianLaw E)) := by
    simpa only [mul_one] using (hξi.const_inner v₀).mul_prod
      (integrable_const (1 : ℝ) (μ := euclideanGaussianLaw E))
  have hvi : Integrable V (P.prod (euclideanGaussianLaw E)) :=
    (noise_gaussian_linear_integrable E hξ h2).const_mul a
  have huz : (∫ w, U w ∂P.prod (euclideanGaussianLaw E)) = 0 := by
    have he := integral_prod_mul (μ := P) (ν := euclideanGaussianLaw E)
      (fun ω => ⟪v₀, ξ ω⟫_ℝ) (fun _ : E => (1 : ℝ))
    simpa [U, integral_inner hξi, hcenter] using he
  have hvz : (∫ w, V w ∂P.prod (euclideanGaussianLaw E)) = 0 := by
    dsimp [V]
    rw [integral_const_mul, noise_gaussian_linear_zero E hξ h2, mul_zero]
  have hlz : (∫ w, U w + V w ∂P.prod (euclideanGaussianLaw E)) = 0 := by
    rw [integral_add hui hvi, huz, hvz, add_zero]
  have hU := shifted_weak_product (P := P) E ht d v₀ hd hpint
  have hV := shifted_quadratic_product E hξ h2 ht d hd a
  have hT := shifted_tail_product (P := P) E ht d hd
  have hte : (fun w : Ω × E => Real.exp (2 * |T w|) *
      (if 1 / 2 < |T w| then (T w) ^ 2 else 0)) =
      (fun w => shiftedTail t₀ ⟪d, w.2⟫_ℝ) := by
    funext w
    unfold shiftedTail T
    split_ifs <;> simp
  have hti : Integrable (fun w => Real.exp (2 * |T w|) *
      (if 1 / 2 < |T w| then (T w) ^ 2 else 0)) (P.prod (euclideanGaussianLaw E)) := by
    rw [hte]
    exact hT.1
  have htm : Measurable T := by dsimp [T]; fun_prop
  have hum : Measurable U := by dsimp [U]; fun_prop
  have hvm : Measurable V := by dsimp [V]; fun_prop
  have hs := integrated_mixed_scalar hp hp2 hε htm hum hvm (hui.add hvi) hlz hU.1 hV.1 hti
  rw [hte] at hs
  have hsum := add_le_add (add_le_add hU.2 hV.2) hT.2
  have hbound := hs.trans (add_le_add_left (mul_le_mul_of_nonneg_left hsum
    (by norm_num : (0 : ℝ) ≤ 100)) 1)
  change (∫ w, coreExp E ξ t₀ d v₀ a ε w ∂P.prod (euclideanGaussianLaw E)) ≤ _ at hbound
  exact hbound.trans (by linarith [Real.add_one_le_exp (100 *
    (mixedWeakConstant * (∫ ω, |⟪v₀, ξ ω⟫_ℝ| ^ p ∂P) +
      mixedQuadraticConstant * a ^ 2 * (∫ ω, ‖ξ ω‖ ^ 2 ∂P) +
      4 * mixedQuadraticConstant * ‖d‖ ^ 2))])

end HeavyTail.GaussianEstimates
