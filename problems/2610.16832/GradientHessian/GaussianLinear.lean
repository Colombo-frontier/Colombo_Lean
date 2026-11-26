import GradientHessian.GaussianHilbert

/-! # Linear Gaussian exponential moments and tails

The product-integration proof is adapted from the self-contained portions of
the checked Nonsmooth/GaussianLinearMGF module. All measures and moments are
the actual standard Gaussian ones; no concentration estimate is assumed.
-/

namespace GradientHessian.GaussianHilbert
open MeasureTheory ProbabilityTheory Filter
open scoped InnerProductSpace
noncomputable section

theorem standardGaussian_mgf (t : ℝ) :
    (∫ z : ℝ, Real.exp (t*z) ∂gaussianReal 0 1) = Real.exp (t^2/2) := by
  simpa [mgf] using (mgf_gaussianReal (X := id) (p := gaussianReal 0 1)
    (by simp : (gaussianReal 0 1).map id = gaussianReal 0 1) t)

theorem gaussianVector_exp_linear (d : ℕ) (t : Fin d → ℝ) :
    (∫ v : Fin d → ℝ, Real.exp (∑ i, t i * v i) ∂GaussianSquare.gaussianVector d) =
      Real.exp ((∑ i, (t i) ^ 2) / 2) := by
  simp_rw [Real.exp_sum]
  have hp : (∫ v : Fin d → ℝ, ∏ i, Real.exp (t i * v i)
      ∂GaussianSquare.gaussianVector d) =
      ∏ i, ∫ z : ℝ, Real.exp (t i * z) ∂gaussianReal 0 1 := by
    letI : MeasureSpace ℝ := ⟨gaussianReal 0 1⟩
    letI : SigmaFinite (volume : Measure ℝ) := by
      change SigmaFinite (gaussianReal 0 1)
      infer_instance
    exact integral_fintype_prod_eq_prod (Fin d) (fun i (z : ℝ) => Real.exp (t i * z))
  rw [hp]
  simp_rw [standardGaussian_mgf]
  rw [← Real.exp_sum, Finset.sum_div]

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

theorem euclideanGaussian_exp_inner (u : E) :
    (∫ z : E, Real.exp ⟪u, z⟫_ℝ ∂euclideanGaussianLaw E) = Real.exp (‖u‖ ^ 2 / 2) := by
  rw [euclideanGaussianLaw]
  have hf : StronglyMeasurable (fun z : E => Real.exp ⟪u, z⟫_ℝ) := by
    apply Continuous.stronglyMeasurable
    fun_prop
  rw [integral_map_of_stronglyMeasurable (gaussianSynthesis_continuous E).measurable hf]
  have he (v : Fin (Module.finrank ℝ E) → ℝ) :
      ⟪u, gaussianSynthesis E v⟫_ℝ = ∑ i, ⟪stdOrthonormalBasis ℝ E i, u⟫_ℝ * v i := by
    simp only [gaussianSynthesis, inner_sum, inner_smul_right, real_inner_comm u, mul_comm]
  simp_rw [he]
  rw [gaussianVector_exp_linear]
  have hn : (∑ i, ⟪stdOrthonormalBasis ℝ E i, u⟫_ℝ ^ 2) = ‖u‖ ^ 2 := by
    simpa only [Real.norm_eq_abs, sq_abs] using (stdOrthonormalBasis ℝ E).sum_sq_norm_inner u
  rw [hn]

theorem euclideanGaussian_exp_inner_integrable (u : E) :
    Integrable (fun z : E => Real.exp ⟪u, z⟫_ℝ) (euclideanGaussianLaw E) := by
  by_contra h
  have hi := euclideanGaussian_exp_inner E u
  rw [integral_undef h] at hi
  exact (Real.exp_ne_zero _).symm hi

theorem euclideanGaussian_mgf_inner (u : E) (t : ℝ) :
    (∫ z : E, Real.exp (t * ⟪u, z⟫_ℝ) ∂euclideanGaussianLaw E) =
      Real.exp (t^2 * ‖u‖^2 / 2) := by
  have h := euclideanGaussian_exp_inner E (t • u)
  simpa only [real_inner_smul_left, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] using h

theorem euclideanGaussian_mgf_inner_integrable (u : E) (t : ℝ) :
    Integrable (fun z : E => Real.exp (t * ⟪u, z⟫_ℝ)) (euclideanGaussianLaw E) := by
  simpa only [real_inner_smul_left] using euclideanGaussian_exp_inner_integrable E (t • u)

theorem euclideanGaussian_inner_right_tail (u : E) (hu : u ≠ 0) {a : ℝ} (ha : 0 < a) :
    (euclideanGaussianLaw E).real {z | a ≤ ⟪u,z⟫_ℝ} ≤
      Real.exp (-a^2/(2*‖u‖^2)) := by
  have hn : 0 < ‖u‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hu)
  let t := a / ‖u‖^2
  have ht : 0 < t := div_pos ha hn
  have hset : {z : E | Real.exp (t*a) ≤ Real.exp (t*⟪u,z⟫_ℝ)} =
      {z | a ≤ ⟪u,z⟫_ℝ} := by
    ext z
    simp only [Set.mem_setOf_eq, Real.exp_le_exp, mul_le_mul_left ht]
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (μ := euclideanGaussianLaw E) (f := fun z => Real.exp (t*⟪u,z⟫_ℝ))
    (ae_of_all _ fun _ => (Real.exp_pos _).le)
    (euclideanGaussian_mgf_inner_integrable E u t) (Real.exp (t*a))
  rw [hset, euclideanGaussian_mgf_inner] at hmarkov
  have hbound : (euclideanGaussianLaw E).real {z | a ≤ ⟪u,z⟫_ℝ} ≤
      Real.exp (t^2*‖u‖^2/2) / Real.exp (t*a) :=
    (le_div_iff₀ (Real.exp_pos _)).2 (by simpa only [mul_comm] using hmarkov)
  convert hbound using 1
  rw [← Real.exp_sub]
  congr 1
  dsimp [t]
  field_simp
  ring

theorem euclideanGaussian_inner_two_sided (u : E) (hu : u ≠ 0) {a : ℝ} (ha : 0 < a) :
    (euclideanGaussianLaw E).real {z | a ≤ |⟪u,z⟫_ℝ|} ≤
      2 * Real.exp (-a^2/(2*‖u‖^2)) := by
  have hs : {z : E | a ≤ |⟪u,z⟫_ℝ|} ⊆
      {z | a ≤ ⟪u,z⟫_ℝ} ∪ {z | a ≤ ⟪-u,z⟫_ℝ} := by
    intro z hz
    change a ≤ |⟪u,z⟫_ℝ| at hz
    rcases le_abs.mp hz with h | h
    · exact Or.inl h
    · exact Or.inr (by simpa only [inner_neg_left] using h)
  have hpos := euclideanGaussian_inner_right_tail E u hu ha
  have hneg := euclideanGaussian_inner_right_tail E (-u) (neg_ne_zero.mpr hu) ha
  rw [norm_neg] at hneg
  calc
    _ ≤ (euclideanGaussianLaw E).real
        ({z | a ≤ ⟪u,z⟫_ℝ} ∪ {z | a ≤ ⟪-u,z⟫_ℝ}) := measureReal_mono hs
    _ ≤ (euclideanGaussianLaw E).real {z | a ≤ ⟪u,z⟫_ℝ} +
        (euclideanGaussianLaw E).real {z | a ≤ ⟪-u,z⟫_ℝ} := measureReal_union_le _ _
    _ ≤ _ := by linarith

end
end GradientHessian.GaussianHilbert
