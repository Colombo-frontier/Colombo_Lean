import HeavyTail.GaussianLowerProduct

/-! The exponential tilt of the concrete Euclidean Gaussian is exactly its
translation. This is an equality of measures obtained from scalar densities,
finite-product measures, and the orthonormal synthesis map. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators InnerProductSpace NNReal ENNReal
namespace HeavyTail.GaussianLower
noncomputable section

theorem map_withDensity_comp {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (P : Measure Ω) {f : Ω → Ξ} {r : Ξ → ℝ≥0∞}
    (hf : Measurable f) (hr : Measurable r) :
    (P.withDensity (r ∘ f)).map f = (P.map f).withDensity r := by
  ext s hs
  rw [Measure.map_apply hf hs, withDensity_apply _ (hf hs),
    withDensity_apply _ hs, Measure.restrict_map hf hs, lintegral_map hr hf]
  rfl

theorem coordinateGaussian_affine_map {k : ℕ} (μ : Fin k → ℝ) (σ : ℝ) :
    (GaussianEstimates.gaussianVector k).map (fun z i ↦ μ i + σ * z i) =
      coordinateGaussianLaw μ σ := by
  unfold coordinateGaussianLaw
  apply (Measure.pi_eq ?_).symm
  intro s hs
  rw [Measure.map_apply (by fun_prop) (MeasurableSet.univ_pi hs)]
  have he : (fun z : Fin k → ℝ ↦ fun i ↦ μ i + σ * z i) ⁻¹' Set.univ.pi s =
      Set.univ.pi (fun i ↦ (fun y : ℝ ↦ μ i + σ * y) ⁻¹' s i) := by
    ext z
    simp
  rw [he, GaussianEstimates.gaussianVector, Measure.pi_pi]
  apply Finset.prod_congr rfl
  intro i hi
  rw [← scalar_gaussian_affine_sample (μ i) σ,
    Measure.map_apply (by fun_prop) (hs i)]

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

def gaussianCoordinates (t : E) : Fin (Module.finrank ℝ E) → ℝ :=
  fun i ↦ ⟪stdOrthonormalBasis ℝ E i, t⟫_ℝ

omit [MeasurableSpace E] [BorelSpace E] in
theorem gaussianSynthesis_translate (t : E) (z : Fin (Module.finrank ℝ E) → ℝ) :
    GaussianEstimates.gaussianSynthesis E (fun i ↦ gaussianCoordinates E t i + z i) =
      t + GaussianEstimates.gaussianSynthesis E z := by
  simp only [GaussianEstimates.gaussianSynthesis, add_smul, Finset.sum_add_distrib,
    gaussianCoordinates, (stdOrthonormalBasis ℝ E).sum_repr']

omit [MeasurableSpace E] [BorelSpace E] in
theorem coordinateRatio_synthesis (t : E) (z : Fin (Module.finrank ℝ E) → ℝ) :
    coordinateRatio (gaussianCoordinates E t) (fun _ ↦ 0) 1 z =
      exponentialRatio t (GaussianEstimates.gaussianSynthesis E z) := by
  simp only [coordinateRatio, scalarRatio, sub_zero, one_pow, div_one, mul_one]
  rw [← Real.exp_sum]
  unfold exponentialRatio
  congr 1
  have hn : (∑ i, gaussianCoordinates E t i ^ 2) = ‖t‖ ^ 2 := by
    simpa only [gaussianCoordinates, Real.norm_eq_abs, sq_abs] using
      (stdOrthonormalBasis ℝ E).sum_sq_norm_inner t
  simp only [Finset.sum_sub_distrib, ← Finset.sum_div, hn]
  congr 1
  simp only [GaussianEstimates.gaussianSynthesis, inner_sum, inner_smul_right,
    gaussianCoordinates, real_inner_comm t, mul_comm]

/-- Cameron--Martin translation identity for the concrete standard finite-dimensional Gaussian. -/
theorem euclideanGaussian_translation (t : E) :
    (GaussianEstimates.euclideanGaussianLaw E).withDensity
      (fun z ↦ ENNReal.ofReal (exponentialRatio t z)) =
      (GaussianEstimates.euclideanGaussianLaw E).map (fun z ↦ t + z) := by
  have hm : Measurable (GaussianEstimates.gaussianSynthesis E) :=
    (GaussianEstimates.gaussianSynthesis_continuous E).measurable
  have hr : Measurable (fun z ↦ ENNReal.ofReal (exponentialRatio t z)) := by
    unfold exponentialRatio
    fun_prop
  have hz : coordinateGaussianLaw (fun _ : Fin (Module.finrank ℝ E) ↦ 0) 1 =
      GaussianEstimates.gaussianVector (Module.finrank ℝ E) := by
    simp [coordinateGaussianLaw, GaussianEstimates.gaussianVector]
  have hratio : (fun z ↦ ENNReal.ofReal (exponentialRatio t z)) ∘
      GaussianEstimates.gaussianSynthesis E = fun z ↦ ENNReal.ofReal
        (coordinateRatio (gaussianCoordinates E t) (fun _ ↦ 0) 1 z) := by
    funext z
    rw [Function.comp_apply, coordinateRatio_synthesis]
  change ((GaussianEstimates.gaussianVector (Module.finrank ℝ E)).map
      (GaussianEstimates.gaussianSynthesis E)).withDensity _ = _
  rw [← map_withDensity_comp _ hm hr, hratio, ← hz,
    ← coordinateGaussian_change_of_measure (by norm_num : (1 : ℝ) ≠ 0),
    ← coordinateGaussian_affine_map]
  simp only [one_mul]
  rw [Measure.map_map hm (by fun_prop)]
  unfold GaussianEstimates.euclideanGaussianLaw
  rw [Measure.map_map (by fun_prop) hm]
  congr 1
  funext z
  exact gaussianSynthesis_translate E t z

end
end HeavyTail.GaussianLower
