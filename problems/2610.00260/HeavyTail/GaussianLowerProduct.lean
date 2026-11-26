import HeavyTail.GaussianLowerLikelihood

/-! Actual finite-product Gaussian laws and their likelihood-ratio moments. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
namespace HeavyTail.GaussianLower
noncomputable section

def coordinateGaussianLaw {k : ℕ} (μ : Fin k → ℝ) (σ : ℝ) : Measure (Fin k → ℝ) :=
  Measure.pi fun i ↦ gaussianReal (μ i) ⟨σ ^ 2, sq_nonneg σ⟩

instance coordinateGaussianLaw_probability {k : ℕ} (μ : Fin k → ℝ) (σ : ℝ) :
    IsProbabilityMeasure (coordinateGaussianLaw μ σ) := by
  unfold coordinateGaussianLaw
  infer_instance

def coordinateRatio {k : ℕ} (μ ν : Fin k → ℝ) (σ : ℝ) (y : Fin k → ℝ) : ℝ :=
  ∏ i, scalarRatio (μ i) (ν i) σ (y i)

theorem coordinateRatio_pos {k : ℕ} (μ ν : Fin k → ℝ) (σ : ℝ) (y : Fin k → ℝ) :
    0 < coordinateRatio μ ν σ y :=
  Finset.prod_pos fun _ _ ↦ scalarRatio_pos _ _ _ _

theorem coordinateRatio_measurable {k : ℕ} (μ ν : Fin k → ℝ) (σ : ℝ) :
    Measurable (coordinateRatio μ ν σ) := by
  unfold coordinateRatio
  exact Finset.measurable_prod _ fun i _ ↦
    (scalarRatio_measurable _ _ _).comp (measurable_pi_apply i)

private theorem product_integrable {k : ℕ} (ν : Fin k → Measure ℝ)
    [∀ i, SigmaFinite (ν i)] {f : Fin k → ℝ → ℝ}
    (hf : ∀ i, Integrable (f i) (ν i)) :
    Integrable (fun y : Fin k → ℝ ↦ ∏ i, f i (y i)) (Measure.pi ν) := by
  exact @Integrable.fintype_prod_dep ℝ _ (Fin k) _ (fun _ ↦ ℝ) f
    (fun i ↦ ⟨ν i⟩) (fun i ↦ inferInstance) hf

private theorem product_integral {k : ℕ} (ν : Fin k → Measure ℝ)
    [∀ i, SigmaFinite (ν i)] (f : Fin k → ℝ → ℝ) :
    (∫ y : Fin k → ℝ, ∏ i, f i (y i) ∂Measure.pi ν) =
      ∏ i, ∫ y, f i y ∂ν i := by
  exact @integral_fintype_prod_eq_prod ℝ _ (Fin k) _ (fun _ ↦ ℝ) f
    (fun i ↦ ⟨ν i⟩) (fun i ↦ inferInstance)

theorem coordinateRatio_mean {k : ℕ} {σ : ℝ} (hσ : σ ≠ 0) (μ ν : Fin k → ℝ) :
    (∫ y, coordinateRatio μ ν σ y ∂coordinateGaussianLaw ν σ) = 1 := by
  simp only [coordinateGaussianLaw, coordinateRatio]
  rw [product_integral _ (fun i y ↦ scalarRatio (μ i) (ν i) σ y)]
  simp_rw [scalarRatio_mean hσ]
  simp

theorem coordinateRatio_integrable {k : ℕ} {σ : ℝ} (hσ : σ ≠ 0) (μ ν : Fin k → ℝ) :
    Integrable (coordinateRatio μ ν σ) (coordinateGaussianLaw ν σ) :=
  integrable_of_integral_eq_one (coordinateRatio_mean hσ μ ν)

theorem coordinateRatio_second {k : ℕ} {σ : ℝ} (hσ : σ ≠ 0) (μ ν : Fin k → ℝ) :
    (∫ y, coordinateRatio μ ν σ y ^ 2 ∂coordinateGaussianLaw ν σ) =
      Real.exp (∑ i, ((μ i - ν i) / σ) ^ 2) := by
  simp only [coordinateRatio, ← Finset.prod_pow]
  rw [coordinateGaussianLaw, product_integral _ (fun i y ↦ scalarRatio (μ i) (ν i) σ y ^ 2)]
  simp_rw [scalarRatio_second hσ]
  rw [Real.exp_sum]

/-- The actual shifted product measure is the base measure weighted by this ratio. -/
theorem coordinateGaussian_change_of_measure {k : ℕ} {σ : ℝ} (hσ : σ ≠ 0)
    (μ ν : Fin k → ℝ) :
    coordinateGaussianLaw μ σ = (coordinateGaussianLaw ν σ).withDensity
      (fun y ↦ ENNReal.ofReal (coordinateRatio μ ν σ y)) := by
  unfold coordinateGaussianLaw
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), Measure.restrict_pi_pi]
  have hi (i : Fin k) : Integrable (scalarRatio (μ i) (ν i) σ)
      ((gaussianReal (ν i) ⟨σ ^ 2, sq_nonneg σ⟩).restrict (s i)) :=
    (integrable_of_integral_eq_one (scalarRatio_mean hσ (μ i) (ν i))).restrict
  have hip := product_integrable
    (fun i ↦ (gaussianReal (ν i) ⟨σ ^ 2, sq_nonneg σ⟩).restrict (s i)) hi
  simp only [coordinateRatio]
  rw [← ofReal_integral_eq_lintegral_ofReal hip
    (Filter.Eventually.of_forall fun y ↦ (coordinateRatio_pos μ ν σ y).le)]
  rw [product_integral _ (fun i y ↦ scalarRatio (μ i) (ν i) σ y), ENNReal.ofReal_prod_of_nonneg
    (fun i _ ↦ integral_nonneg fun y ↦ (scalarRatio_pos (μ i) (ν i) σ y).le)]
  apply Finset.prod_congr rfl
  intro i hi'
  rw [scalar_gaussian_change_of_measure hσ (μ i) (ν i), withDensity_apply _ (hs i)]
  exact ofReal_integral_eq_lintegral_ofReal (hi i)
    (Filter.Eventually.of_forall fun y ↦ (scalarRatio_pos (μ i) (ν i) σ y).le)

end
end HeavyTail.GaussianLower
