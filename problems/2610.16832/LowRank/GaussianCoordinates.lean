import LowRank.GaussianRotation
import LowRank.GaussianModel

/-! Bridges the independent scalar-coordinate Gaussian distribution to the
Euclidean Gaussian used by the orthogonal-invariance theorems. -/

namespace LowRank
open MeasureTheory ProbabilityTheory
open scoped BigOperators InnerProductSpace
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] {n : ℕ}

def basisCoordinates (b : OrthonormalBasis (Fin n) ℝ E) : E ≃L[ℝ] (Fin n → ℝ) :=
  b.repr.toContinuousLinearEquiv.trans (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ))

theorem basisCoordinates_symm_apply (b : OrthonormalBasis (Fin n) ℝ E) (v : Fin n → ℝ) :
    (basisCoordinates b).symm v = ∑ i, v i • b i := by
  exact (b.sum_repr_symm ((WithLp.equiv 2 (Fin n → ℝ)).symm v)).symm

theorem standardVectorLaw_basis_synthesis (b : OrthonormalBasis (Fin n) ℝ E) :
    (standardVectorLaw n).map (basisCoordinates b).symm = euclideanGaussianLaw E := by
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_apply]
  have hf : StronglyMeasurable (fun z : E => Complex.exp ((⟪z, t⟫_ℝ : ℂ) * Complex.I)) :=
    (by fun_prop : Continuous _).stronglyMeasurable
  rw [integral_map_of_stronglyMeasurable (basisCoordinates b).symm.continuous.measurable hf]
  simp_rw [basisCoordinates_symm_apply, sum_inner, real_inner_smul_left]
  have hs : (∫ v : Fin n → ℝ, Complex.exp (((∑ i, v i * ⟪b i, t⟫_ℝ : ℝ) : ℂ) * Complex.I)
      ∂standardVectorLaw n) = Complex.exp (-((∑ i, ⟪b i, t⟫_ℝ ^ 2 : ℝ) : ℂ) / 2) := by
    simpa only [mul_comm] using standardVectorLaw_characteristic n (fun i => ⟪b i, t⟫_ℝ)
  rw [hs, euclideanGaussian_characteristic]
  have hn : (∑ i, ⟪b i, t⟫_ℝ ^ 2) = ‖t‖ ^ 2 := by
    simpa only [Real.norm_eq_abs, sq_abs] using b.sum_sq_norm_inner t
  rw [hn, Complex.ofReal_pow]

theorem gaussian_basis_coordinates (b : OrthonormalBasis (Fin n) ℝ E) :
    (euclideanGaussianLaw E).map (basisCoordinates b) = standardVectorLaw n := by
  rw [← standardVectorLaw_basis_synthesis b,
    Measure.map_map (basisCoordinates b).continuous.measurable
      (basisCoordinates b).symm.continuous.measurable]
  simp only [Function.comp_def, ContinuousLinearEquiv.apply_symm_apply, Measure.map_id']

/-- An orthogonal transformation acting on independent scalar coordinates. -/
def coordinateRotation (b : OrthonormalBasis (Fin n) ℝ E) (e : E ≃ₗᵢ[ℝ] E) :
    (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ) :=
  ((basisCoordinates b).symm.trans e.toContinuousLinearEquiv).trans (basisCoordinates b)

theorem coordinateRotation_apply (b : OrthonormalBasis (Fin n) ℝ E) (e : E ≃ₗᵢ[ℝ] E)
    (z : Fin n → ℝ) :
    coordinateRotation b e z = basisCoordinates b (e ((basisCoordinates b).symm z)) := rfl

theorem standardVectorLaw_coordinateRotation (b : OrthonormalBasis (Fin n) ℝ E)
    (e : E ≃ₗᵢ[ℝ] E) :
    (standardVectorLaw n).map (coordinateRotation b e) = standardVectorLaw n := by
  change (standardVectorLaw n).map
    ((basisCoordinates b) ∘ e ∘ (basisCoordinates b).symm) = _
  rw [← Measure.map_map (basisCoordinates b).continuous.measurable
    (e.continuous.measurable.comp (basisCoordinates b).symm.continuous.measurable)]
  rw [← Measure.map_map e.continuous.measurable (basisCoordinates b).symm.continuous.measurable,
    standardVectorLaw_basis_synthesis, euclideanGaussian_isometry, gaussian_basis_coordinates]

def iidVectorLaw (n : ℕ) (v : NNReal) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ => gaussianReal 0 v)

instance iidVectorLaw_probability (n : ℕ) (v : NNReal) : IsProbabilityMeasure (iidVectorLaw n v) := by
  unfold iidVectorLaw
  infer_instance

theorem standardVectorLaw_scale (n : ℕ) (σ : ℝ) :
    (standardVectorLaw n).map (fun z => σ • z) = iidVectorLaw n ⟨σ ^ 2, sq_nonneg σ⟩ := by
  have h := measurePreserving_pi (fun _ : Fin n => gaussianReal 0 1)
    (fun _ : Fin n => gaussianReal 0 ⟨σ ^ 2, sq_nonneg σ⟩)
    (fun _ => (show MeasurePreserving (fun x : ℝ => σ * x)
      (gaussianReal 0 1) (gaussianReal 0 ⟨σ ^ 2, sq_nonneg σ⟩) from
      ⟨measurable_const.mul measurable_id, by simpa using gaussianReal_map_const_mul (μ := 0) (v := 1) σ⟩))
  exact h.map_eq

theorem iidVectorLaw_as_scaled (n : ℕ) (v : NNReal) :
    iidVectorLaw n v = (standardVectorLaw n).map (fun z => Real.sqrt v • z) := by
  rw [standardVectorLaw_scale]
  congr 1
  exact NNReal.eq (Real.sq_sqrt v.coe_nonneg).symm

theorem iidVectorLaw_coordinateRotation (b : OrthonormalBasis (Fin n) ℝ E)
    (e : E ≃ₗᵢ[ℝ] E) (v : NNReal) :
    (iidVectorLaw n v).map (coordinateRotation b e) = iidVectorLaw n v := by
  have hscale : Measurable (fun z : Fin n → ℝ => Real.sqrt v • z) :=
    measurable_const.smul measurable_id
  rw [iidVectorLaw_as_scaled n v, Measure.map_map (coordinateRotation b e).continuous.measurable hscale]
  have heq : (coordinateRotation b e) ∘ (fun z => Real.sqrt v • z) =
      (fun z => Real.sqrt v • z) ∘ (coordinateRotation b e) := by
    funext z
    exact (coordinateRotation b e).map_smul _ _
  rw [heq, ← Measure.map_map hscale
    (coordinateRotation b e).continuous.measurable, standardVectorLaw_coordinateRotation]

end
end LowRank
