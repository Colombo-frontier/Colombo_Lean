import GaussianMapKL254
import GaussianFloor254

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Matrix
open scoped ENNReal NNReal BigOperators Matrix
namespace Paper254

theorem coordinateKL_inverse (q a r : ℝ) (hq : 0 < q) (ha : 0 < a) :
    coordinateKL q a⁻¹ r=(q*a-1-Real.log (q*a)+a*r^2)/2 := by
  unfold coordinateKL covariancePenalty
  have he : a⁻¹/q=(q*a)⁻¹ := by field_simp
  rw [he,Real.log_inv]
  simp only [div_inv_eq_mul]
  ring

def PrecisionGaussian.gaussianMeasure {d : ℕ} (P : PrecisionGaussian d) : Measure (Coordinates d) :=
  rotatedGaussian (star P.positive.isHermitian.eigenvectorUnitary) P.mean
    (fun i => ⟨(P.positive.isHermitian.eigenvalues i)⁻¹,(inv_pos.mpr (P.positive.eigenvalues_pos i)).le⟩)

/-- Full SPD matrices are represented by orthogonal eigen-coordinates.
The comparator is isotropic in those coordinates; no diagonality of P is assumed. -/
theorem PrecisionGaussian.kl_equals_potential {d : ℕ} (P : PrecisionGaussian d)
    (u : Coordinates d) (q : ℝ≥0) (hq : q ≠ 0) :
    klDiv (rotatedGaussian (star P.positive.isHermitian.eigenvectorUnitary) u (fun _ => q))
      P.gaussianMeasure=ENNReal.ofReal (P.potential q u) := by
  let U := star P.positive.isHermitian.eigenvectorUnitary
  let a := P.positive.isHermitian.eigenvalues
  have ha : ∀ i,0 < a i := P.positive.eigenvalues_pos
  have hqr : 0 < (q:ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hq)
  have hn : ∀ i,(⟨(a i)⁻¹,(inv_pos.mpr (ha i)).le⟩ : ℝ≥0) ≠ 0 := by
    intro i
    exact (show (0:ℝ≥0)<⟨(a i)⁻¹,(inv_pos.mpr (ha i)).le⟩ from inv_pos.mpr (ha i)).ne'
  have hk := rotatedGaussian_kl U u P.mean (fun _ => q)
    (fun i => ⟨(a i)⁻¹,(inv_pos.mpr (ha i)).le⟩) (fun _ => hq) hn
  change klDiv (rotatedGaussian U u (fun _ => q))
    (rotatedGaussian U P.mean (fun i => ⟨(a i)⁻¹,(inv_pos.mpr (ha i)).le⟩))=_
  rw [hk]
  congr 1
  unfold PrecisionGaussian.potential
  rw [precision_spectral_rotated P.positive,rotatedPrecision_potential U a (u-P.mean) q hqr ha]
  apply Finset.sum_congr rfl
  intro i _
  exact coordinateKL_inverse q (a i) _ hqr (ha i)

end Paper254
#print axioms Paper254.PrecisionGaussian.kl_equals_potential
