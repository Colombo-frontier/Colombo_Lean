import GradientHessian.GaussianTail
import Mathlib.Probability.Distributions.Gaussian
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.CharacteristicFunction
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection
import Mathlib.Tactic

/-! A self-contained standard Gaussian law and its orthogonal invariance.
The characteristic-function proof is adapted from the locally verified
Nonsmooth/GaussianCharacteristic.lean, with only Mathlib dependencies here. Reused from the checked NCBall/GaussianHilbert module, preserving its characteristic-function proof. -/

namespace GradientHessian.GaussianHilbert
open MeasureTheory ProbabilityTheory
open scoped BigOperators InnerProductSpace
noncomputable section

theorem gaussianVector_characteristic (d : ℕ) (t : Fin d → ℝ) :
    (∫ v : Fin d → ℝ, Complex.exp (((∑ i, t i * v i : ℝ) : ℂ) * Complex.I)
      ∂GaussianSquare.gaussianVector d) = Complex.exp (-((∑ i, (t i) ^ 2 : ℝ) : ℂ) / 2) := by
  have he (v : Fin d → ℝ) :
      Complex.exp (((∑ i, t i * v i : ℝ) : ℂ) * Complex.I) =
        ∏ i, Complex.exp ((t i : ℂ) * (v i : ℂ) * Complex.I) := by
    rw [Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum]
    simp only [Complex.ofReal_mul]
  simp_rw [he]
  have hp : (∫ v : Fin d → ℝ, ∏ i, Complex.exp ((t i : ℂ) * (v i : ℂ) * Complex.I)
      ∂GaussianSquare.gaussianVector d) =
        ∏ i, ∫ z : ℝ, Complex.exp ((t i : ℂ) * (z : ℂ) * Complex.I) ∂gaussianReal 0 1 := by
    letI : MeasureSpace ℝ := ⟨gaussianReal 0 1⟩
    letI : SigmaFinite (volume : Measure ℝ) := by
      change SigmaFinite (gaussianReal 0 1)
      infer_instance
    exact integral_fintype_prod_eq_prod (Fin d)
      (fun i (z : ℝ) => Complex.exp ((t i : ℂ) * (z : ℂ) * Complex.I))
  rw [hp]
  have hg (i : Fin d) :
      (∫ z : ℝ, Complex.exp ((t i : ℂ) * (z : ℂ) * Complex.I) ∂gaussianReal 0 1) =
        Complex.exp (-(t i : ℂ) ^ 2 / 2) := by
    simpa only [charFun_apply_real, Complex.ofReal_zero, Complex.ofReal_one,
      NNReal.coe_one, mul_zero, zero_mul, zero_sub, one_mul, neg_div] using
      (charFun_gaussianReal (μ := 0) (v := 1) (t i))
  simp_rw [hg]
  rw [← Complex.exp_sum]
  congr 1
  simp only [Complex.ofReal_sum, Complex.ofReal_pow, ← Finset.sum_neg_distrib,
    ← Finset.sum_div]

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

def gaussianSynthesis (v : Fin (Module.finrank ℝ E) → ℝ) : E :=
  ∑ i, v i • stdOrthonormalBasis ℝ E i

omit [MeasurableSpace E] [BorelSpace E] in
theorem gaussianSynthesis_continuous : Continuous (gaussianSynthesis E) := by
  unfold gaussianSynthesis
  exact continuous_finset_sum _ (fun i _ => (continuous_apply i).smul continuous_const)

def euclideanGaussianLaw : Measure E :=
  (GaussianSquare.gaussianVector (Module.finrank ℝ E)).map (gaussianSynthesis E)

instance euclideanGaussianLaw_probability : IsProbabilityMeasure (euclideanGaussianLaw E) := by
  unfold euclideanGaussianLaw
  exact isProbabilityMeasure_map (gaussianSynthesis_continuous E).measurable.aemeasurable

theorem euclideanGaussian_characteristic (t : E) :
    charFun (euclideanGaussianLaw E) t = Complex.exp (-(‖t‖ : ℂ) ^ 2 / 2) := by
  rw [charFun_apply, euclideanGaussianLaw]
  have hf : StronglyMeasurable (fun z : E => Complex.exp ((⟪z, t⟫_ℝ : ℂ) * Complex.I)) := by
    apply Continuous.stronglyMeasurable
    fun_prop
  rw [integral_map_of_stronglyMeasurable (gaussianSynthesis_continuous E).measurable hf]
  have he (v : Fin (Module.finrank ℝ E) → ℝ) :
      ⟪gaussianSynthesis E v, t⟫_ℝ = ∑ i, ⟪stdOrthonormalBasis ℝ E i, t⟫_ℝ * v i := by
    simp only [gaussianSynthesis, sum_inner, real_inner_smul_left, mul_comm]
  simp_rw [he]
  rw [gaussianVector_characteristic]
  have hn : (∑ i, ⟪stdOrthonormalBasis ℝ E i, t⟫_ℝ ^ 2) = ‖t‖ ^ 2 := by
    simpa only [Real.norm_eq_abs, sq_abs] using (stdOrthonormalBasis ℝ E).sum_sq_norm_inner t
  rw [hn, Complex.ofReal_pow]

theorem euclideanGaussian_isometry (e : E ≃ₗᵢ[ℝ] E) :
    (euclideanGaussianLaw E).map e = euclideanGaussianLaw E := by
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_apply]
  have hf : StronglyMeasurable (fun z : E => Complex.exp ((⟪z, t⟫_ℝ : ℂ) * Complex.I)) := by
    apply Continuous.stronglyMeasurable
    fun_prop
  rw [integral_map_of_stronglyMeasurable e.continuous.measurable hf]
  simp_rw [e.inner_map_eq_flip]
  change charFun (euclideanGaussianLaw E) (e.symm t) = _
  rw [euclideanGaussian_characteristic, euclideanGaussian_characteristic, e.symm.norm_map]

omit [MeasurableSpace E] [BorelSpace E] in
theorem gaussianSynthesis_coordinate (v : Fin (Module.finrank ℝ E) → ℝ)
    (i : Fin (Module.finrank ℝ E)) :
    ⟪stdOrthonormalBasis ℝ E i, gaussianSynthesis E v⟫_ℝ = v i := by
  simp only [gaussianSynthesis, inner_sum, inner_smul_right,
    (orthonormal_iff_ite.mp (stdOrthonormalBasis ℝ E).orthonormal)]
  simp

omit [MeasurableSpace E] [BorelSpace E] in
theorem gaussianSynthesis_norm_square (v : Fin (Module.finrank ℝ E) → ℝ) :
    ‖gaussianSynthesis E v‖ ^ 2 = GaussianSquare.energy v := by
  simpa only [Real.norm_eq_abs, sq_abs, gaussianSynthesis_coordinate, GaussianSquare.energy] using
    ((stdOrthonormalBasis ℝ E).sum_sq_norm_inner (gaussianSynthesis E v)).symm

/-- The exact manuscript chi-square tail, expressed using the actual Hilbert
norm and the standard Gaussian measure in its orthonormal coordinates. -/
theorem norm_square_two_sided [Nontrivial E] {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    (euclideanGaussianLaw E).real
      {z | u < |‖z‖ ^ 2 / (Module.finrank ℝ E : ℝ) - 1|} ≤
      2 * Real.exp (-(Module.finrank ℝ E : ℝ) * u ^ 2 / 8) := by
  have hm : MeasurableSet {z : E | u < |‖z‖ ^ 2 / (Module.finrank ℝ E : ℝ) - 1|} := by
    apply measurableSet_lt measurable_const
    fun_prop
  rw [measureReal_def, euclideanGaussianLaw,
    Measure.map_apply (gaussianSynthesis_continuous E).measurable hm]
  have he : (gaussianSynthesis E) ⁻¹'
      {z : E | u < |‖z‖ ^ 2 / (Module.finrank ℝ E : ℝ) - 1|} =
      {v | u < |GaussianSquare.energy v / (Module.finrank ℝ E : ℝ) - 1|} := by
    ext v
    simp only [Set.mem_preimage, Set.mem_setOf_eq, gaussianSynthesis_norm_square]
  rw [he]
  exact GaussianSquare.chi_square_two_sided Module.finrank_pos hu hu1

theorem norm_square_lower_tail {u : ℝ} (hu : 0 < u) :
    (euclideanGaussianLaw E).real
      {z | ‖z‖ ^ 2 ≤ (Module.finrank ℝ E : ℝ)*(1-u)} ≤
      Real.exp (-(Module.finrank ℝ E : ℝ) * u ^ 2 / 4) := by
  have hm : MeasurableSet {z : E | ‖z‖ ^ 2 ≤ (Module.finrank ℝ E : ℝ)*(1-u)} := by
    apply measurableSet_le
    · fun_prop
    · exact measurable_const
  rw [measureReal_def, euclideanGaussianLaw,
    Measure.map_apply (gaussianSynthesis_continuous E).measurable hm]
  have he : (gaussianSynthesis E) ⁻¹'
      {z : E | ‖z‖ ^ 2 ≤ (Module.finrank ℝ E : ℝ)*(1-u)} =
      {v | GaussianSquare.energy v ≤ (Module.finrank ℝ E : ℝ)*(1-u)} := by
    ext v
    simp only [Set.mem_preimage, Set.mem_setOf_eq, gaussianSynthesis_norm_square]
  rw [he]
  exact GaussianSquare.chi_square_lower_tail _ hu

theorem euclideanGaussian_no_atom_zero [Nontrivial E] : euclideanGaussianLaw E {0} = 0 := by
  letI : NoAtoms (gaussianReal 0 1) := ⟨fun x =>
    (gaussianReal_absolutelyContinuous 0 (by norm_num : (1:NNReal) ≠ 0)) (measure_singleton x)⟩
  letI : NeZero (Module.finrank ℝ E) := ⟨Nat.ne_of_gt Module.finrank_pos⟩
  have he : (gaussianSynthesis E) ⁻¹' ({0} : Set E) = {0} := by
    ext v
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h
      funext i
      have hc := gaussianSynthesis_coordinate E v i
      rw [h, inner_zero_right] at hc
      exact hc.symm
    · intro h
      simp [h, gaussianSynthesis]
  rw [euclideanGaussianLaw, Measure.map_apply (gaussianSynthesis_continuous E).measurable
    (measurableSet_singleton 0), he, GaussianSquare.gaussianVector]
  exact measure_singleton _

end
end GradientHessian.GaussianHilbert
