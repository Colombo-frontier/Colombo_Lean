import Nonsmooth.GaussianExponential
import Nonsmooth.SupportGram

open MeasureTheory ProbabilityTheory Function
open scoped Topology InnerProductSpace ENNReal
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem supportRowSynthesis_rows_continuous {k : ℕ} (c : Fin k → ℝ) :
      Continuous (fun b : Fin k → E => supportRowSynthesis b c) := by
  change Continuous (fun b : Fin k → E => ∑ i, c i • b i)
  exact continuous_finsetSum _ (fun i _ => continuous_const.smul (continuous_apply i))

theorem gaussianRows_unit_combination_law {k : ℕ} (c : Fin k → ℝ) (hc : ∑ i, (c i) ^ 2 = 1) :
    Measure.map (fun b : Fin k → E => supportRowSynthesis b c)
      (Measure.pi (fun _ : Fin k => euclideanGaussianLaw E)) = euclideanGaussianLaw E := by
  have hmeas := (supportRowSynthesis_rows_continuous (E := E) c).measurable
  letI : IsProbabilityMeasure (Measure.map (fun b : Fin k → E => supportRowSynthesis b c)
      (Measure.pi (fun _ : Fin k => euclideanGaussianLaw E))) := Measure.isProbabilityMeasure_map hmeas.aemeasurable
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_apply]
  have hfun : StronglyMeasurable (fun z : E => Complex.exp ((⟪z, t⟫_ℝ : ℂ) * Complex.I)) := by
    apply Continuous.stronglyMeasurable
    fun_prop
  rw [integral_map_of_stronglyMeasurable hmeas hfun]
  have he (b : Fin k → E) : Complex.exp ((⟪supportRowSynthesis b c, t⟫_ℝ : ℂ) * Complex.I) =
      ∏ i, Complex.exp ((⟪b i, (c i) • t⟫_ℝ : ℂ) * Complex.I) := by
    change Complex.exp ((⟪∑ i, c i • b i, t⟫_ℝ : ℂ) * Complex.I) = _
    simp only [sum_inner, real_inner_smul_left, inner_smul_right,
      Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum]
  simp_rw [he]
  have hp : (∫ b : Fin k → E, ∏ i, Complex.exp ((⟪b i, (c i) • t⟫_ℝ : ℂ) * Complex.I)
      ∂Measure.pi (fun _ : Fin k => euclideanGaussianLaw E)) =
      ∏ i, ∫ z : E, Complex.exp ((⟪z, (c i) • t⟫_ℝ : ℂ) * Complex.I) ∂euclideanGaussianLaw E := by
    letI : MeasureSpace E := ⟨euclideanGaussianLaw E⟩
    letI : SigmaFinite (volume : Measure E) := by
      change SigmaFinite (euclideanGaussianLaw E)
      infer_instance
    exact integral_fintype_prod_eq_prod
      (fun (i : Fin k) (z : E) => Complex.exp ((⟪z, (c i) • t⟫_ℝ : ℂ) * Complex.I))
  rw [hp]
  have hi (i : Fin k) : (∫ z : E, Complex.exp ((⟪z, (c i) • t⟫_ℝ : ℂ) * Complex.I) ∂euclideanGaussianLaw E) =
      Complex.exp (-(‖(c i) • t‖ : ℂ) ^ 2 / 2) := euclideanGaussian_characteristic _
  simp_rw [hi]
  rw [← Complex.exp_sum, euclideanGaussian_characteristic]
  congr 1
  have hn (i : Fin k) : (‖(c i) • t‖ : ℂ) ^ 2 = (c i : ℂ) ^ 2 * (‖t‖ : ℂ) ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, Complex.ofReal_mul, mul_pow, ← Complex.ofReal_pow, sq_abs,
      Complex.ofReal_pow]
  simp_rw [hn]
  rw [← Finset.sum_div, Finset.sum_neg_distrib, ← Finset.sum_mul]
  have hcc : (∑ i, (c i : ℂ) ^ 2) = 1 := by exact_mod_cast hc
  rw [hcc, one_mul]

theorem gaussianRows_unit_combination_concentration {k : ℕ} (c : Fin k → ℝ) (hc : ∑ i, (c i) ^ 2 = 1) :
    (Measure.pi (fun _ : Fin k => euclideanGaussianLaw E)).real
      {b : Fin k → E | ‖supportRowSynthesis b c‖ ^ 2 < (Module.finrank ℝ E : ℝ) / 2 ∨
        2 * (Module.finrank ℝ E : ℝ) < ‖supportRowSynthesis b c‖ ^ 2} ≤
          2 * Real.exp (-(Module.finrank ℝ E : ℝ) / 32) := by
  have hs : MeasurableSet {z : E | ‖z‖ ^ 2 < (Module.finrank ℝ E : ℝ) / 2 ∨
      2 * (Module.finrank ℝ E : ℝ) < ‖z‖ ^ 2} :=
    (measurableSet_lt (continuous_norm.pow 2).measurable measurable_const).union
      (measurableSet_lt measurable_const (continuous_norm.pow 2).measurable)
  have hm := map_measureReal_apply (μ := Measure.pi (fun _ : Fin k => euclideanGaussianLaw E))
    (supportRowSynthesis_rows_continuous c).measurable hs
  rw [gaussianRows_unit_combination_law c hc] at hm
  exact hm.symm.trans_le euclideanGaussian_square_two_sided_exponential

end
end Nonsmooth
