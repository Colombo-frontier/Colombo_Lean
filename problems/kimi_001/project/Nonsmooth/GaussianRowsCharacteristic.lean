import Nonsmooth.GaussianCombination

open MeasureTheory ProbabilityTheory Function
open scoped InnerProductSpace ENNReal Topology
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

theorem finite_rows_measure_ext_characteristic {k : ℕ} (μ ν : Measure (Fin k → E))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ t : Fin k → E,
      (∫ b : Fin k → E, Complex.exp (((∑ i, ⟪b i, t i⟫_ℝ : ℝ) : ℂ) * Complex.I) ∂μ) =
        ∫ b : Fin k → E, Complex.exp (((∑ i, ⟪b i, t i⟫_ℝ : ℝ) : ℂ) * Complex.I) ∂ν) : μ = ν := by
  letI : MeasurableSpace (PiLp 2 (fun _ : Fin k => E)) := borel _
  letI : BorelSpace (PiLp 2 (fun _ : Fin k => E)) := ⟨rfl⟩
  let e : PiLp 2 (fun _ : Fin k => E) ≃L[ℝ] (Fin k → E) :=
    PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin k => E)
  have he : Measure.map e.symm μ = Measure.map e.symm ν := by
    apply Measure.ext_of_charFun
    funext t
    simp only [charFun_apply]
    have hc : StronglyMeasurable (fun x : PiLp 2 (fun _ : Fin k => E) =>
      Complex.exp ((⟪x, t⟫_ℝ : ℂ) * Complex.I)) := by
      apply Continuous.stronglyMeasurable
      fun_prop
    rw [integral_map_of_stronglyMeasurable e.symm.continuous.measurable hc,
      integral_map_of_stronglyMeasurable e.symm.continuous.measurable hc]
    exact h (fun i => t i)
  have hmap := congrArg (Measure.map e) he
  rw [Measure.map_map e.continuous.measurable e.symm.continuous.measurable,
    Measure.map_map e.continuous.measurable e.symm.continuous.measurable] at hmap
  simp only [Function.comp_def, e.apply_symm_apply] at hmap
  change Measure.map id μ = Measure.map id ν at hmap
  simpa only [Measure.map_id] using hmap

variable [Nontrivial E]

theorem gaussianRows_characteristic {k : ℕ} (t : Fin k → E) :
    (∫ b : Fin k → E, Complex.exp (((∑ i, ⟪b i, t i⟫_ℝ : ℝ) : ℂ) * Complex.I)
      ∂Measure.pi (fun _ : Fin k => euclideanGaussianLaw E)) =
        Complex.exp (-((∑ i, ‖t i‖ ^ 2 : ℝ) : ℂ) / 2) := by
  simp only [Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum]
  have hp : (∫ b : Fin k → E, ∏ i, Complex.exp ((⟪b i, t i⟫_ℝ : ℂ) * Complex.I)
      ∂Measure.pi (fun _ : Fin k => euclideanGaussianLaw E)) =
      ∏ i, ∫ z : E, Complex.exp ((⟪z, t i⟫_ℝ : ℂ) * Complex.I) ∂euclideanGaussianLaw E := by
    letI : MeasureSpace E := ⟨euclideanGaussianLaw E⟩
    letI : SigmaFinite (volume : Measure E) := by
      change SigmaFinite (euclideanGaussianLaw E)
      infer_instance
    exact integral_fintype_prod_eq_prod (fun (i : Fin k) (z : E) => Complex.exp ((⟪z, t i⟫_ℝ : ℂ) * Complex.I))
  rw [hp]
  have hi (i : Fin k) : (∫ z : E, Complex.exp ((⟪z, t i⟫_ℝ : ℂ) * Complex.I) ∂euclideanGaussianLaw E) =
      Complex.exp (-(‖t i‖ : ℂ) ^ 2 / 2) := euclideanGaussian_characteristic _
  simp_rw [hi]
  rw [← Complex.exp_sum]
  congr 1
  simp only [← Finset.sum_div, Finset.sum_neg_distrib, Complex.ofReal_pow]

end
end Nonsmooth
