import GaussianIsotropy254
import Mathlib.Probability.Distributions.Gaussian.Basic

noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped NNReal ENNReal BigOperators
namespace Paper254

def consContinuousLinearMap (d : ℕ) : (ℝ × Coordinates d) →L[ℝ] Coordinates (d+1) :=
  ({ toFun := fun p => Fin.cons p.1 p.2
     map_add' := by intro a b; ext i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl
     map_smul' := by intro a b; ext i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl } :
    (ℝ × Coordinates d) →ₗ[ℝ] Coordinates (d+1)).toContinuousLinearMap

theorem gaussian_product_isGaussian (d : ℕ) (m : Fin d → ℝ) (c : Fin d → ℝ≥0) :
    IsGaussian (Measure.pi (fun i => gaussianReal (m i) (c i))) := by
  induction d with
  | zero =>
    rw [Measure.pi_of_empty _ (0 : Coordinates 0)]
    infer_instance
  | succ d ih =>
    letI := ih (fun i => m i.succ) (fun i => c i.succ)
    have hm := (measurePreserving_piFinSuccAbove (fun i => gaussianReal (m i) (c i)) 0).symm.map_eq
    have he : Measure.pi (fun i => gaussianReal (m i) (c i))=
        ((gaussianReal (m 0) (c 0)).prod (Measure.pi (fun i : Fin d => gaussianReal (m i.succ) (c i.succ)))).map
          (consContinuousLinearMap d) := by
      rw [← hm]
      simp only [Fin.zero_succAbove]
      congr 1
      funext p
      simp [MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv,
        Fin.insertNth_zero,consContinuousLinearMap]
    rw [he]
    infer_instance

theorem rotatedGaussian_isGaussian {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℝ)
    (m : Coordinates d) (c : Fin d → ℝ≥0) : IsGaussian (rotatedGaussian U m c) := by
  letI := gaussian_product_isGaussian d ((U : Precision d) *ᵥ m) c
  change IsGaussian ((Measure.pi (fun i => gaussianReal (((U : Precision d) *ᵥ m) i) (c i))).map
    (Matrix.toLin' ((star U : Matrix.unitaryGroup (Fin d) ℝ).val)).toContinuousLinearMap)
  infer_instance

theorem PrecisionGaussian.measure_isGaussian {d : ℕ} (P : PrecisionGaussian d) :
    IsGaussian P.gaussianMeasure := rotatedGaussian_isGaussian _ _ _

/-- The scalar Gaussian integral now applies to every linear projection
of the actual multivariate state measure, including zero variance. -/
theorem gaussian_linear_quadratic_integral {d : ℕ} (P : PrecisionGaussian d)
    (L : Coordinates d →L[ℝ] ℝ) (lam : ℝ) :
    let a := ∫ x,L x ∂P.gaussianMeasure
    let v := (variance L P.gaussianMeasure).toNNReal
    let D := 1+2*lam^2*(v:ℝ)
    (∫ x,Real.exp (-lam*L x-lam^2*(L x)^2) ∂P.gaussianMeasure)=
      (Real.sqrt D)⁻¹*Real.exp ((-lam*a-lam^2*a^2+lam^2*(v:ℝ)/2)/D) := by
  letI := P.measure_isGaussian
  have he := IsGaussian.map_eq_gaussianReal (μ := P.gaussianMeasure) L
  have hm : Measurable (fun x : ℝ => Real.exp (-lam*x-lam^2*x^2)) := by fun_prop
  rw [← integral_map L.measurable.aemeasurable hm.aestronglyMeasurable,he]
  exact gaussian_quadratic_integral _ lam _

theorem gaussian_affine_quadratic_integral {d : ℕ} (P : PrecisionGaussian d)
    (L : Coordinates d →L[ℝ] ℝ) (b lam : ℝ) :
    let a := (∫ x,L x ∂P.gaussianMeasure)-b
    let v := (variance L P.gaussianMeasure).toNNReal
    let D := 1+2*lam^2*(v:ℝ)
    (∫ x,Real.exp (-lam*(L x-b)-lam^2*(L x-b)^2) ∂P.gaussianMeasure)=
      (Real.sqrt D)⁻¹*Real.exp ((-lam*a-lam^2*a^2+lam^2*(v:ℝ)/2)/D) := by
  letI := P.measure_isGaussian
  have he := IsGaussian.map_eq_gaussianReal (μ := P.gaussianMeasure) L
  have hm : Measurable (fun x : ℝ => Real.exp (-lam*(x-b)-lam^2*(x-b)^2)) := by fun_prop
  rw [← integral_map L.measurable.aemeasurable hm.aestronglyMeasurable,he]
  have hx : Measurable (fun x : ℝ => x-b) := by fun_prop
  have hg : Measurable (fun x : ℝ => Real.exp (-lam*x-lam^2*x^2)) := by fun_prop
  rw [← integral_map hx.aemeasurable hg.aestronglyMeasurable,gaussianReal_map_sub_const]
  exact gaussian_quadratic_integral _ lam _

end Paper254
#print axioms Paper254.PrecisionGaussian.measure_isGaussian
#print axioms Paper254.gaussian_linear_quadratic_integral
#print axioms Paper254.gaussian_affine_quadratic_integral
