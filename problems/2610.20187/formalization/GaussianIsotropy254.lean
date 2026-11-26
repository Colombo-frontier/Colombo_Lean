import GaussianMatrixKL254
import GaussianNorm254
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Matrix
open scoped ENNReal NNReal BigOperators Matrix
namespace Paper254

theorem unitary_preserves_volume {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℝ) :
    Measure.map (unitaryMeasurableEquiv U) (volume : Measure (Coordinates d))=volume := by
  have hdet : (U : Precision d).det*(U : Precision d).det=1 := by
    have hh := congrArg Matrix.det (unitary.coe_star_mul_self U)
    simpa only [Matrix.det_mul,star_eq_conjTranspose,Matrix.conjTranspose_eq_transpose_of_trivial,
      Matrix.det_transpose,Matrix.det_one] using hh
  have hne : (U : Precision d).det ≠ 0 := by intro hz; rw [hz] at hdet; norm_num at hdet
  have habs : |(U : Precision d).det|=1 := by
    nlinarith [sq_abs (U : Precision d).det,abs_nonneg (U : Precision d).det]
  have hlin : LinearMap.det (Matrix.toLin' (U : Precision d)) ≠ 0 := by
    rwa [LinearMap.det_toLin']
  have hh := Real.map_linearMap_volume_pi_eq_smul_volume_pi hlin
  simpa only [LinearMap.det_toLin',abs_inv,habs,inv_one,ENNReal.ofReal_one,one_smul] using hh

theorem gaussianProductPDF_isotropic {d : ℕ} (m x : Coordinates d) (q : ℝ≥0) :
    gaussianProductPDF m (fun _ => q) x=(Real.sqrt (2*Real.pi*q))⁻¹^d*
      Real.exp (-(∑ i,(x i-m i)^2)/(2*q)) := by
  unfold gaussianProductPDF
  simp_rw [gaussianPDFReal_def]
  rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,
    ← Real.exp_sum]
  congr 2
  rw [← Finset.sum_div,← Finset.sum_neg_distrib]

theorem gaussianProductPDF_rotate {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℝ)
    (m x : Coordinates d) (q : ℝ≥0) :
    gaussianProductPDF ((U : Precision d) *ᵥ m) (fun _ => q) ((U : Precision d) *ᵥ x)=
      gaussianProductPDF m (fun _ => q) x := by
  rw [gaussianProductPDF_isotropic,gaussianProductPDF_isotropic]
  have hh := unitary_sum_squares U (x-m)
  simp only [Matrix.mulVec_sub,Pi.sub_apply] at hh
  rw [hh]

theorem map_isotropic_gaussian {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℝ)
    (m : Coordinates d) (q : ℝ≥0) (hq : q ≠ 0) :
    (Measure.pi (fun i => gaussianReal (m i) q)).map (unitaryMeasurableEquiv U)=
      Measure.pi (fun i => gaussianReal (((U : Precision d) *ᵥ m) i) q) := by
  let e := unitaryMeasurableEquiv U
  let f := fun x => ENNReal.ofReal (gaussianProductPDF m (fun _ => q) x)
  let g := fun x => ENNReal.ofReal (gaussianProductPDF ((U : Precision d) *ᵥ m) (fun _ => q) x)
  have hfg : ∀ x,g (e x)=f x := fun x => congrArg ENNReal.ofReal (gaussianProductPDF_rotate U m x q)
  rw [gaussian_product_density m (fun _ => q) (fun _ => hq),
    gaussian_product_density ((U : Precision d) *ᵥ m) (fun _ => q) (fun _ => hq)]
  rw [← volume_pi]
  change (volume.withDensity f).map e=volume.withDensity g
  ext s hs
  rw [Measure.map_apply e.measurable hs,withDensity_apply f (e.measurable hs),withDensity_apply g hs]
  have hh := setLIntegral_map hs
    (gaussianProductPDF_measurable ((U : Precision d) *ᵥ m) (fun _ => q)) e.measurable (μ := volume)
  rw [unitary_preserves_volume U] at hh
  rw [hh]
  exact lintegral_congr (fun x => (hfg x).symm)

theorem rotatedGaussian_isotropic {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℝ)
    (m : Coordinates d) (q : ℝ≥0) (hq : q ≠ 0) :
    rotatedGaussian U m (fun _ => q)=Measure.pi (fun i => gaussianReal (m i) q) := by
  unfold rotatedGaussian
  rw [← map_isotropic_gaussian U m q hq,Measure.map_map
    (unitaryMeasurableEquiv U).symm.measurable (unitaryMeasurableEquiv U).measurable]
  simp

/-- The comparator measure here is the standard isotropic product Gaussian,
independent of the precision matrix's eigenbasis. -/
theorem PrecisionGaussian.standard_gaussian_kl {d : ℕ} (P : PrecisionGaussian d)
    (u : Coordinates d) (q : ℝ≥0) (hq : q ≠ 0) :
    klDiv (Measure.pi (fun i => gaussianReal (u i) q)) P.gaussianMeasure=
      ENNReal.ofReal (P.potential q u) := by
  rw [← rotatedGaussian_isotropic (star P.positive.isHermitian.eigenvectorUnitary) u q hq]
  exact P.kl_equals_potential u q hq

end Paper254
#print axioms Paper254.PrecisionGaussian.standard_gaussian_kl
