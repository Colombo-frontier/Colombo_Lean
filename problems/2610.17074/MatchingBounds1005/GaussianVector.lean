import Mathlib.Probability.Distributions.Gaussian
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic

/-!
# Actual standard Gaussian vectors

The law is constructed from independent scalar Gaussian coordinates, pushed
to Euclidean space. Characteristic functions, not postulated multivariate
Gaussian identities, establish its invariance and linear observation laws.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators InnerProductSpace ENNReal NNReal

namespace MatchingBounds1005.GaussianVector

abbrev Vec (n : ℕ) := EuclideanSpace ℝ (Fin n)

def standardGaussian (n : ℕ) : Measure (Vec n) :=
  (Measure.pi (fun _ : Fin n => gaussianReal 0 1)).map
    (EuclideanSpace.measurableEquiv (Fin n)).symm

instance standardGaussian_probability (n : ℕ) : IsProbabilityMeasure (standardGaussian n) :=
  isProbabilityMeasure_map (EuclideanSpace.measurableEquiv (Fin n)).symm.measurable.aemeasurable

/-- The Euclidean law has exactly the prescribed independent coordinates. -/
theorem standardGaussian_coordinate_law (n : ℕ) :
    (standardGaussian n).map (EuclideanSpace.measurableEquiv (Fin n)) =
      Measure.pi (fun _ : Fin n => gaussianReal 0 1) := by
  rw [standardGaussian, Measure.map_map (EuclideanSpace.measurableEquiv (Fin n)).measurable
    (EuclideanSpace.measurableEquiv (Fin n)).symm.measurable]
  simp only [Function.comp_def, MeasurableEquiv.apply_symm_apply, Measure.map_id']

theorem integral_coordinate_product (n : ℕ) (f : Fin n → ℝ → ℂ) :
    (∫ x : Fin n → ℝ, ∏ i, f i (x i)
      ∂Measure.pi (fun _ : Fin n => gaussianReal 0 1)) =
      ∏ i, ∫ x : ℝ, f i x ∂gaussianReal 0 1 := by
  letI : MeasureSpace ℝ := ⟨gaussianReal 0 1⟩
  letI : IsProbabilityMeasure (volume : Measure ℝ) :=
    inferInstanceAs (IsProbabilityMeasure (gaussianReal 0 1))
  letI : ∀ _ : Fin n, SigmaFinite (volume : Measure ℝ) := fun _ => inferInstance
  exact integral_fintype_prod_eq_prod (Fin n) f

theorem norm_sq_coordinates {n : ℕ} (t : Vec n) :
    ‖t‖ ^ 2 = ∑ i, t i ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp [PiLp.inner_apply, pow_two]

/-- Characteristic function of the concrete product Gaussian law. -/
theorem standardGaussian_charFun {n : ℕ} (t : Vec n) :
    charFun (standardGaussian n) t = Complex.exp (-((‖t‖ : ℂ) ^ 2) / 2) := by
  rw [charFun_apply, standardGaussian,
    integral_map (EuclideanSpace.measurableEquiv (Fin n)).symm.measurable.aemeasurable
      ((by fun_prop : Continuous
        (fun x : Vec n => Complex.exp ((⟪x, t⟫_ℝ : ℂ) * Complex.I))).measurable.aestronglyMeasurable)]
  have hexp (x : Fin n → ℝ) :
      Complex.exp ((⟪(EuclideanSpace.measurableEquiv (Fin n)).symm x, t⟫_ℝ : ℂ) * Complex.I) =
      ∏ i, Complex.exp ((t i : ℂ) * (x i : ℂ) * Complex.I) := by
    rw [← Complex.exp_sum]
    congr 1
    simp [PiLp.inner_apply, EuclideanSpace.measurableEquiv,
      Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul, Finset.mul_sum, mul_comm]
  simp_rw [hexp]
  rw [integral_coordinate_product n (fun i x => Complex.exp ((t i : ℂ) * (x : ℂ) * Complex.I))]
  have hscalar (i : Fin n) :
      (∫ x : ℝ, Complex.exp ((t i : ℂ) * (x : ℂ) * Complex.I) ∂gaussianReal 0 1) =
        Complex.exp (-((t i : ℂ) ^ 2) / 2) := by
    rw [← charFun_apply_real, charFun_gaussianReal]
    simp [neg_div]
  simp_rw [hscalar]
  rw [← Complex.exp_sum]
  congr 1
  rw [← Finset.sum_div, Finset.sum_neg_distrib]
  have hn : (‖t‖ : ℂ) ^ 2 = ∑ i, (t i : ℂ) ^ 2 := by
    exact_mod_cast norm_sq_coordinates t
  rw [hn]

theorem charFun_map_isometry {n : ℕ} (U : Vec n ≃ₗᵢ[ℝ] Vec n) (t : Vec n) :
    charFun ((standardGaussian n).map U) t = charFun (standardGaussian n) (U.symm t) := by
  rw [charFun_apply, charFun_apply,
    integral_map U.continuous.measurable.aemeasurable
      ((by fun_prop : Continuous (fun x : Vec n =>
        Complex.exp ((⟪x, t⟫_ℝ : ℂ) * Complex.I))).measurable.aestronglyMeasurable)]
  simp only [LinearIsometryEquiv.inner_map_eq_flip]

/-- Orthogonal invariance of the actual independent-coordinate law. -/
theorem standardGaussian_map_isometry {n : ℕ} (U : Vec n ≃ₗᵢ[ℝ] Vec n) :
    (standardGaussian n).map U = standardGaussian n := by
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_map_isometry, standardGaussian_charFun, standardGaussian_charFun,
    U.symm.norm_map]

/-- Characteristic function of any linear observation, without an
injectivity, covariance-invertibility or full-rank hypothesis. -/
theorem standardGaussian_linear_charFun {n m : ℕ} (B : Vec n →L[ℝ] Vec m) (t : Vec m) :
    charFun ((standardGaussian n).map B) t =
      Complex.exp (-((‖B.adjoint t‖ : ℂ) ^ 2) / 2) := by
  rw [charFun_apply,
    integral_map B.continuous.measurable.aemeasurable
      ((by fun_prop : Continuous (fun x : Vec m =>
        Complex.exp ((⟪x, t⟫_ℝ : ℂ) * Complex.I))).measurable.aestronglyMeasurable)]
  simp_rw [← B.adjoint_inner_right]
  exact standardGaussian_charFun (B.adjoint t)

/-- Every scalar linear observation is an actual scalar Gaussian, including
the zero functional with degenerate variance. -/
theorem standardGaussian_inner_law {n : ℕ} (a : Vec n) :
    (standardGaussian n).map (fun x => ⟪a, x⟫_ℝ) =
      gaussianReal 0 ⟨‖a‖ ^ 2, sq_nonneg _⟩ := by
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_apply_real,
    integral_map (by fun_prop : Measurable (fun x : Vec n => ⟪a, x⟫_ℝ)).aemeasurable
      ((by fun_prop : Continuous (fun x : ℝ =>
        Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I))).measurable.aestronglyMeasurable)]
  have heq (x : Vec n) : (t : ℂ) * (⟪a, x⟫_ℝ : ℂ) * Complex.I =
      (⟪x, t • a⟫_ℝ : ℂ) * Complex.I := by
    rw [real_inner_smul_right, real_inner_comm x a, Complex.ofReal_mul]
  simp_rw [heq]
  rw [← charFun_apply, standardGaussian_charFun, charFun_gaussianReal]
  have hn : (‖t • a‖ : ℂ) ^ 2 = (t : ℂ) ^ 2 * (‖a‖ : ℂ) ^ 2 := by
    norm_cast
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [hn]
  congr 1
  simp only [NNReal.coe_mk, Complex.ofReal_zero, Complex.ofReal_pow, mul_zero, zero_mul, zero_sub]
  ring

/-- Positive-dimensional standard Gaussian vectors give zero mass to every
singleton, including the origin excluded in sphere normalization. -/
theorem standardGaussian_singleton {n : ℕ} (hn : 0 < n) (x : Vec n) :
    standardGaussian n {x} = 0 := by
  let a : Vec n := EuclideanSpace.single (⟨0, hn⟩ : Fin n) 1
  have ha : ‖a‖ = 1 := by simp [a]
  have hv : (⟨‖a‖ ^ 2, sq_nonneg _⟩ : ℝ≥0) = 1 := by
    apply NNReal.coe_injective
    simp [ha]
  have hmap := standardGaussian_inner_law a
  rw [hv] at hmap
  have hs : gaussianReal 0 1 {⟪a, x⟫_ℝ} = 0 :=
    (gaussianReal_absolutelyContinuous 0 (by norm_num : (1 : ℝ≥0) ≠ 0))
      (by simp)
  have hpre : standardGaussian n ((fun y => ⟪a, y⟫_ℝ) ⁻¹' {⟪a, x⟫_ℝ}) = 0 := by
    rw [← Measure.map_apply (by fun_prop : Measurable (fun y : Vec n => ⟪a, y⟫_ℝ))
      (measurableSet_singleton _), hmap]
    exact hs
  apply measure_mono_null _ hpre
  intro y hy
  rcases Set.mem_singleton_iff.mp hy with rfl
  rfl

end MatchingBounds1005.GaussianVector
