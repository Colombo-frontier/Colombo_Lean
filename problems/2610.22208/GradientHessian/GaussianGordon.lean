import GradientHessian.GaussianComparisonCoordinates
import GradientHessian.GaussianFiniteMinMax

/-! Finite Gaussian min-max comparison proved by the literal soft
min-max interpolation and the two exact deterministic approximation errors. -/

noncomputable section
namespace GradientHessian.GaussianConcentration
open MeasureTheory GaussianHilbert Filter
open scoped InnerProductSpace BigOperators NNReal Topology

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
  [DecidableEq I] [DecidableEq J]

theorem gaussian_softMinMax_comparison (A B : E →L[ℝ] (I × J → ℝ))
    (hcross : ∀ a b, coordinateCovariance E A B a b = 0)
    (hrow : ∀ i j l, coordinateCovariance E A A (i,j) (i,l) = coordinateCovariance E B B (i,j) (i,l))
    (hcov : ∀ a b, coordinateCovariance E B B a b ≤ coordinateCovariance E A A a b)
    {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    linearGaussianExpectation E (softMinMax α β) B ≤
      linearGaussianExpectation E (softMinMax α β) A := by
  apply gaussian_comparison_entrywise E ((softMinMax_contDiff α β).of_le le_top)
    (softMinMax_lipschitz hα.ne' hβ.ne')
    (c := ⟨2 * |α| + 2 * |β|, by positivity⟩) (softMinMax_hessian_bound hα.ne' hβ.ne') A B hcross
  intro x a b
  rcases a with ⟨i,j⟩
  rcases b with ⟨k,l⟩
  by_cases hik : i = k
  · subst k
    rw [hrow, sub_self, zero_mul]
  · exact mul_nonneg (sub_nonneg.mpr (hcov _ _))
      (softMinMax_hessian_differentRows_nonneg hα hβ.ne' x i k j l hik)

omit [DecidableEq I] [DecidableEq J] in
theorem gaussian_finiteMinMax_soft_bounds (A : E →L[ℝ] (I × J → ℝ))
    {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    linearGaussianExpectation E finiteMinMax A - Real.log (Fintype.card I) / α ≤
      linearGaussianExpectation E (softMinMax α β) A ∧
    linearGaussianExpectation E (softMinMax α β) A ≤
      linearGaussianExpectation E finiteMinMax A + Real.log (Fintype.card J) / β := by
  have hi : Integrable (fun z => finiteMinMax (A z)) (euclideanGaussianLaw E) :=
    lipschitz_integrable (finiteMinMax_lipschitz.comp A.lipschitz)
  have hs : Integrable (fun z => softMinMax α β (A z)) (euclideanGaussianLaw E) :=
    lipschitz_integrable ((softMinMax_lipschitz hα.ne' hβ.ne').comp A.lipschitz)
  constructor
  · have h := integral_mono (hi.sub (integrable_const (Real.log (Fintype.card I) / α))) hs
      (fun z => (finiteMinMax_soft_bounds hα hβ (A z)).1)
    simp only [Pi.sub_apply] at h
    rw [integral_sub hi (integrable_const _)] at h
    simpa only [integral_const, measureReal_univ_eq_one, one_smul] using h
  · have h := integral_mono hs (hi.add (integrable_const (Real.log (Fintype.card J) / β)))
      (fun z => (finiteMinMax_soft_bounds hα hβ (A z)).2)
    simp only [Pi.add_apply] at h
    rw [integral_add hi (integrable_const _)] at h
    simpa only [integral_const, measureReal_univ_eq_one, one_smul] using h

theorem gaussian_finiteMinMax_comparison (A B : E →L[ℝ] (I × J → ℝ))
    (hcross : ∀ a b, coordinateCovariance E A B a b = 0)
    (hrow : ∀ i j l, coordinateCovariance E A A (i,j) (i,l) = coordinateCovariance E B B (i,j) (i,l))
    (hcov : ∀ a b, coordinateCovariance E B B a b ≤ coordinateCovariance E A A a b) :
    linearGaussianExpectation E finiteMinMax B ≤ linearGaussianExpectation E finiteMinMax A := by
  have hn (n : ℕ) : linearGaussianExpectation E finiteMinMax B ≤
      linearGaussianExpectation E finiteMinMax A +
        (Real.log (Fintype.card I) + Real.log (Fintype.card J)) / ((n : ℝ) + 1) := by
    have hp : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h1 := (gaussian_finiteMinMax_soft_bounds E B hp hp).1
    have h2 := gaussian_softMinMax_comparison E A B hcross hrow hcov hp hp
    have h3 := (gaussian_finiteMinMax_soft_bounds E A hp hp).2
    rw [add_div]
    linarith
  have ht : Tendsto (fun n : ℕ => linearGaussianExpectation E finiteMinMax A +
      (Real.log (Fintype.card I) + Real.log (Fintype.card J)) / ((n : ℝ) + 1)) atTop
      (𝓝 (linearGaussianExpectation E finiteMinMax A)) := by
    have h := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul
      (Real.log (Fintype.card I) + Real.log (Fintype.card J))
    simpa only [mul_one_div, mul_zero, add_zero] using h.const_add (linearGaussianExpectation E finiteMinMax A)
  exact ge_of_tendsto ht (Filter.Eventually.of_forall hn)

end GradientHessian.GaussianConcentration
