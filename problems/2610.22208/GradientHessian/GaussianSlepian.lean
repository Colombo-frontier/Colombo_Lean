import GradientHessian.GaussianComparisonCoordinates
import GradientHessian.GaussianSoftMaximumHessian
import GradientHessian.GaussianFiniteMaximum

/-! A finite Gaussian maximum comparison proved from the actual
interpolation and soft-maximum Hessian, followed by its exact limit. -/

noncomputable section
namespace GradientHessian.GaussianConcentration
open MeasureTheory GaussianHilbert Filter
open scoped InnerProductSpace BigOperators NNReal Topology

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
variable {I : Type*} [Fintype I] [Nonempty I] [DecidableEq I]

theorem gaussian_softMaximum_comparison (A B : E →L[ℝ] (I → ℝ))
    (hcross : ∀ i j, coordinateCovariance E A B i j = 0)
    (hdiag : ∀ i, coordinateCovariance E A A i i = coordinateCovariance E B B i i)
    (hcov : ∀ i j, coordinateCovariance E B B i j ≤ coordinateCovariance E A A i j)
    {β : ℝ} (hβ : 0 < β) :
    linearGaussianExpectation E (softMaximum β) A ≤
      linearGaussianExpectation E (softMaximum β) B := by
  apply gaussian_comparison_entrywise E ((softMaximum_contDiff β).of_le le_top)
    (softMaximum_lipschitz hβ.ne')
    (c := ⟨2 * |β|, by positivity⟩) (softMaximum_hessian_bound hβ.ne') B A
  · intro i j
    rw [coordinateCovariance_swap]
    exact hcross j i
  · intro x i j
    by_cases hij : i = j
    · subst j
      rw [hdiag, sub_self, zero_mul]
    · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (hcov i j))
        (softMaximum_hessian_offDiagonal_nonpos hβ x i j hij)

omit [DecidableEq I] in
theorem gaussian_finiteMaximum_le_softMaximum (A : E →L[ℝ] (I → ℝ)) {β : ℝ} (hβ : 0 < β) :
    linearGaussianExpectation E finiteMaximum A ≤ linearGaussianExpectation E (softMaximum β) A := by
  apply integral_mono (lipschitz_integrable (finiteMaximum_lipschitz.comp A.lipschitz))
    (lipschitz_integrable ((softMaximum_lipschitz hβ.ne').comp A.lipschitz))
  intro z
  exact finiteMaximum_le_softMaximum hβ _

omit [DecidableEq I] in
theorem gaussian_softMaximum_le_finiteMaximum (A : E →L[ℝ] (I → ℝ)) {β : ℝ} (hβ : 0 < β) :
    linearGaussianExpectation E (softMaximum β) A ≤ linearGaussianExpectation E finiteMaximum A +
      Real.log (Fintype.card I) / β := by
  have hi : Integrable (fun z => finiteMaximum (A z)) (euclideanGaussianLaw E) :=
    lipschitz_integrable (finiteMaximum_lipschitz.comp A.lipschitz)
  have h := integral_mono (lipschitz_integrable ((softMaximum_lipschitz hβ.ne').comp A.lipschitz))
    (hi.add (integrable_const (Real.log (Fintype.card I) / β)))
    (fun z => softMaximum_le_finiteMaximum hβ (A z))
  simp only [Pi.add_apply, Function.comp_def] at h
  rw [integral_add hi (integrable_const _)] at h
  simpa only [integral_const, measureReal_univ_eq_one, one_smul] using h

theorem gaussian_finiteMaximum_comparison (A B : E →L[ℝ] (I → ℝ))
    (hcross : ∀ i j, coordinateCovariance E A B i j = 0)
    (hdiag : ∀ i, coordinateCovariance E A A i i = coordinateCovariance E B B i i)
    (hcov : ∀ i j, coordinateCovariance E B B i j ≤ coordinateCovariance E A A i j) :
    linearGaussianExpectation E finiteMaximum A ≤ linearGaussianExpectation E finiteMaximum B := by
  have hn (n : ℕ) : linearGaussianExpectation E finiteMaximum A ≤
      linearGaussianExpectation E finiteMaximum B + Real.log (Fintype.card I) / ((n : ℝ) + 1) := by
    have hp : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    exact (gaussian_finiteMaximum_le_softMaximum E A hp).trans
      ((gaussian_softMaximum_comparison E A B hcross hdiag hcov hp).trans
        (gaussian_softMaximum_le_finiteMaximum E B hp))
  have ht : Tendsto (fun n : ℕ => linearGaussianExpectation E finiteMaximum B +
      Real.log (Fintype.card I) / ((n : ℝ) + 1)) atTop
      (𝓝 (linearGaussianExpectation E finiteMaximum B)) := by
    have h := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (Real.log (Fintype.card I))
    simpa only [mul_one_div, mul_zero, add_zero] using h.const_add
      (linearGaussianExpectation E finiteMaximum B)
  exact ge_of_tendsto ht (Filter.Eventually.of_forall hn)

end GradientHessian.GaussianConcentration
