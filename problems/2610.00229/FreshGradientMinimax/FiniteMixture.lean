import FreshGradientMinimax.BatchKernel
import FreshGradientMinimax.Multilevel

/-! Actual finite mixtures of sampling kernels, with Bochner integral rules. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory
open scoped BigOperators

variable {Q R E : Type*} [MeasurableSpace Q] [MeasurableSpace R]

def finiteMixtureKernel (p : ℕ → ℝ) (L : ℕ → Kernel Q R) (K : ℕ) : Kernel Q R where
  toFun q := ∑ j ∈ Finset.range K, ENNReal.ofReal (p j) • L j q
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro s hs
    simp_rw [Measure.finset_sum_apply, Measure.smul_apply, smul_eq_mul]
    exact Finset.measurable_sum _ (fun j _ => measurable_const.mul ((L j).measurable_coe hs))

theorem finiteMixtureKernel_apply (p : ℕ → ℝ) (L : ℕ → Kernel Q R) (K : ℕ) (q : Q) :
    finiteMixtureKernel p L K q = ∑ j ∈ Finset.range K, ENNReal.ofReal (p j) • L j q := rfl

theorem finiteMixtureKernel_markov (p : ℕ → ℝ) (L : ℕ → Kernel Q R) (K : ℕ)
    [∀ j, IsMarkovKernel (L j)] (hp : ∀ j < K, 0 ≤ p j)
    (hs : (∑ j ∈ Finset.range K, p j) = 1) : IsMarkovKernel (finiteMixtureKernel p L K) := by
  constructor
  intro q
  constructor
  rw [finiteMixtureKernel_apply, Measure.finset_sum_apply]
  simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun j hj => hp j (Finset.mem_range.mp hj)), hs]
  exact ENNReal.ofReal_one

theorem finiteMixtureKernel_map {T : Type*} [MeasurableSpace T]
    (p : ℕ → ℝ) (L : ℕ → Kernel Q R) (K : ℕ) (f : R → T) (hf : Measurable f) :
    (finiteMixtureKernel p L K).map f = finiteMixtureKernel p (fun j => (L j).map f) K := by
  apply Kernel.ext
  intro q
  apply Measure.ext
  intro s hs
  simp only [Kernel.map_apply _ hf, Measure.map_apply hf hs, finiteMixtureKernel_apply,
    Measure.finset_sum_apply, Measure.smul_apply]

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
theorem finiteMixtureKernel_integrable (p : ℕ → ℝ) (L : ℕ → Kernel Q R) (K : ℕ)
    (q : Q) (f : R → E) (hi : ∀ j < K, Integrable f (L j q)) :
    Integrable f (finiteMixtureKernel p L K q) := by
  rw [finiteMixtureKernel_apply]
  exact integrable_finset_sum_measure.mpr (fun j hj =>
    (hi j (Finset.mem_range.mp hj)).smul_measure ENNReal.ofReal_ne_top)

theorem finiteMixtureKernel_integral (p : ℕ → ℝ) (L : ℕ → Kernel Q R) (K : ℕ)
    (q : Q) (f : R → E) (hp : ∀ j < K, 0 ≤ p j)
    (hi : ∀ j < K, Integrable f (L j q)) :
    (∫ r, f r ∂finiteMixtureKernel p L K q) =
      ∑ j ∈ Finset.range K, p j • ∫ r, f r ∂L j q := by
  rw [finiteMixtureKernel_apply, integral_finset_sum_measure (fun j hj =>
    (hi j (Finset.mem_range.mp hj)).smul_measure ENNReal.ofReal_ne_top)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [integral_smul_measure, ENNReal.toReal_ofReal (hp j (Finset.mem_range.mp hj))]

end FreshGradientMinimax
