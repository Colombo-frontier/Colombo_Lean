import FreshGradientMinimax.Oracle

/-! A fixed, measurable two-atom kernel. The mixing probability is constant
across queries; the atom maps may be arbitrary measurable functions. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory

variable {Q R : Type*} [MeasurableSpace Q] [MeasurableSpace R]

def bernoulliKernel (p : ℝ) (a b : Q → R) (ha : Measurable a) (hb : Measurable b) :
    Kernel Q R where
  toFun q := ENNReal.ofReal p • Measure.dirac (a q) +
    ENNReal.ofReal (1 - p) • Measure.dirac (b q)
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro s hs
    simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
    exact (measurable_const.mul ((Kernel.deterministic a ha).measurable_coe hs)).add
      (measurable_const.mul ((Kernel.deterministic b hb).measurable_coe hs))

theorem bernoulliKernel_apply (p : ℝ) (a b : Q → R) (ha : Measurable a) (hb : Measurable b)
    (q : Q) : bernoulliKernel p a b ha hb q =
      ENNReal.ofReal p • Measure.dirac (a q) +
      ENNReal.ofReal (1 - p) • Measure.dirac (b q) := rfl

theorem bernoulliKernel_markov {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (a b : Q → R) (ha : Measurable a) (hb : Measurable b) :
    IsMarkovKernel (bernoulliKernel p a b ha hb) := by
  constructor
  intro q
  constructor
  simp only [bernoulliKernel_apply, Measure.add_apply, Measure.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add hp (sub_nonneg.mpr hp1)]
  norm_num

variable [MeasurableSingletonClass R]
variable {E : Type*} [NormedAddCommGroup E]

theorem bernoulliKernel_integrable (p : ℝ) (a b : Q → R) (ha : Measurable a)
    (hb : Measurable b) (q : Q) (f : R → E) :
    Integrable f (bernoulliKernel p a b ha hb q) := by
  rw [bernoulliKernel_apply, integrable_add_measure]
  exact ⟨integrable_dirac.smul_measure ENNReal.ofReal_ne_top,
    integrable_dirac.smul_measure ENNReal.ofReal_ne_top⟩

theorem bernoulliKernel_integral [NormedSpace ℝ E] [CompleteSpace E]
    {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (a b : Q → R) (ha : Measurable a) (hb : Measurable b) (q : Q) (f : R → E) :
    (∫ r, f r ∂bernoulliKernel p a b ha hb q) = p • f (a q) + (1 - p) • f (b q) := by
  rw [bernoulliKernel_apply, integral_add_measure
    (integrable_dirac.smul_measure ENNReal.ofReal_ne_top)
    (integrable_dirac.smul_measure ENNReal.ofReal_ne_top)]
  simp only [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal hp,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hp1)]

theorem bernoulliKernel_one (a b : Q → R) (ha : Measurable a) (hb : Measurable b) :
    bernoulliKernel 1 a b ha hb = Kernel.deterministic a ha := by
  ext q s hs
  simp [bernoulliKernel_apply, Kernel.deterministic_apply]

end FreshGradientMinimax
