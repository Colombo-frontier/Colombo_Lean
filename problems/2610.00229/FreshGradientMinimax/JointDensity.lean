import FreshGradientMinimax.Basic
import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-! Multiplying the initial-state and conditional-response densities gives
the density of the actual joint transition measure. No restriction is
imposed on the measurable space of initial states or algorithmic seeds. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem compProd_density {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {P Q : Measure α} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {K J : Kernel α β} [IsMarkovKernel K] [IsMarkovKernel J]
    {r : α → ℝ≥0∞} {f : α × β → ℝ≥0∞} (hr : Measurable r) (hf : Measurable f)
    (hP : Q.withDensity r = P) (hK : ∀ a, (J a).withDensity (fun b => f (a, b)) = K a) :
    P ⊗ₘ K = (Q ⊗ₘ J).withDensity (fun z => r z.1 * f z) := by
  ext s hs
  have hm : Measurable (s.indicator (fun z : α × β => r z.1 * f z)) :=
    ((hr.comp measurable_fst).mul hf).indicator hs
  rw [Measure.compProd_apply hs, ← hP,
    lintegral_withDensity_eq_lintegral_mul _ hr (Kernel.measurable_kernel_prodMk_left hs),
    withDensity_apply _ hs, ← lintegral_indicator hs,
    Measure.lintegral_compProd hm]
  apply lintegral_congr
  intro a
  have hma : Measurable ((Prod.mk a ⁻¹' s).indicator (fun b => f (a, b))) :=
    (hf.comp measurable_prodMk_left).indicator (measurable_prodMk_left hs)
  change r a * (K a) (Prod.mk a ⁻¹' s) = _
  rw [← hK a, withDensity_apply _ (measurable_prodMk_left hs),
    ← lintegral_indicator (measurable_prodMk_left hs),
    ← lintegral_const_mul (r a) hma]
  apply lintegral_congr
  intro b
  by_cases h : (a, b) ∈ s
  · simp [h]
  · simp [h]

end FreshGradientMinimax
