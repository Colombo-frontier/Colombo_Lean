import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Tactic.Positivity

/-! Bounds for actual moments on a high-probability event. -/
noncomputable section
open MeasureTheory

namespace MatchingBounds1005.ProbabilityMoment

theorem integral_le_good_add_bad {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (hf : Integrable f μ)
    (G : Set Ω) (hG : MeasurableSet G) (a b ζ : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hgood : ∀ x ∈ G, f x ≤ a) (hglobal : ∀ x, f x ≤ b)
    (hfail : μ.real Gᶜ ≤ ζ) : (∫ x, f x ∂μ) ≤ a + ζ * b := by
  have hia : Integrable (G.indicator (fun _ : Ω => a)) μ :=
    (integrable_const a).indicator hG
  have hib : Integrable (Gᶜ.indicator (fun _ : Ω => b)) μ :=
    (integrable_const b).indicator hG.compl
  have hp (x : Ω) : f x ≤ G.indicator (fun _ : Ω => a) x + Gᶜ.indicator (fun _ : Ω => b) x := by
    by_cases hx : x ∈ G
    · have hxc : x ∉ Gᶜ := fun h => h hx
      simpa only [Set.indicator_of_mem hx, Set.indicator_of_not_mem hxc, add_zero]
        using hgood x hx
    · have hxc : x ∈ Gᶜ := hx
      simpa only [Set.indicator_of_not_mem hx, Set.indicator_of_mem hxc, zero_add]
        using hglobal x
  calc
    (∫ x, f x ∂μ) ≤ ∫ x, G.indicator (fun _ : Ω => a) x + Gᶜ.indicator (fun _ : Ω => b) x ∂μ :=
      integral_mono hf (hia.add hib) hp
    _ = μ.real G * a + μ.real Gᶜ * b := by
      rw [integral_add hia hib, integral_indicator hG, integral_indicator hG.compl]
      simp only [setIntegral_const, smul_eq_mul]
    _ ≤ a + ζ * b := add_le_add
      ((mul_le_mul_of_nonneg_right (measureReal_le_one : μ.real G ≤ 1) ha).trans_eq (one_mul a))
      (mul_le_mul_of_nonneg_right hfail hb)

end MatchingBounds1005.ProbabilityMoment
