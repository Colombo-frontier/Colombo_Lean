import UpperOptimizationMoments
import UpperOptimizationCoupling

/-!
Direct analysis of the implemented algorithm: integrate over the actual Haar
proposal, using good-basis moments on the good event and the deterministic
clipping bound on its complement. No ghost sampler is used in this route.
-/

open MeasureTheory Set

namespace Task006.Full

theorem norm_integral_le_good_bad {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Ω → E} {G : Set Ω} (hG : MeasurableSet G) {a c q : ℝ}
    (ha : 0 ≤ a) (hc : 0 ≤ c) (hq : μ.real Gᶜ ≤ q)
    (hgood : ∀ᵐ ω ∂μ, ω ∈ G → ‖f ω‖ ≤ a)
    (hglobal : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ c) :
    ‖∫ ω, f ω ∂μ‖ ≤ a + c * q := by
  have hi := (integrable_const a (μ := μ)).add ((integrable_const c).indicator hG.compl)
  have hdom : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ a + Gᶜ.indicator (fun _ => c) ω := by
    filter_upwards [hgood, hglobal] with ω hg hb
    by_cases hω : ω ∈ G
    · rw [indicator_of_notMem (show ω ∉ Gᶜ by simpa using hω), add_zero]
      exact hg hω
    · rw [indicator_of_mem (show ω ∈ Gᶜ from hω)]
      linarith
  calc
    ‖∫ ω, f ω ∂μ‖ ≤ ∫ ω, a + Gᶜ.indicator (fun _ => c) ω ∂μ :=
      norm_integral_le_of_norm_le hi hdom
    _ = a + c * μ.real Gᶜ := by
      rw [integral_add (integrable_const _) ((integrable_const _).indicator hG.compl),
        integral_indicator_const c hG.compl]
      simp [mul_comm]
    _ ≤ a + c * q := by linarith [mul_le_mul_of_nonneg_left hq hc]

theorem integral_le_good_bad {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : Integrable f μ)
    {G : Set Ω} (hG : MeasurableSet G) {a c q : ℝ}
    (ha : 0 ≤ a) (hc : 0 ≤ c) (hq : μ.real Gᶜ ≤ q)
    (hgood : ∀ᵐ ω ∂μ, ω ∈ G → f ω ≤ a)
    (hglobal : ∀ᵐ ω ∂μ, f ω ≤ c) :
    (∫ ω, f ω ∂μ) ≤ a + c * q := by
  have hi := (integrable_const a (μ := μ)).add ((integrable_const c).indicator hG.compl)
  have hdom : ∀ᵐ ω ∂μ, f ω ≤ a + Gᶜ.indicator (fun _ => c) ω := by
    filter_upwards [hgood, hglobal] with ω hg hb
    by_cases hω : ω ∈ G
    · rw [indicator_of_notMem (show ω ∉ Gᶜ by simpa using hω), add_zero]
      exact hg hω
    · rw [indicator_of_mem (show ω ∈ Gᶜ from hω)]
      linarith
  calc
    (∫ ω, f ω ∂μ) ≤ ∫ ω, a + Gᶜ.indicator (fun _ => c) ω ∂μ := integral_mono_ae hf hi hdom
    _ = a + c * μ.real Gᶜ := by
      rw [integral_add (integrable_const _) ((integrable_const _).indicator hG.compl),
        integral_indicator_const c hG.compl]
      simp [mul_comm]
    _ ≤ a + c * q := by linarith [mul_le_mul_of_nonneg_left hq hc]

/-- Exact scalar normalization of the direct-mixture regret. -/
theorem mixture_regret_normalization {R t B F q L : ℝ}
    (hR : 0 < R) (ht : 0 < t) (hB : 0 < B) :
    R ^ 2 / (2 * (R / (t * B)) * t) +
        2 * R * (B + F + q * (t * B + L)) +
        (R / (t * B)) * (t * B ^ 2 + q * t ^ 2 * B ^ 2) / 2 =
      3 * R * B + 2 * R * F + (5 / 2 : ℝ) * R * q * t * B + 2 * R * L * q := by
  field_simp [hR.ne', ht.ne', hB.ne']
  <;> ring

/-- The same `Tq ≤ A⁻²` condition as the paper is sufficient for the direct
actual-process route. The conservative smoothing changes the base allowance
from 17/48 to 18/48, still strictly below the requested accuracy. -/
theorem mixture_final_accuracy {eps A t q u : ℝ}
    (heps : 0 < eps) (hA : 4 ≤ A) (ht : 1 ≤ t) (hq : 0 ≤ q) (hu : 0 ≤ u)
    (hub : u ≤ eps / 12) (hqt : q * t ≤ (A ^ 2)⁻¹) :
    18 * eps / 48 + (5 / 2 : ℝ) * u * q * t + 2 * eps * A * q < eps := by
  have hApos : 0 < A := by linarith
  have htpos : 0 < t := by linarith
  have hqle : q ≤ (A ^ 2)⁻¹ := by
    have : q ≤ q * t := by nlinarith
    exact this.trans hqt
  have hInv : (A ^ 2)⁻¹ ≤ (1 / 16 : ℝ) := by
    simpa only [one_div] using one_div_le_one_div_of_le
      (by norm_num : 0 < (16 : ℝ)) (show 16 ≤ A ^ 2 by nlinarith)
  have hAq : A * q ≤ (1 / 4 : ℝ) := by
    have h₁ := mul_le_mul_of_nonneg_left hqle hApos.le
    have hid : A * (A ^ 2)⁻¹ = 1 / A := by field_simp [hApos.ne']
    rw [hid] at h₁
    exact h₁.trans (one_div_le_one_div_of_le (by norm_num : 0 < (4 : ℝ)) hA)
  have huqt : u * (q * t) ≤ eps / 192 := by
    have hmul := mul_le_mul hub (hqt.trans hInv) (mul_nonneg hq htpos.le) (by positivity : 0 ≤ eps / 12)
    nlinarith
  have hlast := mul_le_mul_of_nonneg_left hAq heps.le
  nlinarith

#print axioms norm_integral_le_good_bad
#print axioms mixture_regret_normalization
#print axioms mixture_final_accuracy

end Task006.Full
