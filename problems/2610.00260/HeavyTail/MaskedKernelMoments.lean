import HeavyTail.MaskedCenteredMoments
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-! Integrability, unbiasedness, Lp membership, and the actual centered kernel
moment estimates for the masked-coordinate hard family. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace
namespace HeavyTail.MaskedLower
noncomputable section

theorem hardGradient_coordinate_le {k : ℕ} {a : ℝ} (ha : 0 ≤ a)
    (ρ : ℝ) (v : Fin k → ℝ) (x : HardSpace k) (j : Fin k) :
    |hardGradient a ρ v x j| ≤ a / Real.sqrt k := by
  have hb : 0 ≤ a / Real.sqrt (k : ℝ) := by positivity
  change |a / Real.sqrt (k : ℝ) * Real.sign (x j - ρ * v j)| ≤ _
  rcases Real.sign_apply_eq (x j - ρ * v j) with h | h | h <;> rw [h] <;> simp [abs_of_nonneg hb, hb]

theorem maskedKernel_integrable {k : ℕ} (a ρ π : ℝ) (hπ : 0 ≤ π)
    (hkπ : (k : ℝ) * π ≤ 1) (v : Fin k → Bool) (x : HardSpace k) :
    Integrable (fun y => y) (maskedKernel a ρ π hπ hkπ v x) := by
  change Integrable (fun y : HardSpace k => y) ((coordinateCoin π hπ hkπ).toMeasure.map _)
  apply (integrable_map_measure measurable_id.aestronglyMeasurable
    (Measurable.of_discrete : Measurable (fun b => maskedSampler a ρ π v (x, b))).aemeasurable).mpr
  exact Integrable.of_finite

theorem maskedKernel_unbiased {k : ℕ} (a ρ : ℝ) {π : ℝ} (hπ : 0 < π)
    (hkπ : (k : ℝ) * π ≤ 1) (v : Fin k → Bool) (x : HardSpace k) :
    (∫ y, y ∂maskedKernel a ρ π hπ.le hkπ v x) = hardGradient a ρ (gaussianSigns v) x := by
  change (∫ y : HardSpace k, y ∂((coordinateCoin π hπ.le hkπ).toMeasure.map _)) = _
  calc
    _ = ∫ b, maskedSampler a ρ π v (x, b) ∂(coordinateCoin π hπ.le hkπ).toMeasure :=
      integral_map (Measurable.of_discrete :
        Measurable (fun b => maskedSampler a ρ π v (x, b))).aemeasurable
        (measurable_id : Measurable (fun y : HardSpace k => y)).aestronglyMeasurable
    _ = _ := by
      simpa only [maskedSampler] using
        coordinateReply_unbiased hπ hkπ (hardGradient a ρ (gaussianSigns v) x)

theorem maskedKernel_noise_memLp {k : ℕ} (a ρ π : ℝ) (hπ : 0 ≤ π)
    (hkπ : (k : ℝ) * π ≤ 1) (v : Fin k → Bool) (x : HardSpace k) (p : ℝ≥0∞) :
    MemLp (fun y => y - ∫ z, z ∂maskedKernel a ρ π hπ hkπ v x) p
      (maskedKernel a ρ π hπ hkπ v x) := by
  change MemLp _ p ((coordinateCoin π hπ hkπ).toMeasure.map _)
  apply (memLp_map_measure_iff
    (measurable_id.sub measurable_const).aestronglyMeasurable
    (Measurable.of_discrete : Measurable (fun b => maskedSampler a ρ π v (x, b))).aemeasurable).mpr
  exact MemLp.of_discrete

theorem maskedKernel_centered_moments {k : ℕ} (hk : 0 < k) {a π p : ℝ} (ha : 0 ≤ a)
    (hπ : 0 < π) (hkπ : (k : ℝ) * π ≤ 1) (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (ρ : ℝ) (v : Fin k → Bool) (x : HardSpace k) :
    (∫ y, ‖y - ∫ z, z ∂maskedKernel a ρ π hπ.le hkπ v x‖ ^ p
      ∂maskedKernel a ρ π hπ.le hkπ v x) ≤
        2 * (((k : ℝ) * π) * ((a / Real.sqrt k) / π) ^ p + a ^ p) ∧
    ∀ w : HardSpace k, ‖w‖ = 1 →
      (∫ y, |⟪w, y - ∫ z, z ∂maskedKernel a ρ π hπ.le hkπ v x⟫_ℝ| ^ p
        ∂maskedKernel a ρ π hπ.le hkπ v x) ≤
          2 * (((k : ℝ) * π) * (((a / Real.sqrt k) / π) * (1 / Real.sqrt k)) ^ p + a ^ p) := by
  rw [maskedKernel_unbiased a ρ hπ hkπ v x]
  let g := hardGradient a ρ (gaussianSigns v) x
  have hn : ‖g‖ ≤ a := hardGradient_norm_le hk ha ρ (gaussianSigns v) x
  have hcoord : ∀ j, |g j| ≤ a / Real.sqrt k := hardGradient_coordinate_le ha ρ (gaussianSigns v) x
  have hmap : Measurable (fun b => maskedSampler a ρ π v (x, b)) := Measurable.of_discrete
  constructor
  · change (∫ y, ‖y - g‖ ^ p ∂((coordinateCoin π hπ.le hkπ).toMeasure.map _)) ≤ _
    have heq := integral_map (μ := (coordinateCoin π hπ.le hkπ).toMeasure) hmap.aemeasurable
      ((((measurable_id : Measurable (fun y : HardSpace k => y)).sub_const g).norm).pow_const p).aestronglyMeasurable
    exact heq.trans_le (coordinateReply_centered_norm_le hπ hkπ hp hp2 ha (by positivity) g hcoord hn)
  · intro w hw
    change (∫ y, |⟪w, y - g⟫_ℝ| ^ p ∂((coordinateCoin π hπ.le hkπ).toMeasure.map _)) ≤ _
    have hcont : Continuous (fun y : HardSpace k => |⟪w, y - g⟫_ℝ|) :=
      (continuous_const.inner (continuous_id.sub continuous_const)).abs
    have heq := integral_map (μ := (coordinateCoin π hπ.le hkπ).toMeasure)
      hmap.aemeasurable (hcont.measurable.pow_const p).aestronglyMeasurable
    exact heq.trans_le (coordinateReply_centered_direction_le hk hπ hkπ hp hp2 ha (by positivity)
      g hcoord hn w hw)

end
end HeavyTail.MaskedLower
