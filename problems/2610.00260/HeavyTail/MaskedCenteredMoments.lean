import HeavyTail.MaskedRawMoments

/-! Centered strong and directional moments of the coordinate sampler. -/

open MeasureTheory
open scoped InnerProductSpace
namespace HeavyTail.MaskedLower
noncomputable section

theorem finite_centered_norm_moment_le {Ω E : Type*} [MeasurableSpace Ω]
    [Finite Ω] [MeasurableSingletonClass Ω] [NormedAddCommGroup E]
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Ω → E) (g : E)
    {p : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2) :
    (∫ ω, ‖F ω - g‖ ^ p ∂P) ≤ 2 * ((∫ ω, ‖F ω‖ ^ p ∂P) + ‖g‖ ^ p) := by
  calc
    _ ≤ ∫ ω, 2 * (‖F ω‖ ^ p + ‖g‖ ^ p) ∂P :=
      integral_mono Integrable.of_finite Integrable.of_finite
        (fun ω => norm_sub_rpow_le_twice (F ω) g hp hp2)
    _ = _ := by
      rw [integral_const_mul, integral_add Integrable.of_finite Integrable.of_finite,
        integral_const]
      simp

theorem coordinateReply_centered_norm_le {k : ℕ} {π p a b : ℝ} (hπ : 0 < π)
    (hkπ : (k : ℝ) * π ≤ 1) (hp : 1 ≤ p) (hp2 : p ≤ 2) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (g : HardSpace k) (hg : ∀ j, |g j| ≤ b) (hn : ‖g‖ ≤ a) :
    (∫ m, ‖coordinateReply π g m - g‖ ^ p ∂(coordinateCoin π hπ.le hkπ).toMeasure) ≤
      2 * (((k : ℝ) * π) * (b / π) ^ p + a ^ p) := by
  apply (finite_centered_norm_moment_le (coordinateCoin π hπ.le hkπ).toMeasure
    (coordinateReply π g) g hp hp2).trans
  exact mul_le_mul_of_nonneg_left
    (add_le_add (coordinateReply_norm_moment_le hπ hkπ (by linarith) hb g hg)
      (Real.rpow_le_rpow (norm_nonneg _) hn (by linarith))) (by norm_num)

theorem coordinateReply_centered_direction_le {k : ℕ} (hk : 0 < k) {π p a b : ℝ}
    (hπ : 0 < π) (hkπ : (k : ℝ) * π ≤ 1) (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (g : HardSpace k) (hg : ∀ j, |g j| ≤ b) (hn : ‖g‖ ≤ a)
    (w : HardSpace k) (hw : ‖w‖ = 1) :
    (∫ m, |⟪w, coordinateReply π g m - g⟫_ℝ| ^ p ∂(coordinateCoin π hπ.le hkπ).toMeasure) ≤
      2 * (((k : ℝ) * π) * ((b / π) * (1 / Real.sqrt k)) ^ p + a ^ p) := by
  have hi := finite_centered_norm_moment_le (coordinateCoin π hπ.le hkπ).toMeasure
    (fun m => ⟪w, coordinateReply π g m⟫_ℝ) ⟪w, g⟫_ℝ hp hp2
  simp only [Real.norm_eq_abs, ← inner_sub_right] at hi
  apply hi.trans
  have hinner : |⟪w, g⟫_ℝ| ≤ a := by
    calc
      _ ≤ ‖w‖ * ‖g‖ := abs_real_inner_le_norm _ _
      _ ≤ a := by simpa only [hw, one_mul] using hn
  exact mul_le_mul_of_nonneg_left
    (add_le_add (coordinateReply_direction_moment_le hk hπ hkπ (by linarith) hp2 hb g hg w hw)
      (Real.rpow_le_rpow (abs_nonneg _) hinner (by linarith))) (by norm_num)

end
end HeavyTail.MaskedLower
