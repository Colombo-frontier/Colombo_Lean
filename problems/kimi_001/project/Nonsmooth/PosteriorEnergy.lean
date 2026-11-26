import Nonsmooth.ConditionalMean

open MeasureTheory Filter
open scoped InnerProductSpace ENNReal
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {α E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {m₀ : MeasurableSpace α} {Q : Measure α} [IsProbabilityMeasure Q]

theorem conditional_mean_increment_energy {m n : MeasurableSpace α} (hmn : m ≤ n)
    (hn : n ≤ m₀) {V : α → E} (hV : MemLp V 2 Q) :
    (∫ a, ‖(Q[V | n]) a - (Q[V | m]) a‖ ^ 2 ∂Q) =
      (∫ a, ‖(Q[V | n]) a‖ ^ 2 ∂Q) - ∫ a, ‖(Q[V | m]) a‖ ^ 2 ∂Q := by
  letI : MeasurableSpace α := m₀
  have hN : MemLp (Q[V | n]) 2 Q := hV.condExp (by norm_num)
  have hM : MemLp (Q[V | m]) 2 Q := hV.condExp (by norm_num)
  have hNi := (memLp_two_iff_integrable_sq_norm hN.aestronglyMeasurable).mp hN
  have hMi := (memLp_two_iff_integrable_sq_norm hM.aestronglyMeasurable).mp hM
  have hinner := integral_inner_condExp (hmn.trans hn) hN hM
    (stronglyMeasurable_condExp.aestronglyMeasurable (μ := Q))
  have he : (∫ a, ⟪(Q[V | n]) a, (Q[V | m]) a⟫_ℝ ∂Q) = ∫ a, ‖(Q[V | m]) a‖ ^ 2 ∂Q := by
    rw [hinner]
    apply integral_congr_ae
    filter_upwards [condExp_condExp_of_le hmn hn (f := V) (μ := Q)] with a ha
    rw [ha, real_inner_self_eq_norm_sq]
  simp_rw [norm_sub_sq_real]
  have hNM : Integrable (fun a => 2 * ⟪(Q[V | n]) a, (Q[V | m]) a⟫_ℝ) Q :=
    (integrable_inner_of_memLp hN hM).const_mul 2
  have hsub : Integrable (fun a => ‖(Q[V | n]) a‖ ^ 2 - 2 * ⟪(Q[V | n]) a, (Q[V | m]) a⟫_ℝ) Q :=
    hNi.sub hNM
  rw [integral_add hsub hMi, integral_sub hNi hNM, integral_const_mul, he]
  ring

theorem conditional_mean_energy_from_increments (m : ℕ → MeasurableSpace α)
    (hmono : Monotone m) (hm : ∀ n, m n ≤ m₀) {V : α → E} (hV : MemLp V 2 Q)
    (hzero : (∫ a, ‖(Q[V | m 0]) a‖ ^ 2 ∂Q) = 0) {C : ℝ} (T : ℕ)
    (hstep : ∀ n < T, (∫ a, ‖(Q[V | m (n + 1)]) a - (Q[V | m n]) a‖ ^ 2 ∂Q) ≤ C) :
    (∫ a, ‖(Q[V | m T]) a‖ ^ 2 ∂Q) ≤ (T : ℝ) * C := by
  induction T with
  | zero => simp only [hzero, Nat.cast_zero, zero_mul, le_refl]
  | succ T ih =>
    have hprev := ih (fun n hn => hstep n (Nat.lt.step hn))
    have hnow := hstep T (Nat.lt_succ_self T)
    rw [conditional_mean_increment_energy (hmono (Nat.le_succ T)) (hm (T + 1)) hV] at hnow
    simp only [Nat.cast_add, Nat.cast_one]
    nlinarith

end
end Nonsmooth
