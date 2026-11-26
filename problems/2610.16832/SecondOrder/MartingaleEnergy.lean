import SecondOrder.BinaryEnergy
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

open MeasureTheory Filter
open scoped InnerProductSpace MeasureTheory BigOperators Classical

namespace SecondOrder

variable {Ω E : Type*} {m₀ : MeasurableSpace Ω} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [CompleteSpace E] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- A past-measurable square-integrable vector is orthogonal to a new vector
whose conditional mean is zero. This uses the L2 conditional projection. -/
theorem integral_inner_zero_of_condExp {X Y : Ω → E} {s : MeasurableSpace Ω}
    (hs : s ≤ m₀) (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
    (hXm : AEStronglyMeasurable[s] X μ) (hY0 : μ[Y | s] =ᵐ[μ] (fun _ => 0)) :
    (∫ w, ⟪X w,Y w⟫_ℝ ∂μ) = 0 := by
  letI : MeasurableSpace Ω := m₀
  have hXp : AEStronglyMeasurable[s] (hX.toLp X : Ω → E) μ := hXm.congr hX.coeFn_toLp.symm
  have hp := inner_condExpL2_eq_inner_fun (𝕜 := ℝ) hs (hY.toLp Y) (hX.toLp X) hXp
  have hz := (hY.condExpL2_ae_eq_condExp (𝕜 := ℝ) hs).trans hY0
  calc
    _ = ⟪hY.toLp Y,hX.toLp X⟫_ℝ := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hX.coeFn_toLp,hY.coeFn_toLp] with w hx hy
      rw [hx,hy,real_inner_comm]
    _ = ⟪(condExpL2 E ℝ hs (hY.toLp Y) : Lp E 2 μ),hX.toLp X⟫_ℝ := hp.symm
    _ = 0 := by
      rw [L2.inner_def]
      have he : (fun w => ⟪(condExpL2 E ℝ hs (hY.toLp Y) : Ω → E) w,
          (hX.toLp X : Ω → E) w⟫_ℝ) =ᵐ[μ] (fun _ => (0 : ℝ)) := by
        filter_upwards [hz] with w hw
        rw [hw,inner_zero_left]
      rw [integral_congr_ae he]
      simp

theorem martingale_differences_orthogonal {M : ℕ} (m : Fin M → Ω → E)
    (past : Fin M → MeasurableSpace Ω) (hp : ∀ j, past j ≤ m₀)
    (hm : ∀ k, MemLp (m k) 2 μ)
    (hadapt : ∀ i j, i < j → AEStronglyMeasurable[past j] (m i) μ)
    (hzero : ∀ j, μ[m j | past j] =ᵐ[μ] (fun _ => 0))
    (i j : Fin M) (hij : i ≠ j) : (∫ w, ⟪m i w,m j w⟫_ℝ ∂μ) = 0 := by
  rcases lt_or_gt_of_ne hij with h|h
  · exact integral_inner_zero_of_condExp (hp j) (hm i) (hm j) (hadapt i j h) (hzero j)
  · have hh := integral_inner_zero_of_condExp (hp i) (hm j) (hm i) (hadapt j i h) (hzero i)
    simpa only [real_inner_comm] using hh

/-- The manuscript's capped dyadic-energy lemma for genuine martingale
differences, arbitrary probability laws, and the actual online node schedule. -/
theorem completed_chord_energy_martingale (M L q : ℕ) (N : Ω → ℕ) (hN : Measurable N)
    (hcap : ∀ w, N w ≤ M) (x : Ω → ℕ → E) (a m : Fin M → Ω → E)
    (hx : ∀ w k, x w (k.val+1)-x w k.val = a k w+m k w)
    (ha : ∀ k, Integrable (a k) μ) (ha2 : ∀ k, Integrable (fun w => ‖a k w‖^2) μ)
    (hm : ∀ k, MemLp (m k) 2 μ)
    (hs : ∀ w, (Finset.univ.filter (fun k => a k w ≠ 0)).card ≤ q)
    (past : Fin M → MeasurableSpace Ω) (hp : ∀ j, past j ≤ m₀)
    (hadapt : ∀ i j, i < j → AEStronglyMeasurable[past j] (m i) μ)
    (hzero : ∀ j, μ[m j | past j] =ᵐ[μ] (fun _ => 0)) :
    (∫ w, ∑ i ∈ completedNodes L (N w), ‖x w (nodeRight i)-x w (nodeLeft i)‖^2 ∂μ) ≤
      2*(L : ℝ)*((q : ℝ)*(∫ w, ∑ k, ‖a k w‖^2 ∂μ)+(∫ w, ∑ k, ‖m k w‖^2 ∂μ)) := by
  exact completed_chord_energy M L q N hN hcap x a m hx ha
    (fun k => (hm k).integrable (by norm_num)) ha2
    (fun k => (memLp_two_iff_integrable_sq_norm (hm k).1).mp (hm k)) hs
    (martingale_differences_orthogonal m past hp hm hadapt hzero)

end SecondOrder
