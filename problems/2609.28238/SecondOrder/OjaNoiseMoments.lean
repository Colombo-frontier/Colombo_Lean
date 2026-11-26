import SecondOrder.OjaRayleighNoise

open MeasureTheory Filter
open scoped InnerProductSpace

namespace SecondOrder
noncomputable section

theorem abs_tail_of_second_moment {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : Ω → ℝ} {r V : ℝ}
    (hi : Integrable (fun w => X w^2) μ) (hr : 0 < r)
    (hV : (∫ w, X w^2 ∂μ) ≤ V) :
    μ {w | r ≤ |X w|} ≤ ENNReal.ofReal (V/r^2) := by
  have hsq : 0 < r^2 := sq_pos_of_pos hr
  have hb := (hi.div_const (r^2)).measure_le_integral
    (Eventually.of_forall (fun w => div_nonneg (sq_nonneg _) hsq.le))
    (s := {w | r ≤ |X w|}) (fun w hw => by
      apply (le_div_iff₀ hsq).mpr
      simpa only [one_mul, sq_abs] using pow_le_pow_left₀ hr.le hw 2)
  refine hb.trans (ENNReal.ofReal_le_ofReal ?_)
  rw [integral_div]
  exact div_le_div_of_nonneg_right hV hsq.le

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {P : Parameters} {ν : ℝ}
  {F : Point d → ℝ} {f : Ω → Point d → ℝ}

/-- All mixed terms disappear by integrating the fresh sample first. -/
theorem CommonLoss.ojaRayleighNoise_mean (h : CommonLoss μ P ν F f)
    {η : ℝ} (hη : 0 ≤ η) (x v : Point d) (hv : ‖v‖ = 1) (N : ℕ) :
    (∫ w, ojaRayleighNoise P F f η x v N w ∂drawsLaw μ N) = 0 := by
  induction N with
  | zero => simp [ojaRayleighNoise]
  | succ N ih =>
    have hi := h.ojaRayleighNoise_integrable hη x v hv (N+1)
    change Integrable (fun w : Draws Ω N × Ω => ojaRayleighNoise P F f η x v N w.1 +
      shiftedRayleighError P F f x (ojaHvpRun P f η x v N w.1) w.2)
      ((drawsLaw μ N).prod μ) at hi
    change (∫ w : Draws Ω N × Ω, ojaRayleighNoise P F f η x v N w.1 +
      shiftedRayleighError P F f x (ojaHvpRun P f η x v N w.1) w.2
      ∂(drawsLaw μ N).prod μ) = 0
    rw [integral_prod _ hi]
    have hc (w : Draws Ω N) :
        (∫ z, ojaRayleighNoise P F f η x v N w +
          shiftedRayleighError P F f x (ojaHvpRun P f η x v N w) z ∂μ) =
        ojaRayleighNoise P F f η x v N w := by
      rw [integral_add (integrable_const _)
        (h.shiftedRayleighError_integrable x (ojaHvpRun P f η x v N w)),
        h.shiftedRayleighError_mean]
      simp
    simp_rw [hc]
    exact ih

theorem CommonLoss.ojaRayleighNoise_second_moment (h : CommonLoss μ P ν F f)
    {η : ℝ} (hη : 0 ≤ η) (x v : Point d) (hv : ‖v‖ = 1) (N : ℕ) :
    (∫ w, ojaRayleighNoise P F f η x v N w ^ 2 ∂drawsLaw μ N) ≤ (N : ℝ) := by
  induction N with
  | zero => simp [ojaRayleighNoise]
  | succ N ih =>
    have hi := h.ojaRayleighNoise_sq_integrable hη x v hv (N+1)
    change Integrable (fun w : Draws Ω N × Ω => (ojaRayleighNoise P F f η x v N w.1 +
      shiftedRayleighError P F f x (ojaHvpRun P f η x v N w.1) w.2)^2)
      ((drawsLaw μ N).prod μ) at hi
    change (∫ w : Draws Ω N × Ω, (ojaRayleighNoise P F f η x v N w.1 +
      shiftedRayleighError P F f x (ojaHvpRun P f η x v N w.1) w.2)^2
      ∂(drawsLaw μ N).prod μ) ≤ (N+1:ℕ)
    rw [integral_prod _ hi]
    have hb := integral_mono_of_nonneg
      (Eventually.of_forall (fun w => integral_nonneg (fun z => sq_nonneg _)))
      ((h.ojaRayleighNoise_sq_integrable hη x v hv N).add (integrable_const (1:ℝ)))
      (show ∀ᵐ w ∂drawsLaw μ N,
          (∫ z, (ojaRayleighNoise P F f η x v N w +
            shiftedRayleighError P F f x (ojaHvpRun P f η x v N w) z)^2 ∂μ) ≤
            ojaRayleighNoise P F f η x v N w ^ 2 + 1 from by
        filter_upwards [h.ojaHvpRun_ae_norm hη N] with w hw
        rw [integral_add_sq_zero_mean (h.shiftedRayleighError_integrable x _)
          (h.shiftedRayleighError_sq_integrable x _) (h.shiftedRayleighError_mean x _)]
        have hm := h.shiftedRayleighError_second_moment x (ojaHvpRun P f η x v N w)
        rw [hw x v hv, one_pow] at hm
        exact add_le_add_left hm _)
    have hadd : (∫ w, ojaRayleighNoise P F f η x v N w ^ 2 + 1 ∂drawsLaw μ N) =
        (∫ w, ojaRayleighNoise P F f η x v N w ^ 2 ∂drawsLaw μ N) + 1 := by
      rw [integral_add (h.ojaRayleighNoise_sq_integrable hη x v hv N) (integrable_const _)]
      simp
    change _ ≤ (∫ w, ojaRayleighNoise P F f η x v N w ^ 2 + 1 ∂drawsLaw μ N) at hb
    rw [hadd] at hb
    exact hb.trans (by simpa using add_le_add_right ih 1)

theorem CommonLoss.ojaRayleighNoise_tail (h : CommonLoss μ P ν F f)
    {η : ℝ} (hη : 0 ≤ η) (x v : Point d) (hv : ‖v‖ = 1) (N : ℕ)
    {r : ℝ} (hr : 0 < r) :
    drawsLaw μ N {w | r ≤ |ojaRayleighNoise P F f η x v N w|} ≤ ENNReal.ofReal ((N:ℝ)/r^2) :=
  abs_tail_of_second_moment (h.ojaRayleighNoise_sq_integrable hη x v hv N) hr
    (h.ojaRayleighNoise_second_moment hη x v hv N)

end
end SecondOrder
