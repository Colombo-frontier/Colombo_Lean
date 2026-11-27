import UpperProgramBlockTransfer
import UpperOptimizationFreshRegret
import UpperOptimizationRecurrence

/-! Full finite-time regret for the implemented block recursion. Its fresh
conditional laws are derived from the iid product, not supplied as assumptions. -/

open MeasureTheory MeasureTheory.Measure Metric Set
open scoped BigOperators NNReal

namespace Task006.Full

attribute [local irreducible] upperBlockDirection upperBlockIterate

set_option maxHeartbeats 3000000 in
theorem upperBlock_regret {d T : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (P : UpperProgramParameters) (hT : 0 < T)
    (F : Space d → Ω → ℝ) (hF : Measurable (Function.uncurry F))
    (f : Space d → ℝ) (C : ℝ≥0) (hfLip : LipschitzWith C f)
    (hfConvex : ConvexOn ℝ (closedBall (0 : Space d) (P.R - (P.ρ + P.δ))) f)
    (v : Space d → Space d) {β W : ℝ}
    (hgi : ∀ x, ‖x‖ ≤ P.R - (P.ρ + P.δ) →
      Integrable (upperBlockDirection P F x) (upperSampleBlockLaw d μ))
    (hbias : ∀ x, ‖x‖ ≤ P.R - (P.ρ + P.δ) →
      ‖(∫ b, upperBlockDirection P F x b ∂upperSampleBlockLaw d μ) - v x‖ ≤ β)
    (hmoment : ∀ x, ‖x‖ ≤ P.R - (P.ρ + P.δ) →
      (∫ b, ‖upperBlockDirection P F x b‖ ^ 2 ∂upperSampleBlockLaw d μ) ≤ W)
    (z : Space d) (hz : ‖z‖ ≤ P.R - (P.ρ + P.δ))
    (hsub : ∀ x, ‖x‖ ≤ P.R - (P.ρ + P.δ) → f x - f z ≤ inner ℝ (x - z) (v x)) :
    (∫ blocks, f (upperBlockOutput P F blocks) - f z
      ∂Measure.pi (fun _ : Fin T => upperSampleBlockLaw d μ)) ≤
      P.R ^ 2 / (2 * P.η * T) + 2 * P.R * β + P.η * W / 2 := by
  let ν := upperSampleBlockLaw d μ
  let π := Measure.pi (fun _ : Fin T => ν)
  let X : ℕ → (Fin T → UpperSampleBlock d Ω) → Space d :=
    fun t blocks => upperBlockIterate P F blocks t
  let g : Space d → UpperSampleBlock d Ω → Space d := upperBlockDirection P F
  let Gmax := Real.sqrt d * P.b
  have hR : 0 ≤ P.R := by linarith [P.inner_nonneg, P.rho_nonneg, P.delta_pos]
  have hrR : P.R - (P.ρ + P.δ) ≤ P.R := by linarith [P.rho_nonneg, P.delta_pos]
  have hG : 0 ≤ Gmax := mul_nonneg (Real.sqrt_nonneg _) P.clip_nonneg
  have hXm (t : ℕ) : Measurable (X t) := upperBlockIterate_measurable P hF t
  have hXn (t : ℕ) (w) : ‖X t w‖ ≤ P.R - (P.ρ + P.δ) :=
    upperBlockIterate_norm_le P F w t
  have hgm : Measurable (Function.uncurry g) := upperBlockDirection_measurable P hF
  have hgn (x : Space d) (b) : ‖g x b‖ ≤ Gmax := upperBlockDirection_norm_le P F x b
  have hdist {x : Space d} (hx : ‖x‖ ≤ P.R - (P.ρ + P.δ)) : ‖x - z‖ ≤ 2 * P.R := by
    have hh := norm_sub_le x z
    linarith
  have hgap (t : ℕ) : Integrable (fun w => f (X t w) - f z) π := by
    apply Integrable.of_bound ((hfLip.continuous.measurable.comp (hXm t)).sub measurable_const).aestronglyMeasurable
      ((C : ℝ) * (2 * P.R))
    filter_upwards [] with w
    exact (hfLip.norm_sub_le _ _).trans (mul_le_mul_of_nonneg_left (hdist (hXn t w)) C.coe_nonneg)
  have hsq (t : ℕ) : Integrable (fun w => ‖X t w - z‖ ^ 2) π := by
    apply Integrable.of_bound (((hXm t).sub measurable_const).norm.pow_const 2).aestronglyMeasurable
      ((2 * P.R) ^ 2)
    filter_upwards [] with w
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hdist (hXn t w)) 2
  have hrec (t : ℕ) (ht : t < T) :
      (∫ w, f (X t w) - f z ∂π) ≤
        ((∫ w, ‖X t w - z‖ ^ 2 ∂π) - (∫ w, ‖X (t + 1) w - z‖ ^ 2 ∂π)) /
          (2 * P.η) + (2 * P.R * β + P.η * W / 2) := by
    let tt : Fin T := ⟨t, ht⟩
    let stateLaw : Measure (Space d) := π.map (X t)
    letI : IsProbabilityMeasure stateLaw := Measure.isProbabilityMeasure_map (hXm t).aemeasurable
    have hpast : ∀ w w', (∀ j : Fin T, j.val < tt.val → w j = w' j) → X t w = X t w' :=
      fun w w' hh => upperBlockIterate_past P F t hh
    have hs : ∀ᵐ x ∂stateLaw, ‖x‖ ≤ P.R - (P.ρ + P.δ) :=
      (ae_map_iff (hXm t).aemeasurable (measurableSet_le measurable_norm measurable_const)).mpr
        (ae_of_all _ (hXn t))
    have hsprod : ∀ᵐ p ∂stateLaw.prod ν, ‖p.1‖ ≤ P.R - (P.ρ + P.δ) :=
      quasiMeasurePreserving_fst.ae hs
    have hinnerM : Measurable (fun p : Space d × UpperSampleBlock d Ω =>
        inner ℝ (p.1 - z) (g p.1 p.2)) := (measurable_fst.sub measurable_const).inner hgm
    have hinnerProd : Integrable (fun p : Space d × UpperSampleBlock d Ω =>
        inner ℝ (p.1 - z) (g p.1 p.2)) (stateLaw.prod ν) := by
      apply Integrable.of_bound hinnerM.aestronglyMeasurable (2 * P.R * Gmax)
      filter_upwards [hsprod] with p hp
      exact (norm_inner_le_norm _ _).trans
        (mul_le_mul (hdist hp) (hgn _ _) (norm_nonneg _) (by positivity))
    have hsecondProd : Integrable (fun p : Space d × UpperSampleBlock d Ω => ‖g p.1 p.2‖ ^ 2)
        (stateLaw.prod ν) := by
      apply Integrable.of_bound (hgm.norm.pow_const 2).aestronglyMeasurable (Gmax ^ 2)
      filter_upwards [] with p
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hgn _ _) 2
    have hfeas : ∀ w, X t w ∈ closedBall (0 : Space d) (P.R - (P.ρ + P.δ)) :=
      fun w => by simpa only [mem_closedBall, dist_zero_right] using hXn t w
    have hgrad := fresh_expected_subgradient_le ν tt (X t) (hXm t) hpast
      (K := closedBall (0 : Space d) (P.R - (P.ρ + P.δ)))
      isClosed_closedBall.measurableSet hfeas g hgm f
      hfLip.continuous.measurable v z (by positivity : 0 ≤ 2 * P.R)
      (fun x hx => hgi x (by simpa only [mem_closedBall, dist_zero_right] using hx))
      (fun x hx => hbias x (by simpa only [mem_closedBall, dist_zero_right] using hx))
      (fun x hx => hsub x (by simpa only [mem_closedBall, dist_zero_right] using hx))
      (fun x hx => hdist (by simpa only [mem_closedBall, dist_zero_right] using hx)) (hgap t) hinnerProd
    have hsecond := fresh_second_moment_le ν tt (X t) (hXm t) hpast
      (K := closedBall (0 : Space d) (P.R - (P.ρ + P.δ)))
      isClosed_closedBall.measurableSet hfeas g hgm
      (fun x hx => hmoment x (by simpa only [mem_closedBall, dist_zero_right] using hx)) hsecondProd
    have hpair : Measurable (fun w : Fin T → UpperSampleBlock d Ω => (X t w, w tt)) :=
      (hXm t).prodMk (measurable_pi_apply tt)
    have hinnerI : Integrable (fun w => inner ℝ (X t w - z) (g (X t w) (w tt))) π := by
      apply Integrable.of_bound (hinnerM.comp hpair).aestronglyMeasurable (2 * P.R * Gmax)
      filter_upwards [] with w
      exact (norm_inner_le_norm _ _).trans
        (mul_le_mul (hdist (hXn t w)) (hgn _ _) (norm_nonneg _) (by positivity))
    have hsecondI : Integrable (fun w => ‖g (X t w) (w tt)‖ ^ 2) π := by
      apply Integrable.of_bound ((hgm.comp hpair).norm.pow_const 2).aestronglyMeasurable (Gmax ^ 2)
      filter_upwards [] with w
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hgn _ _) 2
    have hstep : ∀ᵐ w ∂π, X (t + 1) w = ballProj (P.R - (P.ρ + P.δ)) P.inner_nonneg
        (X t w - P.η • g (X t w) (w tt)) := by
      filter_upwards [] with w
      change upperBlockIterate P F w (t + 1) = _
      rw [upperBlockIterate, dif_pos ht]
    have he := projected_step_expected_of_inner (μ := π) P.inner_nonneg P.eta_pos
      (by positivity : 0 ≤ 2 * P.R) (X t) (X (t + 1))
      (fun w => g (X t w) (w tt)) (fun w => v (X t w)) (fun w => f (X t w) - f z) z hz
      hstep hinnerI (hsq t) (hsq (t + 1)) hsecondI (hgap t) hgrad hsecond
    linarith
  have hinit : (∫ w, ‖X 0 w - z‖ ^ 2 ∂π) ≤ P.R ^ 2 := by
    have hn : ‖z‖ ≤ P.R := hz.trans hrR
    simpa only [X, upperBlockIterate, zero_sub, norm_neg, integral_const, probReal_univ, one_smul]
      using pow_le_pow_left₀ (norm_nonneg z) hn 2
  have hterminal := finite_descent_regret hT P.eta_pos
    (fun t => ∫ w, ‖X t w - z‖ ^ 2 ∂π) (fun t => ∫ w, f (X t w) - f z ∂π)
    hinit (integral_nonneg (fun _ => sq_nonneg _)) hrec
  have havg : Integrable (fun w => f (upperBlockOutput P F w) - f z) π := by
    apply Integrable.of_bound ((hfLip.continuous.measurable.comp
      (upperBlockOutput_measurable P hF)).sub measurable_const).aestronglyMeasurable
      ((C : ℝ) * (2 * P.R))
    filter_upwards [] with w
    exact (hfLip.norm_sub_le _ _).trans (mul_le_mul_of_nonneg_left
      (hdist (upperBlockOutput_norm_le P hT F w)) C.coe_nonneg)
  have hj : ∀ᵐ w ∂π, f (upperBlockOutput P F w) - f z ≤
      (∑ t ∈ Finset.range T, (f (X t w) - f z)) / T := by
    filter_upwards [] with w
    exact convex_time_average_gap hfConvex hT (fun t _ => by simpa using hXn t w) z
  have hsumI := integrable_finsetSum (Finset.range T) (fun t _ => hgap t)
  have hm := integral_mono_ae havg (hsumI.div_const (T : ℝ)) hj
  simp only [integral_div] at hm
  rw [integral_finsetSum (Finset.range T) (fun t _ => hgap t)] at hm
  exact hm.trans (by linarith [hterminal])

#print axioms upperBlock_regret

end Task006.Full
