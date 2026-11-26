import UpperSmoothingGradient

/-!
The conservative translated-ball argument for the same implemented algorithm.
All measure and volume bounds are derived. No BV, surface-gradient, or
translation estimate is an axiom or a field of the problem model.
-/

open MeasureTheory MeasureTheory.Measure Metric Set
open scoped NNReal

namespace Task006.Full

theorem bounded_setIntegral_sub_common {α V : Type*} [MeasurableSpace α]
    [NormedAddCommGroup V] [NormedSpace ℝ V] {μ : Measure α}
    {g : α → V} {L : ℝ} {A B C : Set α}
    (hg : AEStronglyMeasurable g μ) (hbound : ∀ᵐ z ∂μ, ‖g z‖ ≤ L)
    (hAfin : μ A < ⊤) (hBfin : μ B < ⊤) (hC : MeasurableSet C)
    (hCA : C ⊆ A) (hCB : C ⊆ B) :
    ‖(∫ z in A, g z ∂μ) - (∫ z in B, g z ∂μ)‖ ≤
      L * (μ.real A - μ.real C) + L * (μ.real B - μ.real C) := by
  have hiA : IntegrableOn g A μ :=
    IntegrableOn.of_bound hAfin hg.restrict L (ae_restrict_of_ae hbound)
  have hiB : IntegrableOn g B μ :=
    IntegrableOn.of_bound hBfin hg.restrict L (ae_restrict_of_ae hbound)
  have hnormA := norm_setIntegral_le_of_norm_le_const_ae
    (lt_of_le_of_lt (measure_mono sdiff_subset) hAfin)
    (ae_restrict_of_ae hbound : ∀ᵐ z ∂μ.restrict (A \ C), ‖g z‖ ≤ L)
  have hnormB := norm_setIntegral_le_of_norm_le_const_ae
    (lt_of_le_of_lt (measure_mono sdiff_subset) hBfin)
    (ae_restrict_of_ae hbound : ∀ᵐ z ∂μ.restrict (B \ C), ‖g z‖ ≤ L)
  rw [measureReal_sdiff hCA hC hAfin.ne] at hnormA
  rw [measureReal_sdiff hCB hC hBfin.ne] at hnormB
  have hid : (∫ z in A, g z ∂μ) - (∫ z in B, g z ∂μ) =
      (∫ z in A \ C, g z ∂μ) - (∫ z in B \ C, g z ∂μ) := by
    rw [setIntegral_sdiff hC hiA hCA, setIntegral_sdiff hC hiB hCB]
    abel
  rw [hid]
  exact (norm_sub_le _ _).trans (add_le_add hnormA hnormB)

theorem norm_ballIntegral_sub_le_shell {d : ℕ} {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] {g : Space d → V} {L ρ : ℝ}
    (hg : AEStronglyMeasurable g volume) (hbound : ∀ᵐ z, ‖g z‖ ≤ L)
    (x y : Space d) (hxy : ‖x - y‖ ≤ ρ) :
    ‖(∫ z in closedBall x ρ, g z) - (∫ z in closedBall y ρ, g z)‖ ≤
      2 * L * (volume.real (closedBall (0 : Space d) ρ) -
        volume.real (closedBall (0 : Space d) (ρ - ‖x - y‖))) := by
  have hCA : closedBall x (ρ - ‖x - y‖) ⊆ closedBall x ρ :=
    closedBall_subset_closedBall (by linarith [norm_nonneg (x - y)])
  have hCB : closedBall x (ρ - ‖x - y‖) ⊆ closedBall y ρ :=
    closedBall_subset_closedBall' (by rw [dist_eq_norm]; linarith)
  have hb := bounded_setIntegral_sub_common hg hbound
    (A := closedBall x ρ) (B := closedBall y ρ) (C := closedBall x (ρ - ‖x - y‖))
    measure_closedBall_lt_top measure_closedBall_lt_top measurableSet_closedBall hCA hCB
  rw [addHaar_real_closedBall_center volume x ρ, addHaar_real_closedBall_center volume y ρ,
    addHaar_real_closedBall_center volume x (ρ - ‖x - y‖)] at hb
  convert hb using 1 <;> ring

/-- The precise volume-loss estimate used for the factor `2d`: Bernoulli's
inequality applied to `(1-h/ρ)^d`, with no surface-measure assumption. -/
theorem ball_volume_loss_le {d : ℕ} {ρ h : ℝ} (hρ : 0 < ρ) (hh : 0 ≤ h) (hhρ : h ≤ ρ) :
    volume.real (closedBall (0 : Space d) ρ) -
        volume.real (closedBall (0 : Space d) (ρ - h)) ≤
      (Module.finrank ℝ (Space d) : ℝ) * (h / ρ) * volume.real (closedBall (0 : Space d) ρ) := by
  let n := Module.finrank ℝ (Space d)
  have ht0 : 0 ≤ h / ρ := div_nonneg hh hρ.le
  have ht1 : h / ρ ≤ 1 := (div_le_one hρ).mpr hhρ
  have hbern : 1 - (n : ℝ) * (h / ρ) ≤ (1 - h / ρ) ^ n := by
    have hb := one_add_mul_le_pow (a := -(h / ρ)) (by linarith : -2 ≤ -(h / ρ)) n
    simpa only [mul_neg, sub_eq_add_neg] using hb
  have hid : ρ - h = ρ * (1 - h / ρ) := by field_simp [hρ.ne']
  rw [addHaar_real_closedBall' volume (0 : Space d) hρ.le,
    addHaar_real_closedBall' volume (0 : Space d) (sub_nonneg.mpr hhρ), hid, mul_pow]
  have hm := mul_le_mul_of_nonneg_left hbern
    (mul_nonneg (pow_nonneg hρ.le n) (measureReal_nonneg : 0 ≤ volume.real (closedBall (0 : Space d) 1)))
  dsimp only [n] at hbern hm
  nlinarith

theorem ballSmoothDerivative_norm_le {d : ℕ} {f : Space d → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (ρ : ℝ) (x : Space d) :
    ‖ballSmoothDerivative f ρ x‖ ≤ L := by
  have hb : ∀ᵐ u ∂unitBallLaw d, ‖fderiv ℝ f (x + ρ • u)‖ ≤ L :=
    ae_of_all _ (fun _ => norm_fderiv_le_of_lipschitz ℝ hf)
  simpa only [ballSmoothDerivative, probReal_univ, mul_one]
    using norm_integral_le_of_norm_le_const hb

/-- A proved conservative alternative to the manuscript's sharper smoothing
constant. The same algorithm and its original parameters need only this `2d`
bound to achieve the main theorem's requested accuracy. -/
theorem norm_ballSmoothDerivative_sub_le {d : ℕ} {f : Space d → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) {ρ : ℝ} (hρ : 0 < ρ)
    (hn : 1 ≤ Module.finrank ℝ (Space d)) (x y : Space d) :
    ‖ballSmoothDerivative f ρ x - ballSmoothDerivative f ρ y‖ ≤
      (2 * (Module.finrank ℝ (Space d) : ℝ) * L / ρ) * ‖x - y‖ := by
  let Vρ := volume.real (closedBall (0 : Space d) ρ)
  have hV : 0 < Vρ := by
    exact ENNReal.toReal_pos (measure_closedBall_pos volume (0 : Space d) hρ).ne'
      measure_closedBall_lt_top.ne
  have hnreal : (1 : ℝ) ≤ Module.finrank ℝ (Space d) := by exact_mod_cast hn
  by_cases hsmall : ‖x - y‖ ≤ ρ
  · have hbound : ∀ᵐ z : Space d, ‖fderiv ℝ f z‖ ≤ L :=
      ae_of_all _ (fun _ => norm_fderiv_le_of_lipschitz ℝ hf)
    have hs := norm_ballIntegral_sub_le_shell (measurable_fderiv ℝ f).aestronglyMeasurable
      hbound x y hsmall
    have hv := ball_volume_loss_le (d := d) hρ (norm_nonneg (x - y)) hsmall
    rw [ballSmoothDerivative_ballIntegral f hρ x, ballSmoothDerivative_ballIntegral f hρ y,
      ← smul_sub ((volume.real (closedBall (0 : Space d) ρ))⁻¹)
        (∫ z in closedBall x ρ, fderiv ℝ f z) (∫ z in closedBall y ρ, fderiv ℝ f z),
      norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hV)]
    have hmul := mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hV.le)
    have hvolmul := mul_le_mul_of_nonneg_left hv
      (mul_nonneg (show 0 ≤ 2 * (L : ℝ) by positivity) (inv_nonneg.mpr hV.le))
    change Vρ⁻¹ * ‖(∫ z in closedBall x ρ, fderiv ℝ f z) -
      (∫ z in closedBall y ρ, fderiv ℝ f z)‖ ≤ _
    calc
      _ ≤ Vρ⁻¹ * (2 * L * (Vρ -
          volume.real (closedBall (0 : Space d) (ρ - ‖x - y‖)))) := hmul
      _ ≤ Vρ⁻¹ * (2 * L * ((Module.finrank ℝ (Space d) : ℝ) *
          (‖x - y‖ / ρ) * Vρ)) := by nlinarith [hvolmul]
      _ = _ := by
        field_simp [hV.ne', hρ.ne']
        <;> ring
  · have hlarge : ρ ≤ ‖x - y‖ := le_of_not_ge hsmall
    have hb := (norm_sub_le (ballSmoothDerivative f ρ x) (ballSmoothDerivative f ρ y)).trans
      (add_le_add (ballSmoothDerivative_norm_le hf ρ x) (ballSmoothDerivative_norm_le hf ρ y))
    have hscale : (1 : ℝ) ≤ (Module.finrank ℝ (Space d) : ℝ) * (‖x - y‖ / ρ) := by
      have hr : (1 : ℝ) ≤ ‖x - y‖ / ρ := (le_div_iff₀ hρ).mpr (by simpa using hlarge)
      nlinarith
    have hm := mul_le_mul_of_nonneg_left hscale (show 0 ≤ 2 * (L : ℝ) by positivity)
    have hid : 2 * (L : ℝ) * ((Module.finrank ℝ (Space d) : ℝ) * (‖x - y‖ / ρ)) =
        (2 * (Module.finrank ℝ (Space d) : ℝ) * L / ρ) * ‖x - y‖ := by ring
    rw [hid] at hm
    linarith

#print axioms bounded_setIntegral_sub_common
#print axioms ball_volume_loss_le
#print axioms norm_ballSmoothDerivative_sub_le

end Task006.Full
