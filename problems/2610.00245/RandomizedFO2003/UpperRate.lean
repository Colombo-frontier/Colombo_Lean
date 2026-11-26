import RandomizedFO2003.RestartCounting
import RandomizedFO2003.Algebra

namespace RandomizedFO2003.Accelerated

theorem restartArgument_factorization {ε Δ ρ : ℝ} (hε : 0 < ε) (hρ : 0 < ρ) :
    Δ / (ρ * accuracyRadius ε ρ ^ 3) =
      (512 : ℝ) ^ (3 / 2 : ℝ) * (Δ * ρ ^ (1 / 2 : ℝ) * ε ^ (-(3 / 2 : ℝ))) := by
  have hpow : accuracyRadius ε ρ ^ 3 = ((ε / 512) / ρ) ^ (3 / 2 : ℝ) := by
    unfold accuracyRadius
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity : 0 ≤ (ε / 512) / ρ)]
    norm_num
  have hr : ρ ^ (3 / 2 : ℝ) = ρ * ρ ^ (1 / 2 : ℝ) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hρ, Real.rpow_one]
  rw [hpow, Real.div_rpow (by positivity) hρ.le, Real.div_rpow hε.le (by norm_num), hr,
    Real.rpow_neg hε.le]
  have hp := (Real.rpow_pos_of_pos hε (3 / 2 : ℝ)).ne'
  have hq := (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 512) (3 / 2 : ℝ)).ne'
  have hr' := (Real.rpow_pos_of_pos hρ (1 / 2 : ℝ)).ne'
  field_simp
  ring

theorem horizonArgument_factorization {ε L ρ : ℝ} (hε : 0 < ε) (hL : 0 < L) (hρ : 0 < ρ) :
    1 / rawMomentum (stepSize L) ρ (accuracyRadius ε ρ) =
      ((512 : ℝ) ^ (1 / 4 : ℝ) / 2) *
        (L ^ (1 / 2 : ℝ) * ρ ^ (-(1 / 4 : ℝ)) * ε ^ (-(1 / 4 : ℝ))) := by
  have hB := accuracyRadius_pos hε hρ
  have hquarter : Real.sqrt (accuracyRadius ε ρ) =
      ε ^ (1 / 4 : ℝ) / ((512 : ℝ) ^ (1 / 4 : ℝ) * ρ ^ (1 / 4 : ℝ)) := by
    unfold accuracyRadius
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
      ← Real.rpow_mul (by positivity : 0 ≤ (ε / 512) / ρ)]
    norm_num only [show (1 / 2 : ℝ) * (1 / 2 : ℝ) = 1 / 4 by norm_num]
    rw [Real.div_rpow (by positivity) hρ.le, Real.div_rpow hε.le (by norm_num)]
    ring
  have hstep : Real.sqrt (stepSize L) = 1 / (2 * L ^ (1 / 2 : ℝ)) := by
    unfold stepSize
    rw [Real.sqrt_div (by norm_num), Real.sqrt_one, Real.sqrt_mul (by norm_num),
      Real.sqrt_eq_rpow L]
    norm_num
  have hr : ρ ^ (1 / 2 : ℝ) = ρ ^ (1 / 4 : ℝ) * ρ ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_add hρ]
    norm_num
  unfold rawMomentum
  rw [Real.sqrt_mul (by positivity : 0 ≤ ρ * accuracyRadius ε ρ), Real.sqrt_mul hρ.le,
    hquarter, hstep, Real.sqrt_eq_rpow, hr, Real.rpow_neg hρ.le, Real.rpow_neg hε.le]
  have hp := (Real.rpow_pos_of_pos hε (1 / 4 : ℝ)).ne'
  have hq := (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 512) (1 / 4 : ℝ)).ne'
  have hr' := (Real.rpow_pos_of_pos hρ (1 / 4 : ℝ)).ne'
  have hL' := (Real.rpow_pos_of_pos hL (1 / 2 : ℝ)).ne'
  field_simp
  ring

theorem continuous_cost_factorization {ε Δ L ρ : ℝ}
    (hε : 0 < ε) (hL : 0 < L) (hρ : 0 < ρ) :
    (2 * (Δ / (ρ * accuracyRadius ε ρ ^ 3))) *
        (1 / rawMomentum (stepSize L) ρ (accuracyRadius ε ρ)) =
      (512 : ℝ) ^ (7 / 4 : ℝ) * Model.rate ε Δ L ρ := by
  rw [restartArgument_factorization hε hρ, horizonArgument_factorization hε hL hρ]
  calc
    _ = ((512 : ℝ) ^ (3 / 2 : ℝ) * (512 : ℝ) ^ (1 / 4 : ℝ)) *
        ((Δ * ρ ^ (1 / 2 : ℝ) * ε ^ (-(3 / 2 : ℝ))) *
          (L ^ (1 / 2 : ℝ) * ρ ^ (-(1 / 4 : ℝ)) * ε ^ (-(1 / 4 : ℝ)))) := by ring
    _ = _ := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 512), rate_factorization ε Δ L ρ hε hρ]
      norm_num only [show (3 / 2 : ℝ) + 1 / 4 = 7 / 4 by norm_num]
      rfl

/-- The actual integer block budget, including one final epoch, has the
target rate. The high-mass hypothesis absorbs its additive epoch cost. -/
theorem configured_query_cost_le {ε Δ L ρ : ℝ}
    (hε : 0 < ε) (hL : 0 < L) (hρ : 0 < ρ)
    (hmass : 1 ≤ Δ * ρ ^ (1 / 2 : ℝ) * ε ^ (-(3 / 2 : ℝ))) :
    ((restartLimit Δ (ρ * accuracyRadius ε ρ ^ 3) *
      epochHorizon (stepSize L) ρ (accuracyRadius ε ρ) : ℕ) : ℝ) ≤
        (512 : ℝ) ^ (7 / 4 : ℝ) * Model.rate ε Δ L ρ := by
  have hB := accuracyRadius_pos hε hρ
  have hδ : 0 < ρ * accuracyRadius ε ρ ^ 3 := by positivity
  have ht := rawMomentum_pos (stepSize_pos hL) hρ hB
  have harg : 1 ≤ Δ / (ρ * accuracyRadius ε ρ ^ 3) := by
    rw [restartArgument_factorization hε hρ]
    have hc : (1 : ℝ) ≤ (512 : ℝ) ^ (3 / 2 : ℝ) :=
      Real.one_le_rpow (by norm_num) (by norm_num)
    nlinarith
  have hM : (restartLimit Δ (ρ * accuracyRadius ε ρ ^ 3) : ℝ) ≤
      2 * (Δ / (ρ * accuracyRadius ε ρ ^ 3)) := by
    have hf := Nat.floor_le (show 0 ≤ Δ / (ρ * accuracyRadius ε ρ ^ 3) by positivity)
    simp only [restartLimit, Nat.cast_add, Nat.cast_one]
    linarith
  have hN : (epochHorizon (stepSize L) ρ (accuracyRadius ε ρ) : ℝ) ≤
      1 / rawMomentum (stepSize L) ρ (accuracyRadius ε ρ) :=
    Nat.floor_le (by positivity)
  rw [Nat.cast_mul, ← continuous_cost_factorization hε hL hρ]
  exact mul_le_mul hM hN (by positivity) (by positivity)

end RandomizedFO2003.Accelerated
