import SecondOrder.OjaPopulationRayleigh

open scoped InnerProductSpace

namespace SecondOrder
noncomputable section

/-- Taking a square number of iterations avoids a rounded square root in
the actual step size and in the probability calculation. -/
def ojaScale (d : ℕ) (ε : ℝ) : ℕ := ⌈80*(1+Real.log (4*(d:ℝ)))/ε⌉₊

def ojaIterationCount (d : ℕ) (ε : ℝ) : ℕ := ojaScale d ε ^ 2

def ojaLearningRate (d : ℕ) (ε : ℝ) : ℝ := 1/(20*(ojaScale d ε : ℝ))

theorem oja_square_scale_moment {t ℓ : ℝ} (ht : 0 < t) (hℓ : ℓ ≤ 1) :
    (1/(20*t))^2 * ℓ * t^2 ≤ (1/2:ℝ)/100 := by
  have he : (1/(20*t))^2 * ℓ * t^2 = ℓ/400 := by field_simp; ring
  rw [he]
  linarith

theorem oja_square_scale_probability {t : ℝ} (ht : 0 < t) :
    (1:ℝ)/48 ≤ (1-(1/2:ℝ))/12 - t^2/(8*t)^2 := by
  have he : t^2/(8*t)^2 = (1:ℝ)/64 := by field_simp; ring
  rw [he]
  norm_num

theorem oja_square_scale_regret {t L G : ℝ} (ht : 1 ≤ t) (hL : 0 ≤ L)
    (h : 2*(1/(20*t))*G ≤ 3*(1/(20*t))^2*t^2 + L +
      (2*(1/(20*t))+(1/(20*t))^2)*(8*t)) :
    G ≤ 20*(1+L)*t := by
  have ht0 : 0 < t := by linarith
  have hm := mul_le_mul_of_nonneg_left h (show 0 ≤ 10*t by positivity)
  have hleft : (10*t)*(2*(1/(20*t))*G) = G := by field_simp; ring
  have hright : (10*t)*(3*(1/(20*t))^2*t^2 + L +
      (2*(1/(20*t))+(1/(20*t))^2)*(8*t)) = (10*L+323/40)*t + 1/5 := by
    field_simp
    ring
  rw [hleft,hright] at hm
  have hLt : 0 ≤ L*t := mul_nonneg hL ht0.le
  nlinarith

theorem oja_log_dimension_nonneg {d : ℕ} (hd : 0 < d) : 0 ≤ Real.log (4*(d:ℝ)) := by
  apply Real.log_nonneg
  have hd1 : (1:ℝ) ≤ d := by exact_mod_cast hd
  linarith

theorem ojaScale_lower (d : ℕ) {ε : ℝ} (hε : 0 < ε) :
    80*(1+Real.log (4*(d:ℝ))) ≤ ε*(ojaScale d ε : ℝ) := by
  have hc := Nat.le_ceil (80*(1+Real.log (4*(d:ℝ)))/ε)
  have hm := (div_le_iff₀ hε).mp hc
  simpa only [ojaScale, mul_comm] using hm

theorem ojaScale_pos {d : ℕ} (hd : 0 < d) {ε : ℝ} (hε : 0 < ε) : 0 < ojaScale d ε := by
  have hL := oja_log_dimension_nonneg hd
  have hl := ojaScale_lower d hε
  have ht : (0:ℝ) < ojaScale d ε := by nlinarith
  exact Nat.cast_pos.mp ht

theorem ojaLearningRate_pos {d : ℕ} (hd : 0 < d) {ε : ℝ} (hε : 0 < ε) :
    0 < ojaLearningRate d ε := by
  have ht : (0:ℝ) < ojaScale d ε := Nat.cast_pos.mpr (ojaScale_pos hd hε)
  unfold ojaLearningRate
  positivity

theorem ojaLearningRate_le_one {d : ℕ} (hd : 0 < d) {ε : ℝ} (hε : 0 < ε) :
    ojaLearningRate d ε ≤ 1 := by
  have ht : (1:ℝ) ≤ ojaScale d ε := by exact_mod_cast ojaScale_pos hd hε
  unfold ojaLearningRate
  apply (div_le_iff₀ (by positivity : 0 < 20*(ojaScale d ε : ℝ))).mpr
  linarith

theorem ojaIterationCount_pos {d : ℕ} (hd : 0 < d) {ε : ℝ} (hε : 0 < ε) :
    0 < ojaIterationCount d ε := pow_pos (ojaScale_pos hd hε) 2

/-- The iteration count has inverse-square tolerance dependence and a
squared logarithmic dimension factor. This counts only the Oja run. -/
theorem ojaIterationCount_bound {d : ℕ} (hd : 0 < d) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (ojaIterationCount d ε : ℝ) ≤ 6561*(1+Real.log (4*(d:ℝ)))^2/ε^2 := by
  let D : ℝ := 1+Real.log (4*(d:ℝ))
  have hD : 1 ≤ D := by dsimp [D]; linarith [oja_log_dimension_nonneg hd]
  have hq : 0 ≤ 80*D/ε := by positivity
  have ht : (ojaScale d ε : ℝ) ≤ 80*D/ε+1 := by
    exact (Nat.ceil_lt_add_one hq).le
  have htarget : (ojaScale d ε : ℝ) ≤ 81*D/ε := by
    have he : 80*D/ε+1 ≤ 81*D/ε := by
      apply (le_div_iff₀ hε).mpr
      have hx : (80*D/ε+1)*ε = 80*D+ε := by field_simp
      rw [hx]
      linarith
    exact ht.trans he
  have hs := pow_le_pow_left₀ (Nat.cast_nonneg _) htarget 2
  norm_num [div_pow,mul_pow] at hs
  simpa only [ojaIterationCount,Nat.cast_pow,D] using hs

end
end SecondOrder
