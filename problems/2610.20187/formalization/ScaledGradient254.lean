import AdaptiveGradient254

noncomputable section
namespace Paper254

def gradientRate (D G : ℝ) (T : ℕ) (P : ℝ) : ℝ := G*Real.sqrt ((T : ℝ)*(D^2+D*P))

theorem gradientRate_square (D G P : ℝ) (T : ℕ) (hD : 0 < D) (hG : 0 < G) (hP : 0 ≤ P) :
    (gradientRate D G T P)^2 = G^2*T*(D^2+D*P) := by
  unfold gradientRate
  rw [mul_pow,Real.sq_sqrt (by positivity)]
  ring

theorem scaled_gradient_feasible (D G P : ℝ) (T : ℕ) (hD : 0 < D) (hG : 0 < G)
    (hP : 0 ≤ P) (hPT : P ≤ D*T) (hT : (4 : ℝ) ≤ T) :
    (2*D/G)/T ≤ gradientRate D G T P/(G^2*T) ∧
      gradientRate D G T P/(G^2*T) ≤ 2*D/G := by
  have hT0 : (0 : ℝ) < T := by linarith
  let R := gradientRate D G T P
  have hR : 0 < R := by dsimp [R,gradientRate]; positivity
  have hs : R^2 = G^2*T*(D^2+D*P) := gradientRate_square D G P T hD hG hP
  have hlo : 2*D*G ≤ R := by
    have hh := mul_le_mul_of_nonneg_right hT (show 0 ≤ G^2*D^2 by positivity)
    have hp := mul_nonneg (show 0 ≤ G^2*T*D by positivity) hP
    by_contra hn
    have hprod := mul_pos (sub_pos.mpr (lt_of_not_ge hn)) (show 0 < 2*D*G+R by positivity)
    nlinarith
  have hhi : R ≤ 2*D*G*T := by
    have hh := mul_le_mul_of_nonneg_left hPT (show 0 ≤ G^2*T*D by positivity)
    have ht : (T : ℝ) ≤ (T : ℝ)^2 := by nlinarith
    have hm := mul_le_mul_of_nonneg_left ht (show 0 ≤ G^2*D^2 by positivity)
    by_contra hn
    have hp := mul_pos (sub_pos.mpr (lt_of_not_ge hn)) (show 0 < R+2*D*G*T by positivity)
    nlinarith
  constructor
  · apply (div_le_div_iff₀ hT0 (show 0 < G^2*T by positivity)).mpr
    have hh := mul_le_mul_of_nonneg_right hlo hT0.le
    have he : (2*D/G)*(G^2*T) = 2*D*G*T := by field_simp
    rw [he]
    nlinarith
  · apply (div_le_iff₀ (show 0 < G^2*T by positivity)).mpr
    have he : (2*D/G)*(G^2*T) = 2*D*G*T := by field_simp
    rw [he]
    exact hhi

theorem scaled_gradient_cost (D G P α : ℝ) (T : ℕ) (hD : 0 < D) (hG : 0 < G)
    (hP : 0 ≤ P) (hT : 0 < T)
    (hlo : gradientRate D G T P/(G^2*T) ≤ α)
    (hhi : α ≤ 2*(gradientRate D G T P/(G^2*T))) :
    (D^2+2*D*P)/(2*α)+α*G^2*T/2 ≤ 2*gradientRate D G T P := by
  let R := gradientRate D G T P
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hR : 0 < R := by dsimp [R,gradientRate]; positivity
  have hs : R^2 = G^2*T*(D^2+D*P) := gradientRate_square D G P T hD hG hP
  have hα : 0 < α := lt_of_lt_of_le (div_pos hR (by positivity)) hlo
  have hl := (div_le_iff₀ (show 0 < G^2*T by positivity)).mp hlo
  have hu := (le_div_iff₀ (show 0 < G^2*T by positivity)).mp
    (show α ≤ (2*R)/(G^2*T) by simpa only [mul_div_assoc] using hhi)
  have hpot : (D^2+2*D*P)/(2*α) ≤ R := by
    apply (div_le_iff₀ (show 0 < 2*α by positivity)).mpr
    have hh := mul_le_mul_of_nonneg_right hl hR.le
    have hgoal : (D^2+2*D*P)*(G^2*T) ≤ (R*(2*α))*(G^2*T) := by
      nlinarith [mul_nonneg (show 0 ≤ G^2*T by positivity) (sq_nonneg D)]
    exact (mul_le_mul_iff_left₀ (show 0 < G^2*T by positivity)).mp hgoal
  have hsm : α*G^2*T/2 ≤ R := by nlinarith
  change _ ≤ 2*R
  linarith

end Paper254
#print axioms Paper254.scaled_gradient_cost
