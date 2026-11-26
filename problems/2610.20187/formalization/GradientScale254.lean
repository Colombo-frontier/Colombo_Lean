import ScaleGrid254
import ProjectedGradientOnline254
import LogBudget254

noncomputable section
open scoped BigOperators
namespace Paper254

theorem pathLength_le_diameter {d T : ℕ} {D : ℝ} {W : Domain d D}
    (hD : 0 ≤ D) (u : Fin T → W.carrier) : pathLength u ≤ D*T := by
  calc
    pathLength u ≤ ∑ _t : Fin T, D := by
      apply Finset.sum_le_sum
      intro t _
      split_ifs
      · exact W.diameter _ (u t).property _ (u _).property
      · exact hD
    _ = D*T := by simp; ring

theorem gradient_scale_feasible (D P : ℝ) (hD : 0 < D) (hP : 0 ≤ P)
    (T : ℕ) (hT : 0 < T) (hPT : P ≤ D*T) (hlarge : (1+D)^2 ≤ (T : ℝ)) :
    (1+D)/T ≤ Real.sqrt (T*(1+P))/T ∧ Real.sqrt (T*(1+P))/T ≤ 1+D := by
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hs := Real.sq_sqrt (show 0 ≤ (T : ℝ)*(1+P) by positivity)
  have hr := Real.sqrt_nonneg ((T : ℝ)*(1+P))
  constructor
  · apply (div_le_div_iff_of_pos_right hTr).mpr
    nlinarith [mul_nonneg hTr.le hP]
  · apply (div_le_iff₀ hTr).mpr
    have hpp := mul_le_mul_of_nonneg_left hPT hTr.le
    have ht2 : (T : ℝ) ≤ (T : ℝ)^2 := by nlinarith
    have hprod := mul_nonneg (show 0 ≤ (1+D)^2-(1+D) by nlinarith) (sq_nonneg (T : ℝ))
    have htimes := mul_nonneg (show 0 ≤ (T : ℝ)^2-T by nlinarith) (show 0 ≤ 1+D by positivity)
    nlinarith

theorem gradient_scale_cost (D G P : ℝ) (hD : 0 < D) (hP : 0 ≤ P)
    (T : ℕ) (hT : 0 < T) (α : ℝ)
    (hlo : Real.sqrt (T*(1+P))/T ≤ α) (hhi : α ≤ 2*(Real.sqrt (T*(1+P))/T)) :
    (D^2+2*D*P)/(2*α)+α*G^2*T/2 ≤ (D^2+2*D+G^2)*Real.sqrt (T*(1+P)) := by
  let R := Real.sqrt ((T : ℝ)*(1+P))
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hR : 0 < R := Real.sqrt_pos.2 (by positivity)
  have hs : R^2 = (T : ℝ)*(1+P) := Real.sq_sqrt (by positivity)
  have hα : 0 < α := lt_of_lt_of_le (div_pos hR hTr) hlo
  have hl : R ≤ α*T := (div_le_iff₀ hTr).mp hlo
  have hu : α*T ≤ 2*R := by
    have hh := (le_div_iff₀ hTr).mp (show α ≤ (2*R)/T by simpa only [mul_div_assoc] using hhi)
    exact hh
  have hlin := mul_le_mul_of_nonneg_right hl hR.le
  have hnum : D^2+2*D*P ≤ (D^2+2*D)*(1+P) := by nlinarith [mul_nonneg (sq_nonneg D) hP]
  have hmove : (D^2+2*D*P)/(2*α) ≤ (D^2+2*D)*R := by
    apply (div_le_iff₀ (by positivity : 0 < 2*α)).mpr
    have hh := mul_le_mul_of_nonneg_left hlin (show 0 ≤ D^2+2*D by positivity)
    have haux : (D^2+2*D*P)*T ≤ ((D^2+2*D)*R*(2*α))*T := by nlinarith
    exact (mul_le_mul_iff_left₀ hTr).mp haux
  have hsmooth : α*G^2*T/2 ≤ G^2*R := by
    have hh := mul_le_mul_of_nonneg_right hu (sq_nonneg G)
    nlinarith
  change _ ≤ (D^2+2*D+G^2)*R
  nlinarith

end Paper254
#print axioms Paper254.gradient_scale_cost
