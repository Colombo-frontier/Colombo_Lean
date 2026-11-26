import SampleReuse.Model

namespace SampleReuse
noncomputable section

/-- Literal B_g in the manuscript, before logarithmic factors and ceilings. -/
def sourceGradientBudget (P : Parameters) (ε γ : ℝ) : ℝ :=
  1+P.gap*P.gradientLip/ε^2+P.gradientNoise^2/ε^2+
    P.gradientNoise*P.gradientLip*P.gap/ε^3+P.gradientLip^2*P.gap/(ε^2*γ)

/-- Literal B_H in the manuscript, including both curvature contributions. -/
def sourceHessianBudget (P : Parameters) (ε γ : ℝ) : ℝ :=
  1+P.gap*P.gradientLip/ε^2+P.hessianNoise^2/γ^2+
    P.hessianNoise*P.hessianLip*P.gap/(ε*γ^2)+2*P.hessianLip^2*P.gap/γ^3

def sourceGradientConstant (P : Parameters) : ℝ :=
  1+P.gap*P.gradientLip+P.gradientNoise^2+
    P.gradientNoise*P.gradientLip*P.gap+P.gradientLip^2*P.gap

def sourceHessianConstant (P : Parameters) : ℝ :=
  1+P.gap*P.gradientLip+P.hessianNoise^2+
    P.hessianNoise*P.hessianLip*P.gap+2*P.hessianLip^2*P.gap

theorem sourceGradientConstant_pos (P : Parameters) : 0 < sourceGradientConstant P := by
  unfold sourceGradientConstant
  have := P.gap_pos
  have := P.gradientLip_pos
  have := P.gradientNoise_pos
  positivity

theorem sourceHessianConstant_pos (P : Parameters) : 0 < sourceHessianConstant P := by
  unfold sourceHessianConstant
  have := P.gap_pos
  have := P.gradientLip_pos
  have := P.hessianNoise_pos
  have := P.hessianLip_pos
  positivity

theorem mixed_cubic_bound {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : a^2*b ≤ a^3+b^3 := by
  rcases le_total a b with hab|hba
  · have hh := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha hab 2) hb
    nlinarith [pow_nonneg ha 3]
  · have hh := mul_le_mul_of_nonneg_left hba (sq_nonneg a)
    nlinarith [pow_nonneg hb 3]

theorem mixed_inverse_cubic_bound {ε γ : ℝ} (hε : 0 < ε) (hγ : 0 < γ) :
    1/(ε^2*γ) ≤ 1/ε^3+1/γ^3 := by
  have hh := mixed_cubic_bound (inv_nonneg.mpr hε.le) (inv_nonneg.mpr hγ.le)
  simpa only [one_div,mul_inv_rev,inv_pow,mul_comm] using hh

theorem other_mixed_inverse_cubic_bound {ε γ : ℝ} (hε : 0 < ε) (hγ : 0 < γ) :
    1/(ε*γ^2) ≤ 1/ε^3+1/γ^3 := by
  simpa only [mul_comm,add_comm] using mixed_inverse_cubic_bound hγ hε

theorem inverse_square_le_cube {ε : ℝ} (hε : 0 < ε) (he : ε ≤ 1) : 1/ε^2 ≤ 1/ε^3 := by
  apply one_div_le_one_div_of_le (pow_pos hε 3)
  have hh := mul_le_mul_of_nonneg_left he (sq_nonneg ε)
  nlinarith

theorem one_le_inverse_square {ε : ℝ} (hε : 0 < ε) (he : ε ≤ 1) : 1 ≤ 1/ε^2 := by
  apply (le_div_iff₀ (sq_pos_of_pos hε)).mpr
  have hh := pow_le_pow_left₀ hε.le he 2
  simpa using hh

theorem weighted_budget_bound {a b c e x y z w R : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (he : 0 ≤ e)
    (h1 : 1 ≤ R) (hx : x ≤ R) (hy : y ≤ R) (hz : z ≤ R) (hw : w ≤ R) :
    1+a*x+b*y+c*z+e*w ≤ (1+a+b+c+e)*R := by
  nlinarith [mul_le_mul_of_nonneg_left hx ha,mul_le_mul_of_nonneg_left hy hb,
    mul_le_mul_of_nonneg_left hz hc,mul_le_mul_of_nonneg_left hw he]

theorem sourceGradientBudget_rate (P : Parameters) {ε γ : ℝ}
    (hε : 0 < ε) (he : ε ≤ 1) (hγ : 0 < γ) :
    sourceGradientBudget P ε γ ≤ sourceGradientConstant P*(1/ε^3+1/(ε^2*γ)) := by
  have h3 : 0 ≤ 1/ε^3 := by positivity
  have hm : 0 ≤ 1/(ε^2*γ) := by positivity
  have hx : 1/ε^2 ≤ 1/ε^3+1/(ε^2*γ) :=
    (inverse_square_le_cube hε he).trans (le_add_of_nonneg_right hm)
  have hh := weighted_budget_bound (mul_nonneg P.gap_pos.le P.gradientLip_pos.le)
    (sq_nonneg P.gradientNoise)
    (mul_nonneg (mul_nonneg P.gradientNoise_pos.le P.gradientLip_pos.le) P.gap_pos.le)
    (mul_nonneg (sq_nonneg P.gradientLip) P.gap_pos.le)
    ((one_le_inverse_square hε he).trans hx) hx hx (le_add_of_nonneg_right hm)
    (le_add_of_nonneg_left h3)
  simpa only [sourceGradientBudget,sourceGradientConstant,div_eq_mul_inv,one_mul] using hh

theorem sourceHessianBudget_rate (P : Parameters) {ε γ : ℝ}
    (hε : 0 < ε) (he : ε ≤ 1) (hγ : 0 < γ) (hg : γ ≤ 1) :
    sourceHessianBudget P ε γ ≤ sourceHessianConstant P*(1/ε^2+1/(ε*γ^2)+1/γ^3) := by
  have h2 : 0 ≤ 1/ε^2 := by positivity
  have hm : 0 ≤ 1/(ε*γ^2) := by positivity
  have h3 : 0 ≤ 1/γ^3 := by positivity
  have hx : 1/ε^2 ≤ 1/ε^2+1/(ε*γ^2)+1/γ^3 := by linarith
  have hy : 1/γ^2 ≤ 1/ε^2+1/(ε*γ^2)+1/γ^3 := by
    have := inverse_square_le_cube hγ hg
    linarith
  have hh := weighted_budget_bound (mul_nonneg P.gap_pos.le P.gradientLip_pos.le)
    (sq_nonneg P.hessianNoise)
    (mul_nonneg (mul_nonneg P.hessianNoise_pos.le P.hessianLip_pos.le) P.gap_pos.le)
    (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (sq_nonneg P.hessianLip)) P.gap_pos.le)
    ((one_le_inverse_square hε he).trans hx) hx hy (by linarith : 1/(ε*γ^2) ≤ _)
    (by linarith : 1/γ^3 ≤ _)
  simpa only [sourceHessianBudget,sourceHessianConstant,div_eq_mul_inv,one_mul] using hh

theorem sourceBudgets_total_rate (P : Parameters) {ε γ : ℝ}
    (hε : 0 < ε) (he : ε ≤ 1) (hγ : 0 < γ) (hg : γ ≤ 1) :
    sourceGradientBudget P ε γ+sourceHessianBudget P ε γ ≤
      (2*sourceGradientConstant P+3*sourceHessianConstant P)*(1/ε^3+1/γ^3) := by
  have hge := sourceGradientBudget_rate P hε he hγ
  have hHe := sourceHessianBudget_rate P hε he hγ hg
  have hm := mixed_inverse_cubic_bound hε hγ
  have hn := other_mixed_inverse_cubic_bound hε hγ
  have hs := inverse_square_le_cube hε he
  have he3 : 0 ≤ 1/ε^3 := by positivity
  have hg3 : 0 ≤ 1/γ^3 := by positivity
  have hgR : 1/ε^3+1/(ε^2*γ) ≤ 2*(1/ε^3+1/γ^3) := by linarith
  have hHR : 1/ε^2+1/(ε*γ^2)+1/γ^3 ≤ 3*(1/ε^3+1/γ^3) := by linarith
  have hgp := mul_le_mul_of_nonneg_left hgR (sourceGradientConstant_pos P).le
  have hHp := mul_le_mul_of_nonneg_left hHR (sourceHessianConstant_pos P).le
  nlinarith

end
end SampleReuse
