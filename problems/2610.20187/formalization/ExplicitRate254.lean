import BalancedRate254
import ClippedMain254

noncomputable section
namespace Paper254

def explicitCurvedRate (γ G : ℝ) (d T : ℕ) (P : ℝ) : ℝ :=
  γ^(-1/3 : ℝ)*G^(2/3 : ℝ)*(d+1 : ℝ)^(1/3 : ℝ)*logFactor T^(4/3 : ℝ)*
    (T : ℝ)^(1/3 : ℝ)*P^(2/3 : ℝ)

theorem negative_third_cube (γ : ℝ) (hγ : 0 < γ) : (γ^(-1/3 : ℝ))^3 = 1/γ := by
  rw [← Real.rpow_mul_natCast hγ.le]
  norm_num [Real.rpow_neg_one]

theorem explicitCurvedRate_cube (γ G : ℝ) (d T : ℕ) (P : ℝ)
    (hγ : 0 < γ) (hG : 0 < G) (hT : 0 < T) (hP : 0 ≤ P) :
    (explicitCurvedRate γ G d T P)^3 = G^2*(d+1 : ℝ)*logFactor T^4*T*P^2/γ := by
  unfold explicitCurvedRate
  simp only [mul_pow,negative_third_cube γ hγ,two_thirds_rpow_cube G hG.le,
    third_rpow_cube _ (show (0 : ℝ) ≤ d+1 by positivity),
    four_thirds_rpow_cube _ (le_trans (by norm_num) (logFactor_ge_one T hT)),
    third_rpow_cube _ (Nat.cast_nonneg T),two_thirds_rpow_cube P hP]
  ring

theorem balanced_term_exact (γ G root P : ℝ) (d T : ℕ)
    (hγ : 0 < γ) (hG : 0 < G) (hT : 0 < T) (hP : 0 ≤ P) (hr : 0 ≤ root)
    (hbal : γ^2*G^2*T*root^3 = Real.sqrt (d+1 : ℝ)*logFactor T^2*P) :
    γ*G^2*T*root^2 = explicitCurvedRate γ G d T P := by
  let R := γ*G^2*T*root^2
  let Q := explicitCurvedRate γ G d T P
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hL := logFactor_ge_one T hT
  have hQ : 0 ≤ Q := by dsimp [Q,explicitCurvedRate]; positivity
  have hc : γ*R^3 = G^2*(d+1 : ℝ)*logFactor T^4*T*P^2 := by
    have hs := congrArg (fun x : ℝ => x^2*(G^2*T)) hbal
    simp only [mul_pow, Real.sq_sqrt (show (0 : ℝ) ≤ d+1 by positivity)] at hs
    convert hs using 1 <;> dsimp [R] <;> ring
  have hQc := explicitCurvedRate_cube γ G d T P hγ hG hT hP
  change Q^3 = _ at hQc
  have hQc' := (eq_div_iff (ne_of_gt hγ)).mp hQc
  have he : R^3 = Q^3 := by nlinarith
  exact le_antisymm (nonneg_le_of_cube_le R Q hR hQ he.le)
    (nonneg_le_of_cube_le Q R hQ hR he.ge)

theorem explicit_floor_bound (D G γ : ℝ) (d T : ℕ)
    (hD : 0 < D) (hG : 0 < G) (hγ : 0 < γ) (hd : 0 < d) (hT : 0 < T)
    (hcurv : γ*(G*D) ≤ 1/4) :
    γ*G^2*T*(D/T)^2 ≤ (d+1 : ℝ)*logFactor T^2/γ := by
  have hh := floor_smoothing_bound d T hd hT γ G D hγ
  have hc : γ^2*G^2*D^2 ≤ 1/16 := by
    have hn : 0 ≤ γ*(G*D) := by positivity
    nlinarith
  have hm := mul_le_mul_of_nonneg_left hh hγ.le
  have hs := mul_le_mul_of_nonneg_right hc (show 0 ≤ (d : ℝ)*logFactor T^2 by positivity)
  apply (le_div_iff₀ hγ).mpr
  nlinarith [sq_nonneg (logFactor T), mul_nonneg (Nat.cast_nonneg d (α := ℝ)) (sq_nonneg (logFactor T))]

end Paper254
#print axioms Paper254.balanced_term_exact
