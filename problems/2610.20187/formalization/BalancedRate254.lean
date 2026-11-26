import ScaleBalance254

noncomputable section
namespace Paper254

theorem balanced_curved_term (d T : ℕ) (hd : 0 < d) (hT : 0 < T)
    (γ G P root : ℝ) (hγ : 0 < γ) (hG : 0 < G) (hP : 0 ≤ P) (hroot : 0 ≤ root)
    (hbal : γ^2*G^2*T*root^3 = Real.sqrt (d+1 : ℝ)*logFactor T^2*P) :
    γ*G^2*T*root^2 ≤ (1+2*G^2/γ)*curvedRate d T P := by
  let R := γ*G^2*T*root^2
  let Q := curvedRate d T P
  let c := 1+2*G^2/γ
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hQ : 0 ≤ Q := curvedRate_nonneg d T P hP
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hcube : γ*R^3 = G^2*(d+1 : ℝ)*logFactor T^4*T*P^2 := by
    have hs := congrArg (fun x : ℝ => x^2*(G^2*T)) hbal
    simp only [mul_pow, Real.sq_sqrt (show (0 : ℝ) ≤ d+1 by positivity)] at hs
    convert hs using 1 <;> dsimp [R] <;> ring
  have hQcube : Q^3 = (d : ℝ)*logFactor T^4*T*P^2 := curvedRate_cube d T hT P hP
  have hd' : (d+1 : ℝ) ≤ 2*d := by
    have hh : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hdm := mul_le_mul_of_nonneg_left hd'
    (show 0 ≤ G^2*logFactor T^4*T*P^2 by positivity)
  have hdom : γ*R^3 ≤ 2*G^2*Q^3 := by
    rw [hcube, hQcube]
    nlinarith
  have hx : 0 ≤ 2*G^2/γ := by positivity
  have hpoly : 2*G^2/γ ≤ c^3 := by
    dsimp [c]
    nlinarith [mul_nonneg hx (sq_nonneg (2*G^2/γ))]
  have hcoef : 2*G^2 ≤ γ*c^3 := by
    have hh := (div_le_iff₀ hγ).mp hpoly
    nlinarith
  have hcm := mul_le_mul_of_nonneg_right hcoef (pow_nonneg hQ 3)
  have hs : R^3 ≤ (c*Q)^3 := by
    apply (mul_le_mul_iff_right₀ hγ).mp
    rw [mul_pow]
    nlinarith
  exact nonneg_le_of_cube_le R (c*Q) hR (mul_nonneg hc hQ) hs

theorem floor_smoothing_bound (d T : ℕ) (hd : 0 < d) (hT : 0 < T)
    (γ G D : ℝ) (hγ : 0 < γ) :
    γ*G^2*T*(D/T)^2 ≤ γ*G^2*D^2*((d : ℝ)*logFactor T^2) := by
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hL := logFactor_ge_one T hT
  have hinv : 1/(T : ℝ) ≤ 1 := (div_le_one hTr).mpr hT1
  have hh := mul_le_mul_of_nonneg_left hinv (show 0 ≤ γ*G^2*D^2 by positivity)
  have hstatic : 1 ≤ (d : ℝ)*logFactor T^2 := by
    nlinarith [mul_nonneg (show 0 ≤ (d : ℝ)-1 by linarith) (sq_nonneg (logFactor T))]
  have hm := mul_le_mul_of_nonneg_left hstatic (show 0 ≤ γ*G^2*D^2 by positivity)
  have he : γ*G^2*T*(D/T)^2 = γ*G^2*D^2*(1/T) := by field_simp <;> ring
  rw [he]
  linarith

end Paper254
#print axioms Paper254.balanced_curved_term
#print axioms Paper254.floor_smoothing_bound
