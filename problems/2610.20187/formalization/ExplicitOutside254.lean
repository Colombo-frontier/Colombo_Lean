import OutsideScale254

noncomputable section
namespace Paper254

theorem explicit_outside_bound (D G η : ℝ) (d T : ℕ) (P : ℝ)
    (hD : 0 < D) (hG : 0 < G) (hη : 0 < η) (hT : 0 < T) (hP : 0 ≤ P)
    (hlarge : curvature D G η^2*G^2*T*D^3/(Real.sqrt (d+1 : ℝ)*logFactor T^2) ≤ P) :
    gradientRate D G T P ≤ (d+1 : ℝ)*logFactor T^2/curvature D G η+
      2*explicitCurvedRate (curvature D G η) G d T P := by
  let γ := curvature D G η
  let Λ := logFactor T
  let A := (d+1 : ℝ)*Λ^2/γ
  let B := Real.sqrt (d+1 : ℝ)*Λ^2/γ
  let E := explicitCurvedRate γ G d T P
  have hγ : 0 < γ := curvature_pos D G η hD hG hη
  have hL : 1 ≤ Λ := logFactor_ge_one T hT
  have ha : (1 : ℝ) ≤ d+1 := by have hh : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith
  have hsqrt : 1 ≤ Real.sqrt (d+1 : ℝ) := by
    have hh := Real.sq_sqrt (show (0 : ℝ) ≤ d+1 by positivity)
    have hn := Real.sqrt_nonneg (d+1 : ℝ)
    nlinarith
  have hga : γ*A = (d+1 : ℝ)*Λ^2 := by dsimp [A]; field_simp
  have hgb : γ*B = Real.sqrt (d+1 : ℝ)*Λ^2 := by dsimp [B]; field_simp
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hE : 0 ≤ E := by dsimp [E,explicitCurvedRate]; positivity
  have hAB : 1 ≤ γ*A := by
    rw [hga]
    nlinarith [mul_nonneg (show 0 ≤ (d+1 : ℝ)-1 by linarith) (sq_nonneg Λ)]
  have hBB : 1 ≤ γ*B := by
    rw [hgb]
    nlinarith [mul_nonneg (show 0 ≤ Real.sqrt (d+1 : ℝ)-1 by linarith) (sq_nonneg Λ)]
  have hE3 : E^3 = B^2*γ*G^2*T*P^2 := by
    rw [explicitCurvedRate_cube γ G d T P hγ hG hT hP]
    dsimp [B,Λ]
    simp only [div_pow,mul_pow,Real.sq_sqrt (show (0 : ℝ) ≤ d+1 by positivity)]
    field_simp <;> ring
  have ht : γ*G^2*T*D^3 ≤ B*P := by
    have hh := (div_le_iff₀ (show 0 < Real.sqrt (d+1 : ℝ)*logFactor T^2 by positivity)).mp hlarge
    apply (mul_le_mul_iff_right₀ hγ).mp
    have he : γ*(B*P) = P*(Real.sqrt (d+1 : ℝ)*Λ^2) := by dsimp [B]; field_simp
    rw [he]
    change γ^2*G^2*T*D^3 ≤ P*(Real.sqrt (d+1 : ℝ)*Λ^2) at hh
    nlinarith
  exact outside_scale_comparison A B E γ G D T P (gradientRate D G T P)
    hA hB hE hγ.le hG.le hD.le (Nat.cast_nonneg T) hP
    (by unfold gradientRate; positivity) hAB hBB hE3 ht (gradientRate_square D G P T hD hG hP)

theorem explicit_overhead_absorbed (D G η : ℝ) (d T : ℕ)
    (hD : 0 < D) (hG : 0 < G) (hη : 0 < η) (hT : 0 < T) :
    logFactor T/η ≤ (d+1 : ℝ)*logFactor T^2/curvature D G η := by
  have hγ := curvature_pos D G η hD hG hη
  have hge : curvature D G η ≤ η := by
    have hh : curvature D G η ≤ η/2 := min_le_left _ _
    linarith
  have hL := logFactor_ge_one T hT
  have hh := div_le_div_of_nonneg_left (show 0 ≤ logFactor T by linarith) hγ hge
  have hnum : logFactor T ≤ (d+1 : ℝ)*logFactor T^2 := by
    nlinarith [mul_nonneg (Nat.cast_nonneg d (α := ℝ)) (sq_nonneg (logFactor T))]
  exact hh.trans (div_le_div_of_nonneg_right hnum hγ.le)

end Paper254
#print axioms Paper254.explicit_outside_bound
