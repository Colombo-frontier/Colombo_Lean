import BalancedRate254

noncomputable section
namespace Paper254

theorem balanced_scale_feasible (d T : ℕ) (hd : 0 < d) (hT : 0 < T)
    (D G γ P : ℝ) (hD : 0 < D) (hG : 0 < G) (hγ : 0 < γ) (hP : 0 ≤ P)
    (hsmall : P ≤ (γ^2*G^2*D^3/2)*T/(Real.sqrt d*logFactor T^2)) :
    let root := (Real.sqrt (d+1 : ℝ)*logFactor T^2*P/(γ^2*G^2*T))^(1/3 : ℝ)
    0 ≤ root ∧ root ≤ D ∧
    γ^2*G^2*T*root^3 = Real.sqrt (d+1 : ℝ)*logFactor T^2*P ∧
    D/T ≤ max (D/T) root ∧ max (D/T) root ≤ D := by
  let X := Real.sqrt (d+1 : ℝ)*logFactor T^2*P/(γ^2*G^2*T)
  let root := X^(1/3 : ℝ)
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hL := logFactor_ge_one T hT
  have hden : 0 < γ^2*G^2*T := by positivity
  have hsd : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.2 hdr
  have hs : Real.sqrt (d+1 : ℝ) ≤ 2*Real.sqrt (d : ℝ) := by
    have h1 := Real.sq_sqrt (show (0 : ℝ) ≤ d+1 by positivity)
    have h2 := Real.sq_sqrt hdr.le
    have h3 := Real.sqrt_nonneg (d+1 : ℝ)
    nlinarith
  have hp := (le_div_iff₀ (show 0 < Real.sqrt (d : ℝ)*logFactor T^2 by positivity)).mp hsmall
  have hsm := mul_le_mul_of_nonneg_right hs (show 0 ≤ logFactor T^2*P by positivity)
  have hX : X ≤ D^3 := by
    apply (div_le_iff₀ hden).mpr
    nlinarith
  have hX0 : 0 ≤ X := by dsimp [X]; positivity
  have hr : 0 ≤ root := Real.rpow_nonneg hX0 _
  have hcube : root^3 = X := third_rpow_cube X hX0
  have hroot : root ≤ D := nonneg_le_of_cube_le root D hr hD.le (by rw [hcube]; exact hX)
  have hbal : γ^2*G^2*T*root^3 = Real.sqrt (d+1 : ℝ)*logFactor T^2*P := by
    rw [hcube]
    dsimp [X]
    field_simp
  have hlo : D/(T : ℝ) ≤ D := by
    apply (div_le_iff₀ hTr).mpr
    have hh : (1 : ℝ) ≤ T := by exact_mod_cast hT
    nlinarith
  exact ⟨hr, hroot, hbal, le_max_left _ _, max_le hlo hroot⟩

end Paper254
