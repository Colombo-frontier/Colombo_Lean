import CurvedMain254

noncomputable section
namespace Paper254

theorem cube_ratio_bound (x y c : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hc : 0 < c)
    (h : c^2*x^3 ≤ y^3) : x ≤ (1+1/c^2)*y := by
  let k := 1+1/c^2
  have hk : 1 ≤ k := by
    dsimp [k]
    have hh : 0 ≤ 1/c^2 := by positivity
    linarith
  have hck : c^2*k ≥ 1 := by dsimp [k]; field_simp; nlinarith [sq_nonneg c]
  have hk3 : k ≤ k^3 := by nlinarith [mul_nonneg (show 0 ≤ k-1 by linarith) (sq_nonneg k)]
  have hc3 : 1 ≤ c^2*k^3 := le_trans hck (mul_le_mul_of_nonneg_left hk3 (sq_nonneg c))
  have hp := mul_le_mul_of_nonneg_right hc3 (pow_nonneg hy 3)
  have hs : x^3 ≤ (k*y)^3 := by
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hc)).mp
    rw [mul_pow]
    nlinarith
  exact nonneg_le_of_cube_le x (k*y) hx (by positivity) hs

theorem large_path_linear_bound (d T : ℕ) (hd : 0 < d) (hT : 0 < T)
    (P c : ℝ) (hP : 0 ≤ P) (hc : 0 < c)
    (hlarge : c*T/(Real.sqrt d*logFactor T^2) ≤ P) :
    (T : ℝ) ≤ (1+1/c^2)*curvedRate d T P := by
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have hL := logFactor_ge_one T hT
  have hh := (div_le_iff₀ (show 0 < Real.sqrt (d : ℝ)*logFactor T^2 by positivity)).mp hlarge
  have hs : (c*(T : ℝ))^2 ≤ (P*(Real.sqrt (d : ℝ)*logFactor T^2))^2 := by
    nlinarith [mul_nonneg (show 0 ≤ P*(Real.sqrt (d : ℝ)*logFactor T^2)-c*T by linarith)
      (show 0 ≤ P*(Real.sqrt (d : ℝ)*logFactor T^2)+c*T by positivity)]
  simp only [mul_pow, Real.sq_sqrt hdr.le] at hs
  have hm := mul_le_mul_of_nonneg_right hs (Nat.cast_nonneg T (α := ℝ))
  have hcube : c^2*(T : ℝ)^3 ≤ (curvedRate d T P)^3 := by
    rw [curvedRate_cube d T hT P hP]
    nlinarith
  exact cube_ratio_bound T (curvedRate d T P) c (Nat.cast_nonneg T) (curvedRate_nonneg d T P hP) hc hcube

theorem global_curved_learner (D G η : ℝ) (hD : 0 < D) (hG : 0 < G) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ d T : ℕ, 0 < d → 0 < T → ∀ W : Domain d D,
    ∃ A : OnlineLearner W T, ∀ f : Fin T → Loss d,
    (∀ t, AdmissibleLoss W G η (f t)) → ∀ u : Fin T → W.carrier,
    regret A f u ≤ C*((d : ℝ)*logFactor T^2+curvedRate d T (pathLength u)) := by
  obtain ⟨C,c,hC,hc,hmain⟩ := main_curved D G η hD hG hη
  let K := G*D*(1+1/c^2)
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨C+K, by positivity, ?_⟩
  intro d T hd hT W
  obtain ⟨A,hA⟩ := hmain d T hd hT W
  refine ⟨A,?_⟩
  intro f hf u
  have hQ := curvedRate_nonneg d T (pathLength u) (pathLength_nonneg u)
  have hS : 0 ≤ (d : ℝ)*logFactor T^2 := by positivity
  by_cases hs : pathLength u ≤ c*T/(Real.sqrt d*logFactor T^2)
  · have hh := hA f hf u hs
    nlinarith [mul_nonneg hK.le (add_nonneg hS hQ)]
  · have hl := large_path_linear_bound d T hd hT (pathLength u) c (pathLength_nonneg u) hc (le_of_not_ge hs)
    have hb := linear_regret_bound A f u hG.le hf
    have hm := mul_le_mul_of_nonneg_left hl (mul_nonneg hG.le hD.le)
    have hm' : G*D*T ≤ K*curvedRate d T (pathLength u) := by convert hm using 1 <;> dsimp [K] <;> ring
    nlinarith [mul_nonneg hC.le (add_nonneg hS hQ), mul_nonneg hK.le hS]

end Paper254
#print axioms Paper254.global_curved_learner
