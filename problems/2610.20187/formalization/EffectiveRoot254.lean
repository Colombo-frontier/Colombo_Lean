import ScaleBalance254

noncomputable section
namespace Paper254

def unloggedRate (m T : ℕ) (P : ℝ) : ℝ :=
  (m : ℝ)^(1/3 : ℝ)*(T : ℝ)^(1/3 : ℝ)*P^(2/3 : ℝ)

theorem unloggedRate_nonneg (m T : ℕ) (P : ℝ) (hP : 0 ≤ P) : 0 ≤ unloggedRate m T P := by
  unfold unloggedRate
  positivity

theorem unloggedRate_cube (m T : ℕ) (P : ℝ) (hP : 0 ≤ P) :
    (unloggedRate m T P)^3 = (m : ℝ)*T*P^2 := by
  unfold unloggedRate
  simp only [mul_pow,third_rpow_cube _ (Nat.cast_nonneg _),two_thirds_rpow_cube _ hP]

theorem effective_root_conditions (m T : ℕ) (hm : 0 < m) (hT : 0 < T)
    (P : ℝ) (hP : 0 ≤ P) (hlo : 4*m/Real.sqrt T ≤ P) (hhi : P ≤ T/(8*(m : ℝ)^2)) :
    let r := ((T : ℝ)*P^2/(m : ℝ)^2)^(1/3 : ℝ)
    2 ≤ r ∧ r*(m : ℝ)^2 ≤ T/4 ∧ r^3*(m : ℝ)^2 = T*P^2 ∧
      unloggedRate m T P = (m : ℝ)*r := by
  let r := ((T : ℝ)*P^2/(m : ℝ)^2)^(1/3 : ℝ)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hm2 : 0 < (m : ℝ)^2 := sq_pos_of_pos hm0
  have hr0 : 0 ≤ r := Real.rpow_nonneg (by positivity) _
  have hr3 : r^3 = (T : ℝ)*P^2/(m : ℝ)^2 := third_rpow_cube _ (by positivity)
  have hbal : r^3*(m : ℝ)^2 = T*P^2 := by rw [hr3]; field_simp
  have hlow : 2 ≤ r := by
    have hsqrt := Real.sq_sqrt hT0.le
    have hh := (div_le_iff₀ (Real.sqrt_pos.2 hT0)).mp hlo
    have hsq : (4*(m : ℝ))^2 ≤ (P*Real.sqrt T)^2 := by
      nlinarith [mul_nonneg (show 0 ≤ P*Real.sqrt T-4*m by linarith)
        (show 0 ≤ P*Real.sqrt T+4*m by positivity)]
    simp only [mul_pow,hsqrt] at hsq
    have hc : (2 : ℝ)^3 ≤ r^3 := by
      apply (mul_le_mul_iff_left₀ hm2).mp
      nlinarith
    exact nonneg_le_of_cube_le 2 r (by norm_num) hr0 hc
  have hbudget : r*(m : ℝ)^2 ≤ T/4 := by
    have hh := (le_div_iff₀ (show 0 < 8*(m : ℝ)^2 by positivity)).mp hhi
    have hsq : (8*(m : ℝ)^2*P)^2 ≤ (T : ℝ)^2 := by
      nlinarith [mul_nonneg (show 0 ≤ (T : ℝ)-8*(m : ℝ)^2*P by linarith)
        (show 0 ≤ (T : ℝ)+8*(m : ℝ)^2*P by positivity)]
    have htimes := mul_le_mul_of_nonneg_right hsq hT0.le
    have he := congrArg (fun x : ℝ => x*(m : ℝ)^4) hbal
    have hc : (r*(m : ℝ)^2)^3 ≤ ((T : ℝ)/4)^3 := by nlinarith
    exact nonneg_le_of_cube_le _ _ (by positivity) (by positivity) hc
  have heq : unloggedRate m T P = (m : ℝ)*r := by
    have hc := unloggedRate_cube m T P hP
    have he := congrArg (fun x : ℝ => (m : ℝ)*x) hbal
    have hcube : (unloggedRate m T P)^3 = ((m : ℝ)*r)^3 := by nlinarith
    apply le_antisymm
    · exact nonneg_le_of_cube_le _ _ (unloggedRate_nonneg m T P hP) (by positivity) hcube.le
    · exact nonneg_le_of_cube_le _ _ (by positivity) (unloggedRate_nonneg m T P hP) hcube.ge
  exact ⟨hlow,hbudget,hbal,heq⟩

end Paper254
#print axioms Paper254.effective_root_conditions
