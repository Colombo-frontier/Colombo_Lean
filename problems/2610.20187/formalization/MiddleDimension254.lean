import EffectiveRoot254
import Mathlib.Algebra.Order.Floor.Ring

noncomputable section
namespace Paper254
set_option maxHeartbeats 2000000

theorem middle_dimension_choice (d T : ℕ) (hd : 0 < d) (hT : 0 < T)
    (horizon : 4096*(d : ℝ)^2 ≤ T) (P : ℝ)
    (hlarge : (T : ℝ)/(8*(d : ℝ)^2) < P) (hsmall : P ≤ T/1024) :
    ∃ m : ℕ, 0 < m ∧ m ≤ d ∧ 4*m/Real.sqrt T ≤ P ∧ P ≤ T/(8*(m : ℝ)^2) ∧
      Real.sqrt (T*P)/4 ≤ unloggedRate m T P := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hd2 := sq_pos_of_pos hd0
  have hl := (div_lt_iff₀ (show 0 < 8*(d : ℝ)^2 by positivity)).mp hlarge
  have hP1 : 1 ≤ P := by
    by_contra hh
    have hm := mul_lt_mul_of_pos_right (lt_of_not_ge hh) (show 0 < 8*(d : ℝ)^2 by positivity)
    nlinarith only [hm,horizon,hl,hd2]
  have hP0 : 0 < P := by linarith
  let x := Real.sqrt ((T : ℝ)/P)/16
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hx2 : 256*P*x^2 = T := by
    dsimp [x]
    rw [div_pow,Real.sq_sqrt (by positivity)]
    field_simp
    ring
  have hlow : 2 ≤ x := by
    have hs := (le_div_iff₀ (by norm_num : (0 : ℝ) < 1024)).mp hsmall
    have hsq : 4 ≤ x^2 := by
      apply (mul_le_mul_iff_left₀ (show 0 < 256*P by positivity)).mp
      nlinarith
    nlinarith
  let m := ⌊x⌋₊
  have hmlo : x/2 ≤ (m : ℝ) := by have hh := Nat.lt_floor_add_one x; linarith
  have hmhi : (m : ℝ) ≤ x := Nat.floor_le hx0
  have hm0 : (0 : ℝ) < m := by linarith
  have hm : 0 < m := by exact_mod_cast hm0
  have hlower : (T : ℝ) ≤ 1024*P*(m : ℝ)^2 := by
    have hs : x^2 ≤ 4*(m : ℝ)^2 := by nlinarith
    have hh := mul_le_mul_of_nonneg_left hs (show 0 ≤ 256*P by positivity)
    nlinarith
  have hupper : 256*P*(m : ℝ)^2 ≤ T := by
    have hs : (m : ℝ)^2 ≤ x^2 := by nlinarith
    have hh := mul_le_mul_of_nonneg_left hs (show 0 ≤ 256*P by positivity)
    nlinarith
  have hmd : m ≤ d := by
    have hs : x^2 < (d : ℝ)^2 := by
      apply (mul_lt_mul_iff_left₀ (show 0 < 256*P by positivity)).mp
      nlinarith [mul_pos hP0 hd2]
    have hh : (m : ℝ) < d := by nlinarith
    exact_mod_cast hh.le
  have hhi : P ≤ T/(8*(m : ℝ)^2) := by
    apply (le_div_iff₀ (show 0 < 8*(m : ℝ)^2 by positivity)).mpr
    nlinarith [mul_nonneg hP0.le (sq_nonneg (m : ℝ))]
  have hlo : 4*m/Real.sqrt T ≤ P := by
    apply (div_le_iff₀ (Real.sqrt_pos.2 hT0)).mpr
    have hsqrt := Real.sq_sqrt hT0.le
    have hs : 16*(m : ℝ)^2 ≤ T := by
      nlinarith [mul_nonneg (show 0 ≤ P-1 by linarith) (sq_nonneg (m : ℝ))]
    have ht := mul_nonneg hT0.le (show 0 ≤ P^2-1 by nlinarith only [hP1])
    have hnon : 0 ≤ P*Real.sqrt T := by positivity
    by_contra hh
    have hp := mul_pos (sub_pos.mpr (lt_of_not_ge hh))
      (show 0 < 4*(m : ℝ)+P*Real.sqrt T by positivity)
    have hsq : (P*Real.sqrt T)^2 = P^2*T := by rw [mul_pow,hsqrt]
    nlinarith only [hp,hsq,hs,ht]
  let R := Real.sqrt ((T : ℝ)*P)
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  have hR2 : R^2 = (T : ℝ)*P := Real.sq_sqrt (by positivity)
  have hRbound : R ≤ 32*(m : ℝ)*P := by
    have hh := mul_le_mul_of_nonneg_right hlower hP0.le
    by_contra hnot
    have hp := mul_pos (sub_pos.mpr (lt_of_not_ge hnot))
      (show 0 < R+32*(m : ℝ)*P by positivity)
    nlinarith only [hh,hR2,hp]
  have hrate : R/4 ≤ unloggedRate m T P := by
    have hc := unloggedRate_cube m T P hP0.le
    have hh := mul_le_mul_of_nonneg_right hRbound (sq_nonneg R)
    have he := congrArg (fun z : ℝ => (m : ℝ)*P*z) hR2
    have hcube : (R/4)^3 ≤ (unloggedRate m T P)^3 := by nlinarith [pow_nonneg hR 3]
    exact nonneg_le_of_cube_le _ _ (by positivity) (unloggedRate_nonneg m T P hP0.le) hcube
  exact ⟨m,hm,hmd,hlo,hhi,hrate⟩

end Paper254
#print axioms Paper254.middle_dimension_choice
