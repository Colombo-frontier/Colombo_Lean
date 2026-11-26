import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Tactic

namespace SecondOrder

def gatePoly (t : ℝ) : ℝ := 35*t^4 - 84*t^5 + 70*t^6 - 20*t^7
def gateD1 (t : ℝ) : ℝ := 140*t^3*(1-t)^3
def gateD2 (t : ℝ) : ℝ := 420*t^2*(1-t)^2*(1-2*t)
def gateD3 (t : ℝ) : ℝ := 840*t*(1-t)*(1-5*t+5*t^2)
noncomputable def gate (t : ℝ) : ℝ := if t ≤ 0 then 0 else if 1 ≤ t then 1 else gatePoly t

theorem gatePoly_hasDerivAt (t : ℝ) : HasDerivAt gatePoly (gateD1 t) t := by
  convert ((((hasDerivAt_id t).pow 4).const_mul 35).sub
    (((hasDerivAt_id t).pow 5).const_mul 84) |>.add
    (((hasDerivAt_id t).pow 6).const_mul 70) |>.sub
    (((hasDerivAt_id t).pow 7).const_mul 20)) using 1 <;>
    simp only [gatePoly, gateD1, id_eq] <;> ring

theorem gateD1_hasDerivAt (t : ℝ) : HasDerivAt gateD1 (gateD2 t) t := by
  convert ((((hasDerivAt_id t).pow 3).const_mul 140).mul
    (((hasDerivAt_id t).const_sub 1).pow 3)) using 1 <;>
    simp only [gateD1, gateD2, id_eq] <;> ring

theorem gateD2_hasDerivAt (t : ℝ) : HasDerivAt gateD2 (gateD3 t) t := by
  convert (((((hasDerivAt_id t).pow 2).const_mul 420).mul
    (((hasDerivAt_id t).const_sub 1).pow 2)).mul
    (((hasDerivAt_id t).const_mul 2).const_sub 1)) using 1 <;>
    simp only [gateD2, gateD3, id_eq] <;> ring

theorem gate_endpoints : gatePoly 0 = 0 ∧ gatePoly 1 = 1 ∧ gatePoly (1/2) = 1/2 ∧
    gateD1 0 = 0 ∧ gateD1 1 = 0 ∧ gateD2 0 = 0 ∧ gateD2 1 = 0 ∧
    gateD3 0 = 0 ∧ gateD3 1 = 0 := by
  norm_num [gatePoly, gateD1, gateD2, gateD3]

theorem gatePoly_lower {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : t^4 ≤ gatePoly t := by
  have hq : 0 ≤ 10*t^2-25*t+17 := by nlinarith [sq_nonneg (t-5/4)]
  have h := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2)
    (pow_nonneg ht0 4)) (sub_nonneg.mpr ht1)) hq
  nlinarith [show gatePoly t - t^4 = 2*t^4*(1-t)*(10*t^2-25*t+17) by
    unfold gatePoly; ring]

theorem gatePoly_complement_lower {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1-t)^4 ≤ 1-gatePoly t := by
  have hq : 0 ≤ 10*t^2+5*t+2 := by positivity
  have h := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2)
    ht0) (pow_nonneg (sub_nonneg.mpr ht1) 4)) hq
  nlinarith [show 1-gatePoly t-(1-t)^4 = 2*t*(1-t)^4*(10*t^2+5*t+2) by
    unfold gatePoly; ring]

theorem gatePoly_mem_Icc {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ gatePoly t ∧ gatePoly t ≤ 1 := by
  have := gatePoly_lower ht0 ht1
  have := gatePoly_complement_lower ht0 ht1
  constructor <;> nlinarith [pow_nonneg ht0 4, pow_nonneg (sub_nonneg.mpr ht1) 4]

theorem gate_mem_Icc (t : ℝ) : 0 ≤ gate t ∧ gate t ≤ 1 := by
  unfold gate
  split_ifs with h0 h1
  · norm_num
  · norm_num
  · exact gatePoly_mem_Icc (le_of_lt (lt_of_not_ge h0)) (le_of_lt (lt_of_not_ge h1))

theorem gate_fisher_polynomial {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (gateD1 t)^2 ≤ 1225 * gatePoly t * (1-gatePoly t) := by
  have ht : 0 ≤ t*(1-t) := mul_nonneg ht0 (sub_nonneg.mpr ht1)
  have hquarter : t*(1-t) ≤ 1/4 := by nlinarith [sq_nonneg (t-1/2)]
  have hs : 19600*(t*(1-t))^2 ≤ 1225 := by nlinarith [sq_nonneg (t*(1-t)-1/4)]
  have hbase : 0 ≤ t^4*(1-t)^4 := by positivity
  have hprod : t^4*(1-t)^4 ≤ gatePoly t*(1-gatePoly t) :=
    mul_le_mul (gatePoly_lower ht0 ht1) (gatePoly_complement_lower ht0 ht1)
      (by positivity) (gatePoly_mem_Icc ht0 ht1).1
  calc
    (gateD1 t)^2 = (19600*(t*(1-t))^2)*(t^4*(1-t)^4) := by unfold gateD1; ring
    _ ≤ 1225*(t^4*(1-t)^4) := mul_le_mul_of_nonneg_right hs hbase
    _ ≤ 1225*(gatePoly t*(1-gatePoly t)) := mul_le_mul_of_nonneg_left hprod (by norm_num)
    _ = _ := by ring

theorem gate_derivatives_nonnegative {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1/2) :
    0 ≤ gateD1 t ∧ 0 ≤ gateD2 t := by
  have h1 : 0 ≤ 1-t := by linarith
  have h2 : 0 ≤ 1-2*t := by linarith
  constructor <;> simp only [gateD1, gateD2] <;> positivity

end SecondOrder
