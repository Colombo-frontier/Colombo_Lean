import HeavyTail.ConfidenceAmplitude

/-! Explicit two-sided constants for the manuscript's J_p(exp(-z)) inverse
moment asymptotics, proved from the actual Bernoulli centered moment factor. -/
noncomputable section
namespace HeavyTail

theorem erasureMomentFactor_exp_pos (p : ℝ) {z : ℝ} (hz : 0 < z) :
    0 < erasureMomentFactor p (Real.exp (-z)) := by
  have hu : Real.exp (-z) < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hz)
  unfold erasureMomentFactor
  exact add_pos_of_pos_of_nonneg (Real.exp_pos _)
    (div_nonneg (Real.rpow_nonneg (Real.exp_pos _).le _) (Real.rpow_nonneg (sub_nonneg.mpr hu.le) _))

theorem erasureMomentFactor_small_two_sided {p z : ℝ}
    (hp : 1 < p) (hp2 : p ≤ 2) (hz : 0 < z) (hz1 : z ≤ 1) :
    Real.exp (-2) / z ^ (p - 1) ≤ erasureMomentFactor p (Real.exp (-z)) ∧
    erasureMomentFactor p (Real.exp (-z)) ≤ 2 / z ^ (p - 1) := by
  refine ⟨?_, erasureMomentFactor_exp_bound hp hp2 hz⟩
  have hu1 : Real.exp (-z) < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hz)
  have hnum : Real.exp (-2) ≤ (Real.exp (-z)) ^ p := by
    rw [← Real.exp_mul]
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_right hz1 (by linarith only [hp] : 0 ≤ p)
    nlinarith only [hh, hp2]
  have hden : 1 - Real.exp (-z) ≤ z := by
    linarith only [Real.add_one_le_exp (-z)]
  have hpow : (1 - Real.exp (-z)) ^ (p - 1) ≤ z ^ (p - 1) :=
    Real.rpow_le_rpow (sub_nonneg.mpr hu1.le) hden (by linarith only [hp])
  have hpos : 0 < (1 - Real.exp (-z)) ^ (p - 1) :=
    Real.rpow_pos_of_pos (sub_pos.mpr hu1) _
  calc
    _ ≤ (Real.exp (-z)) ^ p / (1 - Real.exp (-z)) ^ (p - 1) :=
      div_le_div₀ (Real.rpow_nonneg (Real.exp_pos _).le _) hnum hpos hpow
    _ ≤ _ := le_add_of_nonneg_left (Real.exp_pos _).le

theorem erasureMomentFactor_large_two_sided {p z : ℝ}
    (hp : 1 ≤ p) (hz : 1 ≤ z) :
    Real.exp (-z) ≤ erasureMomentFactor p (Real.exp (-z)) ∧
    erasureMomentFactor p (Real.exp (-z)) ≤ 2 * Real.exp (-z) := by
  have hz0 : 0 < z := lt_of_lt_of_le zero_lt_one hz
  have hu1 : Real.exp (-z) < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hz0)
  have hodds : Real.exp (-z) / (1 - Real.exp (-z)) ≤ 1 :=
    (exp_neg_erasure_odds hz0).trans ((div_le_one hz0).mpr hz)
  have hodds0 : 0 ≤ Real.exp (-z) / (1 - Real.exp (-z)) :=
    div_nonneg (Real.exp_pos _).le (sub_nonneg.mpr hu1.le)
  have hpow : (Real.exp (-z) / (1 - Real.exp (-z))) ^ (p - 1) ≤ 1 :=
    Real.rpow_le_one hodds0 hodds (sub_nonneg.mpr hp)
  rw [erasureMomentFactor_factor (Real.exp_pos _) hu1]
  constructor
  · exact le_add_of_nonneg_right (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hodds0 _))
  · have hm := mul_le_mul_of_nonneg_left hpow (Real.exp_pos (-z)).le
    linarith only [hm]

theorem inverse_moment_power_identity {A p z : ℝ} (hA : 0 ≤ A) (hp : 0 < p) (hz : 0 < z) :
    (A / z ^ (p - 1)) ^ (-1 / p) = A ^ (-1 / p) * z ^ (1 - 1 / p) := by
  rw [Real.div_rpow hA (Real.rpow_nonneg hz.le _), ← Real.rpow_mul hz.le]
  have he : (p - 1) * (-1 / p) = -(1 - 1 / p) := by field_simp
  rw [he, Real.rpow_neg hz.le, div_eq_mul_inv, inv_inv]

def erasureInverseMoment (p z : ℝ) : ℝ := (erasureMomentFactor p (Real.exp (-z))) ^ (-1 / p)

/-- Explicit version of J_p(exp(-z))^(-1/p) asymp_p z^(1-1/p)
for 0<z≤1, with constants 2^(-1/p) and exp(2/p). -/
theorem erasureInverseMoment_small_two_sided {p z : ℝ}
    (hp : 1 < p) (hp2 : p ≤ 2) (hz : 0 < z) (hz1 : z ≤ 1) :
    (2 : ℝ) ^ (-1 / p) * z ^ (1 - 1 / p) ≤ erasureInverseMoment p z ∧
    erasureInverseMoment p z ≤ Real.exp (2 / p) * z ^ (1 - 1 / p) := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hr : -1 / p ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by norm_num) hp0.le
  obtain ⟨hl, hu⟩ := erasureMomentFactor_small_two_sided hp hp2 hz hz1
  constructor
  · have hh := Real.rpow_le_rpow_of_nonpos (erasureMomentFactor_exp_pos p hz) hu hr
    rw [inverse_moment_power_identity (by norm_num) hp0 hz] at hh
    exact hh
  · have hh := Real.rpow_le_rpow_of_nonpos
      (div_pos (Real.exp_pos (-2)) (Real.rpow_pos_of_pos hz _)) hl hr
    rw [inverse_moment_power_identity (Real.exp_pos _).le hp0 hz, ← Real.exp_mul] at hh
    have he : (-2 : ℝ) * (-1 / p) = 2 / p := by ring
    rw [he] at hh
    exact hh

/-- Explicit version of J_p(exp(-z))^(-1/p) asymp_p exp(z/p)
for z≥1, with constants 2^(-1/p) and 1. -/
theorem erasureInverseMoment_large_two_sided {p z : ℝ}
    (hp : 1 < p) (hz : 1 ≤ z) :
    (2 : ℝ) ^ (-1 / p) * Real.exp (z / p) ≤ erasureInverseMoment p z ∧
    erasureInverseMoment p z ≤ Real.exp (z / p) := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hz0 : 0 < z := lt_of_lt_of_le zero_lt_one hz
  have hr : -1 / p ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by norm_num) hp0.le
  obtain ⟨hl, hu⟩ := erasureMomentFactor_large_two_sided hp.le hz
  have he : (-z) * (-1 / p) = z / p := by ring
  constructor
  · have hh := Real.rpow_le_rpow_of_nonpos (erasureMomentFactor_exp_pos p hz0) hu hr
    rw [Real.mul_rpow (by norm_num) (Real.exp_pos _).le, ← Real.exp_mul, he] at hh
    exact hh
  · have hh := Real.rpow_le_rpow_of_nonpos (Real.exp_pos (-z)) hl hr
    rw [← Real.exp_mul, he] at hh
    exact hh

end HeavyTail
