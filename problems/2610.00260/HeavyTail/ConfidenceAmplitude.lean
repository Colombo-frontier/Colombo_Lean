import HeavyTail.Envelope
import HeavyTail.Erasure
import Mathlib.Analysis.SpecialFunctions.Exp

/-! Quantitative erasure parameters, derived from exponential inequalities.
These close the moment/amplitude calculations in the confidence lower bound;
they do not assume that an adaptive testing bound implies a minimax bound. -/
noncomputable section
namespace HeavyTail

def erasureMomentFactor (p u : ℝ) : ℝ := u + u ^ p / (1 - u) ^ (p - 1)

theorem erasureMomentFactor_nonneg {p u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1) :
    0 ≤ erasureMomentFactor p u := by
  exact add_nonneg hu (div_nonneg (Real.rpow_nonneg hu p)
    (Real.rpow_nonneg (sub_nonneg.mpr hu1) (p - 1)))

theorem erasureMomentFactor_factor {p u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    erasureMomentFactor p u = u + u * (u / (1 - u)) ^ (p - 1) := by
  unfold erasureMomentFactor
  rw [Real.div_rpow hu.le (by linarith)]
  have heq : u ^ p = u * u ^ (p - 1) := by
    calc
      _ = u ^ (1 + (p - 1)) := by congr 1; ring
      _ = _ := by rw [Real.rpow_add hu, Real.rpow_one]
  rw [heq]
  ring

theorem exp_neg_rpow_le_one {z r : ℝ} (hz : 0 < z) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    Real.exp (-z) * z ^ r ≤ 1 := by
  have he : Real.exp (-z) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  by_cases hz1 : z ≤ 1
  · exact (mul_le_mul he (Real.rpow_le_one hz.le hz1 hr)
      (Real.rpow_nonneg hz.le r) (by norm_num)).trans_eq (by ring)
  · have hzpow : z ^ r ≤ z := Real.rpow_le_self_of_one_le (le_of_not_ge hz1) hr1
    have hze : z ≤ Real.exp z := by linarith only [Real.add_one_le_exp z]
    calc
      _ ≤ Real.exp (-z) * z := mul_le_mul_of_nonneg_left hzpow (Real.exp_pos _).le
      _ ≤ Real.exp (-z) * Real.exp z := mul_le_mul_of_nonneg_left hze (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add]; simp

theorem exp_neg_erasure_odds {z : ℝ} (hz : 0 < z) :
    Real.exp (-z) / (1 - Real.exp (-z)) ≤ 1 / z := by
  have hu1 : Real.exp (-z) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hprod : Real.exp (-z) * (z + 1) ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp z) (Real.exp_pos (-z)).le
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h
    exact h
  apply (div_le_div_iff₀ (by linarith : 0 < 1 - Real.exp (-z)) hz).mpr
  nlinarith only [hprod]

/-- A global bound valid in both the small- and large-confidence regimes. -/
theorem erasureMomentFactor_exp_bound {p z : ℝ} (hp : 1 < p) (hp2 : p ≤ 2)
    (hz : 0 < z) : erasureMomentFactor p (Real.exp (-z)) ≤ 2 / z ^ (p - 1) := by
  have hr : 0 ≤ p - 1 := by linarith
  have hu1 : Real.exp (-z) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hzpow : 0 < z ^ (p - 1) := Real.rpow_pos_of_pos hz _
  have hu : Real.exp (-z) ≤ 1 / z ^ (p - 1) := by
    apply (le_div_iff₀ hzpow).mpr
    exact exp_neg_rpow_le_one hz hr (by linarith)
  have hodds : (Real.exp (-z) / (1 - Real.exp (-z))) ^ (p - 1) ≤
      1 / z ^ (p - 1) := by
    calc
      _ ≤ (1 / z) ^ (p - 1) := Real.rpow_le_rpow
        (div_nonneg (Real.exp_pos _).le (sub_nonneg.mpr hu1.le))
        (exp_neg_erasure_odds hz) hr
      _ = _ := by rw [Real.div_rpow (by norm_num) hz.le, Real.one_rpow]
  rw [erasureMomentFactor_factor (Real.exp_pos _) hu1]
  have hm := mul_le_mul hu1.le hodds
    (Real.rpow_nonneg (div_nonneg (Real.exp_pos _).le (sub_nonneg.mpr hu1.le)) _)
    (by norm_num : (0 : ℝ) ≤ 1)
  calc
    _ ≤ 1 / z ^ (p - 1) + 1 * (1 / z ^ (p - 1)) := add_le_add hu hm
    _ = _ := by ring

def confidenceAmplitude (G s p z : ℝ) : ℝ := min G ((s / 2) * z ^ (1 - 1 / p))

theorem confidenceAmplitude_nonneg {G s p z : ℝ} (hG : 0 ≤ G) (hs : 0 ≤ s)
    (hz : 0 ≤ z) : 0 ≤ confidenceAmplitude G s p z := by unfold confidenceAmplitude; positivity

/-- The explicit amplitude makes the actual centered Bernoulli moment admissible. -/
theorem confidenceAmplitude_moment {G s p z : ℝ}
    (hG : 0 ≤ G) (hs : 0 ≤ s) (hp : 1 < p) (hp2 : p ≤ 2) (hz : 0 < z) :
    (confidenceAmplitude G s p z) ^ p * erasureMomentFactor p (Real.exp (-z)) ≤ s ^ p := by
  have hp0 : 0 ≤ p := by linarith
  have hbase : confidenceAmplitude G s p z ≤ (s / 2) * z ^ (1 - 1 / p) := min_le_right _ _
  have hpow := Real.rpow_le_rpow (confidenceAmplitude_nonneg hG hs hz.le) hbase hp0
  have hfactor : ((s / 2) * z ^ (1 - 1 / p)) ^ p =
      s ^ p / (2 : ℝ) ^ p * z ^ (p - 1) := by
    rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hz.le _),
      Real.div_rpow hs (by norm_num), ← Real.rpow_mul hz.le]
    have he : (1 - 1 / p) * p = p - 1 := by
      field_simp [ne_of_gt (show 0 < p by linarith)]
    rw [he]
  have hu1 : Real.exp (-z) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hJ := erasureMomentFactor_exp_bound hp hp2 hz
  have hm := mul_le_mul hpow hJ (erasureMomentFactor_nonneg (Real.exp_pos _).le hu1)
    (Real.rpow_nonneg (by positivity) p)
  rw [hfactor] at hm
  have hzpow := (Real.rpow_pos_of_pos hz (p - 1)).ne'
  have heq : s ^ p / (2 : ℝ) ^ p * z ^ (p - 1) * (2 / z ^ (p - 1)) =
      s ^ p * (2 / (2 : ℝ) ^ p) := by field_simp; ring
  rw [heq] at hm
  have htwo : (2 : ℝ) ≤ (2 : ℝ) ^ p := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hp.le
  have hratio : 2 / (2 : ℝ) ^ p ≤ 1 := (div_le_one (by positivity)).mpr htwo
  exact hm.trans (by simpa using mul_le_mul_of_nonneg_left hratio (Real.rpow_nonneg hs p))

end HeavyTail
