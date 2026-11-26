import HeavyTail.MaskedOracleModel
import HeavyTail.GaussianModelLower
import Mathlib.Algebra.Order.Floor.Ring

/-! Explicit all-budget comparison between the coordinate-revelation amplitude
and the manuscript heavy-tail statistical coefficient. -/

namespace HeavyTail.MaskedLower
noncomputable section

def heavyCoefficient (L s p : ℝ) (T : ℕ) : ℝ :=
  s * ((L ^ 2 / s ^ 2) / T) ^ (1 - 1 / p)

def heavyRate (μ D G L s p : ℝ) (T : ℕ) : ℝ :=
  (1 / 16384 : ℝ) * envelope μ D (min G (heavyCoefficient L s p T))

theorem heavyExponent_range {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) :
    0 ≤ 1 - 1 / p ∧ 1 - 1 / p ≤ 1 / 2 := by
  have hp0 : 0 < p := by linarith
  constructor
  · exact sub_nonneg.mpr ((div_le_one hp0).mpr hp.le)
  · have h := (le_div_iff₀ hp0).mpr (show (1 / 2 : ℝ) * p ≤ 1 by linarith)
    linarith

theorem activeDimension_bounds {L s : ℝ} (hs : 0 < s) (hsL : s ≤ L) :
    0 < Nat.ceil (L ^ 2 / s ^ 2) ∧
      L ^ 2 / s ^ 2 ≤ (Nat.ceil (L ^ 2 / s ^ 2) : ℝ) ∧
      (Nat.ceil (L ^ 2 / s ^ 2) : ℝ) ≤ 2 * (L ^ 2 / s ^ 2) := by
  have hL : 0 < L := hs.trans_le hsL
  have he1 : 1 ≤ L ^ 2 / s ^ 2 := (le_div_iff₀ (sq_pos_of_pos hs)).mpr (by nlinarith)
  have he0 : 0 < L ^ 2 / s ^ 2 := by positivity
  refine ⟨Nat.ceil_pos.mpr he0, Nat.le_ceil _, ?_⟩
  exact (Nat.ceil_lt_add_one he0.le).le.trans (by linarith)

theorem activeDimension_variance {L s : ℝ} (hs : 0 < s) :
    L ^ 2 ≤ (Nat.ceil (L ^ 2 / s ^ 2) : ℝ) * s ^ 2 :=
  (div_le_iff₀ (sq_pos_of_pos hs)).mp (Nat.le_ceil _)

theorem activeDimension_scale_lower {L s : ℝ} (hs : 0 < s) (hsL : s ≤ L) :
    s / 2 ≤ L / Real.sqrt (Nat.ceil (L ^ 2 / s ^ 2) : ℝ) := by
  obtain ⟨hk, _, hkupper⟩ := activeDimension_bounds hs hsL
  have hkR : (0 : ℝ) < Nat.ceil (L ^ 2 / s ^ 2) := Nat.cast_pos.mpr hk
  have hroot := Real.sq_sqrt hkR.le
  have hkbound := (le_div_iff₀ (sq_pos_of_pos hs)).mp
    (show (Nat.ceil (L ^ 2 / s ^ 2) : ℝ) ≤ 2 * L ^ 2 / s ^ 2 by
      simpa only [mul_div_assoc] using hkupper)
  have hL : 0 < L := hs.trans_le hsL
  apply (le_div_iff₀ (Real.sqrt_pos.mpr hkR)).mpr
  have hn : 0 ≤ s * Real.sqrt (Nat.ceil (L ^ 2 / s ^ 2) : ℝ) := by positivity
  nlinarith [sq_nonneg L]

theorem masked_sampling_budget {k T : ℕ} (hT : 0 < T) (hkT : k ≤ T) :
    0 < 1 / (8 * (T : ℝ)) ∧ 1 / (8 * (T : ℝ)) ≤ 1 ∧
      (k : ℝ) * (1 / (8 * (T : ℝ))) ≤ 1 ∧
      (T : ℝ) * (1 / (8 * (T : ℝ))) ≤ 1 / 8 := by
  have hTr : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast (Nat.succ_le_of_lt hT)
  have hkTr : (k : ℝ) ≤ T := Nat.cast_le.mpr hkT
  refine ⟨by positivity, (div_le_one (by positivity)).mpr (by linarith), ?_, ?_⟩
  · rw [mul_one_div]
    exact (div_le_one (by positivity)).mpr (by linarith)
  · rw [mul_one_div]
    exact le_of_eq (by field_simp; ring)

theorem maskedAmplitude_heavy_lower {G L s p : ℝ} {T : ℕ}
    (hG : 0 ≤ G) (hs : 0 < s) (hsL : s ≤ L) (hp : 1 < p) (hp2 : p ≤ 2) (hT : 0 < T) :
    (1 / 64 : ℝ) * min G (heavyCoefficient L s p T) ≤
      maskedAmplitude G L p (Nat.ceil (L ^ 2 / s ^ 2)) (1 / (8 * (T : ℝ))) := by
  let k := Nat.ceil (L ^ 2 / s ^ 2)
  let e := L ^ 2 / s ^ 2
  let q := 1 - 1 / p
  have hL : 0 < L := hs.trans_le hsL
  have hTr : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  obtain ⟨hk, hek, _⟩ := activeDimension_bounds hs hsL
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have he0 : 0 ≤ e := by dsimp [e]; positivity
  have hq := heavyExponent_range hp hp2
  have hpow : (e / T) ^ q / 8 ≤ ((k : ℝ) * (1 / (8 * (T : ℝ)))) ^ q := by
    have hmono : (e / (T : ℝ)) ^ q ≤ ((k : ℝ) / T) ^ q :=
      Real.rpow_le_rpow (div_nonneg he0 hTr.le)
        (div_le_div_of_nonneg_right hek hTr.le) hq.1
    have heighth : (1 / 8 : ℝ) ≤ (1 / 8 : ℝ) ^ q := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge
        (by norm_num : (0 : ℝ) < 1 / 8) (by norm_num : (1 / 8 : ℝ) ≤ 1)
        (show q ≤ 1 by dsimp [q]; linarith [hq.2])
    have hmul := mul_le_mul heighth hmono (Real.rpow_nonneg (by positivity) q)
      (Real.rpow_nonneg (by norm_num) q)
    have heq : (k : ℝ) * (1 / (8 * (T : ℝ))) = (1 / 8 : ℝ) * ((k : ℝ) / T) := by ring
    rw [heq, Real.mul_rpow (by norm_num) (by positivity)]
    calc
      (e / (T : ℝ)) ^ q / 8 = (1 / 8 : ℝ) * (e / T) ^ q := by ring
      _ ≤ _ := hmul
  have hscale : s / 8 ≤ L / (4 * Real.sqrt (k : ℝ)) := by
    have h := activeDimension_scale_lower hs hsL
    dsimp [k]
    convert (div_le_div_of_nonneg_right h (by norm_num : (0 : ℝ) ≤ 4)) using 1 <;> ring
  have hsignal : heavyCoefficient L s p T / 64 ≤
      (L / (4 * Real.sqrt (k : ℝ))) * ((k : ℝ) * (1 / (8 * (T : ℝ)))) ^ q := by
    have hm := mul_le_mul hscale hpow (by positivity : 0 ≤ (e / T) ^ q / 8)
      (by positivity : 0 ≤ L / (4 * Real.sqrt (k : ℝ)))
    convert hm using 1 <;> dsimp [heavyCoefficient, e, q] <;> ring
  apply le_min
  · have hm := mul_le_mul_of_nonneg_left (min_le_left G (heavyCoefficient L s p T))
      (by norm_num : (0 : ℝ) ≤ 1 / 64)
    nlinarith
  · calc
      (1 / 64 : ℝ) * min G (heavyCoefficient L s p T) ≤ heavyCoefficient L s p T / 64 := by
        have h := mul_le_mul_of_nonneg_left (min_le_right G (heavyCoefficient L s p T))
          (by norm_num : (0 : ℝ) ≤ 1 / 64)
        convert h using 1 <;> ring
      _ ≤ _ := hsignal

theorem maskedAmplitude_heavy_envelope {μ D G L s p : ℝ} {T : ℕ}
    (hμ : 0 ≤ μ) (hD : 0 ≤ D) (hG : 0 ≤ G) (hs : 0 < s) (hsL : s ≤ L)
    (hp : 1 < p) (hp2 : p ≤ 2) (hT : 0 < T) :
    heavyRate μ D G L s p T ≤
      envelope μ D (maskedAmplitude G L p (Nat.ceil (L ^ 2 / s ^ 2)) (1 / (8 * (T : ℝ)))) / 4 := by
  have hcoef : 0 ≤ heavyCoefficient L s p T := by unfold heavyCoefficient; positivity
  have hscale := envelope_scale_lower hμ hD (le_min hG hcoef)
    (by norm_num : (0 : ℝ) ≤ 1 / 64) (by norm_num : (1 / 64 : ℝ) ≤ 1)
  have hm := envelope_mono hμ hD (by positivity)
    (maskedAmplitude_heavy_lower hG hs hsL hp hp2 hT)
  unfold heavyRate
  nlinarith

theorem heavyCoefficient_le_trace_small_budget {L s p : ℝ} {T : ℕ}
    (hs : 0 < s) (hsL : s ≤ L) (hp : 1 < p) (hp2 : p ≤ 2) (hT : 0 < T)
    (hTk : T < Nat.ceil (L ^ 2 / s ^ 2)) : heavyCoefficient L s p T ≤ L / Real.sqrt T := by
  have hTr : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  have heT : (T : ℝ) < L ^ 2 / s ^ 2 := Nat.lt_ceil.mp hTk
  have hx : 1 ≤ (L ^ 2 / s ^ 2) / T := (le_div_iff₀ hTr).mpr (by simpa using heT.le)
  have hq := heavyExponent_range hp hp2
  have hm := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx hq.2) hs.le
  unfold heavyCoefficient
  apply hm.trans_eq
  rw [← Real.sqrt_eq_rpow, Real.sqrt_div (by positivity), Real.sqrt_div (sq_nonneg L),
    Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs, abs_of_pos hs, abs_of_pos (hs.trans_le hsL)]
  field_simp
  ring

end
end HeavyTail.MaskedLower
