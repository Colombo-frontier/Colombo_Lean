import HeavyTail.BudgetRounding
import HeavyTail.Curvature

/-! Scalar inversion of the all-budget amplitudes. These are the exact costs
appearing in the source sample-complexity corollary. -/

noncomputable section
namespace HeavyTail

def sampleUpperCost (G L s p δ a : ℝ) : ℝ :=
  1 + (G ^ 2 + L ^ 2) / a ^ 2 + G * confidenceLog δ / a +
    (L ^ 2 / s ^ 2 + confidenceLog δ) * (s / a) ^ (1 / (1 - 1 / p))

def sampleLowerCost (L s p δ a : ℝ) : ℝ :=
  max (L ^ 2 / a ^ 2)
    ((L ^ 2 / s ^ 2 + confidenceLog δ) * (s / a) ^ (1 / (1 - 1 / p)))

theorem envelopeInverse_pos {μ D ε : ℝ} (hμ : 0 ≤ μ) (hD : 0 < D) (hε : 0 < ε) :
    0 < envelopeInverse μ D ε := by
  have hn := envelopeInverse_nonneg hμ hD hε.le
  have he := envelope_right_inverse hμ hD hε.le
  by_contra h
  have hz : envelopeInverse μ D ε = 0 := le_antisymm (le_of_not_gt h) hn
  rw [hz] at he
  have hb := envelope_le_linear (D := D) hμ (le_refl (0 : ℝ))
  rw [he] at hb
  nlinarith only [hb, hε]

theorem sampleUpperCost_ge_one (θ : OracleParameters) {a : ℝ} (ha : 0 < a) :
    1 ≤ sampleUpperCost θ.G θ.L θ.s θ.p θ.δ a := by
  have hG := θ.G_pos
  have hs := θ.s_pos
  have hell := confidenceLog_pos θ.δ_pos θ.δ_lt_tenth
  have hA : 0 ≤ (θ.G ^ 2 + θ.L ^ 2) / a ^ 2 := by positivity
  have hB : 0 ≤ θ.G * confidenceLog θ.δ / a := by positivity
  have hP : 0 ≤ (θ.L ^ 2 / θ.s ^ 2 + confidenceLog θ.δ) *
      (θ.s / a) ^ (1 / (1 - 1 / θ.p)) := by positivity
  unfold sampleUpperCost
  linarith

theorem sample_budget_controls_amplitude (θ : OracleParameters) {a C : ℝ}
    (ha : 0 < a) (hC : 0 ≤ C) {T : ℕ} (hT : 0 < T)
    (hbudget : localizationBudgetConstant (1 - 1 / θ.p) C *
      sampleUpperCost θ.G θ.L θ.s θ.p θ.δ a ≤ T) :
    optimizationAmplitude θ.G θ.L θ.s θ.p θ.δ T ≤ a / (C + 1) := by
  let q := 1 - 1 / θ.p
  let K := θ.L ^ 2 / θ.s ^ 2 + confidenceLog θ.δ
  let B := localizationBudgetConstant q C
  let κ := localizationScale C
  let W := sampleUpperCost θ.G θ.L θ.s θ.p θ.δ a
  have hG := θ.G_pos
  have hs := θ.s_pos
  have hL : 0 < θ.L := θ.s_pos.trans_le θ.s_le_L
  have hell := confidenceLog_pos θ.δ_pos θ.δ_lt_tenth
  have hK : 0 < K := by dsimp [K]; positivity
  have hκ : 0 < κ := localizationScale_pos hC
  have hq : 0 < q := by
    have hp0 : 0 < θ.p := by linarith only [θ.p_gt_one]
    have hinv : 1 / θ.p < 1 := (div_lt_one hp0).mpr θ.p_gt_one
    dsimp [q]
    linarith
  have ht : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  have hc := localizationBudgetConstant_bounds (q := q) hC
  have hB : 0 ≤ B := (by norm_num : (0 : ℝ) ≤ 2).trans hc.1
  have hA0 : 0 ≤ (θ.G ^ 2 + θ.L ^ 2) / a ^ 2 := by positivity
  have hlin0 : 0 ≤ θ.G * confidenceLog θ.δ / a := by positivity
  have hpow0 : 0 ≤ K * (θ.s / a) ^ (1 / q) := by positivity
  have hA : (θ.G ^ 2 + θ.L ^ 2) / a ^ 2 ≤ W := by
    dsimp [W, sampleUpperCost, K, q] at *
    linarith only [hlin0, hpow0]
  have hlin : θ.G * confidenceLog θ.δ / a ≤ W := by
    dsimp [W, sampleUpperCost, K, q] at *
    linarith only [hA0, hpow0]
  have hpow : K * (θ.s / a) ^ (1 / q) ≤ W := by
    dsimp [W, sampleUpperCost, K, q] at *
    linarith only [hA0, hlin0]
  have hb1 := (mul_le_mul hc.2.1 hA hA0 hB).trans hbudget
  have hb2 := (mul_le_mul hc.2.2.1 hlin hlin0 hB).trans hbudget
  have hb3 := (mul_le_mul hc.2.2.2 hpow hpow0 hB).trans hbudget
  have hroot := root_term_of_budget θ.G_pos.le (sq_nonneg θ.L) ha hκ ht
    (show 2 * κ ^ 2 * (θ.G ^ 2 + θ.L ^ 2) / a ^ 2 ≤ T by
      simpa only [mul_div_assoc] using hb1)
  rw [Real.sqrt_sq hL.le, add_div] at hroot
  have hlinear : θ.G * confidenceLog θ.δ / T ≤ a / κ := by
    apply (div_le_iff₀ ht).mpr
    have hb : κ * (θ.G * confidenceLog θ.δ) ≤ (T : ℝ) * a :=
      (div_le_iff₀ ha).mp (by simpa only [mul_div_assoc] using hb2)
    have he : a / κ * T = (T : ℝ) * a / κ := by ring
    rw [he]
    apply (le_div_iff₀ hκ).mpr
    nlinarith only [hb]
  have hpb : K * (θ.s / (a / κ)) ^ (1 / q) ≤ T := by
    have he : θ.s / (a / κ) = κ * (θ.s / a) := by field_simp; ring
    rw [he, Real.mul_rpow hκ.le (by positivity)]
    nlinarith only [hb3]
  have hpower := power_term_of_budget θ.s_pos.le hK.le ht (div_pos ha hκ) hq hpb
  have hsum : optimizationAmplitude θ.G θ.L θ.s θ.p θ.δ T ≤ 3 * (a / κ) := by
    unfold optimizationAmplitude statisticalAmplitude
    change θ.G / Real.sqrt T + θ.G * confidenceLog θ.δ / T +
      (θ.L / Real.sqrt T + θ.s * (K / T) ^ q) ≤ _
    linarith only [hroot, hlinear, hpower]
  apply hsum.trans
  have he : 3 * (a / κ) = (3 / 32 : ℝ) * (a / (C + 1)) := by
    dsimp [κ, localizationScale]
    field_simp
  rw [he]
  have hn : 0 ≤ a / (C + 1) := by positivity
  nlinarith only [hn]

theorem sample_scaled_envelope {μ D G a v C : ℝ}
    (hμ : 0 ≤ μ) (hD : 0 ≤ D) (hG : 0 ≤ G) (ha : 0 ≤ a)
    (hv : 0 ≤ v) (hC : 0 ≤ C) (hamp : v ≤ a / (C + 1)) :
    C * envelope μ D (min G v) ≤ envelope μ D a := by
  have hCp : 0 < C + 1 := by positivity
  have hscaled := envelope_scale_upper hμ hD ha (by positivity : 0 ≤ 1 / (C + 1))
    ((div_le_one hCp).mpr (by linarith : 1 ≤ C + 1))
  have he : (1 / (C + 1)) * a = a / (C + 1) := by ring
  rw [he] at hscaled
  have hm := envelope_mono hμ hD (le_min hG hv) ((min_le_right G v).trans hamp)
  have hh := mul_le_mul_of_nonneg_left (hm.trans hscaled) hC
  have hratio : C / (C + 1) ≤ 1 := (div_le_one hCp).mpr (by linarith)
  have hn := envelope_nonneg hμ hD ha
  have hc := mul_le_mul_of_nonneg_right hratio hn
  have he' : C * (1 / (C + 1) * envelope μ D a) = C / (C + 1) * envelope μ D a := by ring
  rw [he'] at hh
  exact hh.trans (by simpa only [one_mul] using hc)

theorem nonsaturated_amplitude_inverse {μ D G w ε c : ℝ}
    (hμ : 0 ≤ μ) (hD : 0 < D) (hG : 0 < G) (hw : 0 ≤ w) (hε : 0 < ε)
    (hc : 0 < c) (hc1 : c ≤ 1)
    (hsmall : ε ≤ (c / 2) * envelope μ D G)
    (hrisk : c * envelope μ D (min G w) ≤ ε) :
    c * w ≤ envelopeInverse μ D ε := by
  have henv := envelope_pos hμ hD hG
  have hwG : w < G := by
    by_contra h
    have hg : G ≤ w := le_of_not_gt h
    rw [min_eq_left hg] at hrisk
    nlinarith only [hrisk, hsmall, mul_pos hc henv]
  rw [min_eq_right hwG.le] at hrisk
  have hs := envelope_scale_upper hμ hD.le hw hc.le hc1
  exact (envelope_inverse_order hμ hD hε.le (mul_nonneg hc.le hw)).mp (hs.trans hrisk)

theorem sample_lower_cost_of_amplitude (θ : OracleParameters) {a c : ℝ}
    (ha : 0 < a) (hc : 0 < c) (hc1 : c ≤ 1) {T : ℕ} (hT : 0 < T)
    (hamp : c * statisticalAmplitude θ.L θ.s θ.p θ.δ T ≤ a) :
    c ^ (1 / (1 - 1 / θ.p)) * sampleLowerCost θ.L θ.s θ.p θ.δ a ≤ T := by
  let q := 1 - 1 / θ.p
  let K := θ.L ^ 2 / θ.s ^ 2 + confidenceLog θ.δ
  have hs := θ.s_pos
  have hL : 0 < θ.L := θ.s_pos.trans_le θ.s_le_L
  have hell := confidenceLog_pos θ.δ_pos θ.δ_lt_tenth
  have hell' : 0 < Real.log (3 / θ.δ) := hell
  have hK : 0 < K := by dsimp [K]; positivity
  have hq : 0 < q := by
    have hp0 : 0 < θ.p := by linarith only [θ.p_gt_one]
    have hinv : 1 / θ.p < 1 := (div_lt_one hp0).mpr θ.p_gt_one
    dsimp [q]
    linarith
  have hq2 : q ≤ 1 / 2 := (MaskedLower.heavyExponent_range θ.p_gt_one θ.p_le_two).2
  have hrp : 2 ≤ 1 / q := by
    have hi := one_div_le_one_div_of_le hq hq2
    norm_num at hi
    simpa only [one_div] using hi
  have ht : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  have htail0 : 0 ≤ θ.s * (K / T) ^ q := by positivity
  have htrace0 : 0 ≤ θ.L / Real.sqrt T := by positivity
  have htrace : c * θ.L / Real.sqrt T ≤ a := by
    change c * (θ.L / Real.sqrt T + θ.s * (K / T) ^ q) ≤ a at hamp
    rw [mul_div_assoc]
    exact (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right htail0) hc.le).trans hamp
  have htail : (c * θ.s) * (K / T) ^ q ≤ a := by
    change c * (θ.L / Real.sqrt T + θ.s * (K / T) ^ q) ≤ a at hamp
    rw [mul_assoc]
    exact (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left htrace0) hc.le).trans hamp
  have htraceBudget : c ^ 2 * (θ.L ^ 2 / a ^ 2) ≤ T := by
    have hprod := (div_le_iff₀ (Real.sqrt_pos.mpr ht)).mp htrace
    have hsq := pow_le_pow_left₀ (mul_nonneg hc.le hL.le) hprod 2
    rw [mul_pow, mul_pow, Real.sq_sqrt ht.le] at hsq
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (sq_pos_of_pos ha)).mpr
    nlinarith only [hsq]
  have hpowerBudget := power_budget_of_term (mul_nonneg hc.le θ.s_pos.le) hK ht ha hq htail
  have hpower : c ^ (1 / q) * (K * (θ.s / a) ^ (1 / q)) ≤ T := by
    have he : c * θ.s / a = c * (θ.s / a) := by ring
    rw [he, Real.mul_rpow hc.le (by positivity)] at hpowerBudget
    nlinarith only [hpowerBudget]
  have hcpow : c ^ (1 / q) ≤ c ^ 2 := by
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_ge hc hc1 hrp
  have htrace' := (mul_le_mul_of_nonneg_right hcpow (by positivity : 0 ≤ θ.L ^ 2 / a ^ 2)).trans htraceBudget
  change c ^ (1 / q) * max (θ.L ^ 2 / a ^ 2) (K * (θ.s / a) ^ (1 / q)) ≤ T
  rw [mul_max_of_nonneg _ _ (Real.rpow_nonneg hc.le _)]
  exact max_le htrace' hpower

end HeavyTail
