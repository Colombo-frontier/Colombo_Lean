import HeavyTail.ThresholdChoice
import HeavyTail.PhaseSum
import HeavyTail.LocalizationTuning
import Mathlib.Data.Complex.ExponentialBounds

/-! Deterministic localization schedules. The dyadic terminal radius and the
complete rounded raw-call budget are derived from the three amplitude terms. -/

noncomputable section
open scoped BigOperators
namespace HeavyTail

theorem exists_localization_terminal_radius {R₀ r : ℝ} (hr : 0 < r)
    (hstart : 2 * r ≤ R₀) :
    ∃ J : ℕ, 1 ≤ J ∧ r ≤ finalLocalizationRadius R₀ J ∧
      finalLocalizationRadius R₀ J < 2 * r := by
  have hratio : 1 ≤ R₀ / r := (le_div_iff₀ hr).mpr (by linarith)
  obtain ⟨J, hlo, hhi⟩ := exists_nat_pow_near hratio (by norm_num : (1 : ℝ) < 2)
  have hJ : 1 ≤ J := by
    by_contra h
    have hz : J = 0 := by omega
    rw [hz] at hhi
    norm_num at hhi
    have := (div_lt_iff₀ hr).mp hhi
    linarith
  refine ⟨J, hJ, ?_, ?_⟩
  · apply (le_div_iff₀ (by positivity : 0 < (2 : ℝ) ^ J)).mpr
    have := (le_div_iff₀ hr).mp hlo
    nlinarith only [this]
  · apply (div_lt_iff₀ (by positivity : 0 < (2 : ℝ) ^ J)).mpr
    have := (div_lt_iff₀ hr).mp hhi
    rw [pow_succ] at this
    nlinarith only [this]

def localizationTerminalMultiplier (q C : ℝ) : ℝ :=
  36 * C * stageSumConstant (1 / q) + 1

theorem localizationTerminalMultiplier_bounds {q C : ℝ} (hC : 1 ≤ C) :
    1 ≤ localizationTerminalMultiplier q C ∧
      36 * C * stageSumConstant (1 / q) ≤ localizationTerminalMultiplier q C := by
  have hS : (1 / 3 : ℝ) ≤ stageSumConstant (1 / q) := le_max_left _ _
  have hc : 0 ≤ C := zero_le_one.trans hC
  have hprod : 0 ≤ 36 * C * stageSumConstant (1 / q) := by positivity
  unfold localizationTerminalMultiplier
  constructor <;> linarith

/-- Converse to the scalar power-term tuning estimate, with no probability
or online assumption. -/
theorem power_budget_of_term {s ell t v q : ℝ} (hs : 0 ≤ s) (hell : 0 < ell)
    (ht : 0 < t) (hv : 0 < v) (hq : 0 < q)
    (hterm : s * (ell / t) ^ q ≤ v) :
    ell * (s / v) ^ (1 / q) ≤ t := by
  have hn : 0 ≤ s * (ell / t) ^ q := by positivity
  have hp := Real.rpow_le_rpow hn hterm (by positivity : 0 ≤ 1 / q)
  rw [Real.mul_rpow hs (by positivity), ← Real.rpow_mul (by positivity),
    mul_one_div_cancel hq.ne', Real.rpow_one] at hp
  rw [Real.div_rpow hs hv.le, ← mul_div_assoc]
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hv _)).mpr
  have htprod := mul_le_mul_of_nonneg_right hp ht.le
  have he : (s ^ (1 / q) * (ell / t)) * t = ell * s ^ (1 / q) := by field_simp; ring
  rw [he] at htprod
  convert htprod using 1 <;> ring

theorem localization_terminal_components {G V s ell t v q μ R M : ℝ}
    (hG : 0 ≤ G) (hV : 0 ≤ V) (hs : 0 ≤ s) (hell : 0 < ell)
    (ht : 0 < t) (hv : 0 < v) (hq : 0 < q) (hq1 : q ≤ 1)
    (hμ : 0 < μ) (hR : 0 < R) (hM : 1 ≤ M)
    (hroot : (G + Real.sqrt V) / Real.sqrt t ≤ v)
    (hlinear : G * ell / t ≤ v) (hpower : s * (ell / t) ^ q ≤ v)
    (hradius : M * v ≤ μ * R) :
    (G ^ 2 + V) / (μ ^ 2 * R ^ 2) ≤ t / M ∧
      (G / (μ * R)) * ell ≤ t / M ∧
      (s / (μ * R)) ^ (1 / q) * ell ≤ t / M := by
  have hMpos : 0 < M := zero_lt_one.trans_le hM
  have ha : 0 < μ * R := mul_pos hμ hR
  have hrp : 1 ≤ 1 / q := (le_div_iff₀ hq).mpr (by simpa using hq1)
  have hroot' := (div_le_iff₀ (Real.sqrt_pos.mpr ht)).mp hroot
  have hsquare := pow_le_pow_left₀ (by positivity : 0 ≤ G + Real.sqrt V) hroot' 2
  rw [mul_pow, Real.sq_sqrt ht.le] at hsquare
  have hA : G ^ 2 + V ≤ v ^ 2 * t := by
    nlinarith [Real.sq_sqrt hV, mul_nonneg hG (Real.sqrt_nonneg V)]
  have harad := pow_le_pow_left₀ (mul_nonneg hMpos.le hv.le) hradius 2
  rw [mul_pow, mul_pow] at harad
  have hMsq : M ≤ M ^ 2 := by nlinarith
  have hB := (div_le_iff₀ ht).mp hlinear
  have hP := power_budget_of_term hs hell ht hv hq hpower
  refine ⟨?_, ?_, ?_⟩
  · apply (div_le_div_iff₀ (by positivity : 0 < μ ^ 2 * R ^ 2) hMpos).mpr
    have hb1 := mul_le_mul_of_nonneg_left hA hMpos.le
    have hb2 := mul_le_mul_of_nonneg_right hMsq (by positivity : 0 ≤ v ^ 2 * t)
    have hb3 := mul_le_mul_of_nonneg_right harad ht.le
    nlinarith only [hb1, hb2, hb3]
  · rw [div_mul_eq_mul_div]
    apply (div_le_div_iff₀ ha hMpos).mpr
    have hb1 := mul_le_mul_of_nonneg_left hB hMpos.le
    have hb2 := mul_le_mul_of_nonneg_right hradius ht.le
    nlinarith only [hb1, hb2]
  · have hratio : s / (μ * R) ≤ (s / v) / M := by
      calc
        s / (μ * R) ≤ s / (M * v) := div_le_div_of_nonneg_left hs (mul_pos hMpos hv) hradius
        _ = (s / v) / M := by ring
    have hp := mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow (by positivity) hratio (by positivity : 0 ≤ 1 / q)) hell.le
    rw [Real.div_rpow (by positivity) hMpos.le] at hp
    have hMp : M ≤ M ^ (1 / q) := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hM hrp
    calc
      _ ≤ ((s / v) ^ (1 / q) / M ^ (1 / q)) * ell := hp
      _ = (ell * (s / v) ^ (1 / q)) / M ^ (1 / q) := by ring
      _ ≤ t / M ^ (1 / q) := div_le_div_of_nonneg_right hP (Real.rpow_nonneg hMpos.le _)
      _ ≤ t / M := div_le_div_of_nonneg_left ht.le hMpos hMp

/-- The complete ceiling schedule uses at most t charged raw calls. The
constant depends only on the phase constant C and the exponent q. -/
theorem localization_raw_budget_le {G V s ell t v q μ R C : ℝ}
    (hG : 0 ≤ G) (hV : 0 ≤ V) (hs : 0 ≤ s) (hell : 1 ≤ ell)
    (ht : 0 < t) (hv : 0 < v) (hq : 0 < q) (hq1 : q ≤ 1)
    (hμ : 0 < μ) (hR : 0 < R) (hC : 1 ≤ C)
    (hroot : (G + Real.sqrt V) / Real.sqrt t ≤ v)
    (hlinear : G * ell / t ≤ v) (hpower : s * (ell / t) ^ q ≤ v)
    (hradius : localizationTerminalMultiplier q C * v ≤ μ * R)
    (J : ℕ) (hwarm : (2 : ℝ) ^ J * R ≤ Real.sqrt 2 * G / μ) :
    4 * (∑ m ∈ Finset.range J,
      (⌈C * physicalStageWeight (G ^ 2 + V) G s μ R (1 / q) ell m⌉₊ : ℝ)) ≤ t := by
  let M := localizationTerminalMultiplier q C
  have hM := localizationTerminalMultiplier_bounds (q := q) hC
  have hMpos : 0 < M := zero_lt_one.trans_le hM.1
  have hS : 0 ≤ stageSumConstant (1 / q) :=
    (by norm_num : (0 : ℝ) ≤ 1 / 3).trans (le_max_left _ _)
  have hc : 0 ≤ C := zero_le_one.trans hC
  have hcomponents := localization_terminal_components hG hV hs (zero_lt_one.trans_le hell)
    ht hv hq hq1 hμ hR hM.1 hroot hlinear hpower hradius
  have hsum := physical_raw_stage_budget_of_radius hC (by linarith : G ^ 2 ≤ G ^ 2 + V)
    hG hs hμ hR (by positivity : 0 < 1 / q) hell J hwarm
  apply hsum.trans
  have hcpt : (G ^ 2 + V) / (μ ^ 2 * R ^ 2) + (G / (μ * R)) * ell +
      (s / (μ * R)) ^ (1 / q) * ell ≤ 3 * (t / M) := by
    linarith only [hcomponents.1, hcomponents.2.1, hcomponents.2.2]
  apply (mul_le_mul_of_nonneg_left hcpt (by positivity : 0 ≤ 12 * C * stageSumConstant (1 / q))).trans
  have he : 12 * C * stageSumConstant (1 / q) * (3 * (t / M)) =
      (36 * C * stageSumConstant (1 / q) / M) * t := by ring
  rw [he]
  have hratio : 36 * C * stageSumConstant (1 / q) / M ≤ 1 := (div_le_one hMpos).mpr hM.2
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hratio ht.le

theorem confidenceLog_ge_one {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1 / 10) :
    1 ≤ confidenceLog δ := by
  unfold confidenceLog
  apply (Real.le_log_iff_exp_le (by positivity : 0 < 3 / δ)).mpr
  have hthree : (3 : ℝ) ≤ 3 / δ := (le_div_iff₀ hδ).mpr (by linarith)
  exact (Real.exp_one_lt_d9.le.trans (by norm_num)).trans hthree

theorem fixedThresholdAmplitude_components (θ : OracleParameters) {τ : ℝ}
    (hτ : 0 < τ) (hT : 0 < θ.T) :
    let v := fixedThresholdAmplitude θ.G θ.L θ.s θ.p θ.δ τ θ.T
    0 < v ∧
      (θ.G + Real.sqrt (θ.L ^ θ.p * τ ^ (2 - θ.p))) / Real.sqrt θ.T ≤ v ∧
      θ.G * confidenceLog θ.δ / θ.T ≤ v ∧
      θ.s * (confidenceLog θ.δ / θ.T) ^ (1 - 1 / θ.p) ≤ v ∧
      θ.s * (θ.L / τ) ^ (θ.p - 1) ≤ v := by
  have hG := θ.G_pos
  have hs := θ.s_pos
  have hL : 0 < θ.L := θ.s_pos.trans_le θ.s_le_L
  have ht : (0 : ℝ) < θ.T := Nat.cast_pos.mpr hT
  have hell := confidenceLog_pos θ.δ_pos θ.δ_lt_tenth
  have hroot : 0 < (θ.G + Real.sqrt (θ.L ^ θ.p * τ ^ (2 - θ.p))) / Real.sqrt θ.T := by
    positivity
  have hlin : 0 ≤ θ.G * confidenceLog θ.δ / θ.T := by positivity
  have hpower : 0 ≤ θ.s * (confidenceLog θ.δ / θ.T) ^ (1 - 1 / θ.p) := by positivity
  have hbias : 0 ≤ θ.s * (θ.L / τ) ^ (θ.p - 1) := by positivity
  dsimp only [fixedThresholdAmplitude]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith

theorem exists_fixedThreshold_localization_schedule (θ : OracleParameters)
    (hμ : 0 < θ.μ) (hT : 0 < θ.T) {τ C R₀ : ℝ}
    (hτ : 0 < τ) (hC : 1 ≤ C) (hwarm : R₀ ≤ Real.sqrt 2 * θ.G / θ.μ)
    (hstart : 2 * (localizationTerminalMultiplier (1 - 1 / θ.p) C *
      fixedThresholdAmplitude θ.G θ.L θ.s θ.p θ.δ τ θ.T / θ.μ) ≤ R₀) :
    let q := 1 - 1 / θ.p
    let v := fixedThresholdAmplitude θ.G θ.L θ.s θ.p θ.δ τ θ.T
    let M := localizationTerminalMultiplier q C
    ∃ J : ℕ, 1 ≤ J ∧ M * v / θ.μ ≤ finalLocalizationRadius R₀ J ∧
      finalLocalizationRadius R₀ J < 2 * (M * v / θ.μ) ∧
      4 * (∑ m ∈ Finset.range J,
        (⌈C * physicalStageWeight (θ.G ^ 2 + θ.L ^ θ.p * τ ^ (2 - θ.p))
          θ.G θ.s θ.μ (finalLocalizationRadius R₀ J) (1 / q) (confidenceLog θ.δ) m⌉₊ : ℝ)) ≤ θ.T := by
  let q := 1 - 1 / θ.p
  let v := fixedThresholdAmplitude θ.G θ.L θ.s θ.p θ.δ τ θ.T
  let M := localizationTerminalMultiplier q C
  have hv := fixedThresholdAmplitude_components θ hτ hT
  have hM := localizationTerminalMultiplier_bounds (q := q) hC
  have hr : 0 < M * v / θ.μ := div_pos
    (mul_pos (zero_lt_one.trans_le hM.1) hv.1) hμ
  obtain ⟨J, hJ, hlo, hhi⟩ := exists_localization_terminal_radius hr hstart
  refine ⟨J, hJ, hlo, hhi, ?_⟩
  have hq0 : 0 < q := by
    dsimp [q]
    have hinv : 1 / θ.p < 1 := (div_lt_one (by linarith only [θ.p_gt_one] : 0 < θ.p)).mpr θ.p_gt_one
    linarith
  have hq1 : q ≤ 1 := (heavyTailExponent_mem θ.p_gt_one).2
  have hL : 0 < θ.L := θ.s_pos.trans_le θ.s_le_L
  have hR : 0 < finalLocalizationRadius R₀ J := hr.trans_le hlo
  apply localization_raw_budget_le θ.G_pos.le (by positivity : 0 ≤ θ.L ^ θ.p * τ ^ (2 - θ.p))
    θ.s_pos.le (confidenceLog_ge_one θ.δ_pos θ.δ_lt_tenth) (Nat.cast_pos.mpr hT)
    hv.1 hq0 hq1 hμ hR hC hv.2.1 hv.2.2.1 hv.2.2.2.1
  · have h := (div_le_iff₀ hμ).mp hlo
    nlinarith only [h]
  · have he : (2 : ℝ) ^ J * finalLocalizationRadius R₀ J = R₀ := by
      unfold finalLocalizationRadius
      field_simp
    rwa [he]

theorem localizationTerminalMultiplier_ge_scale {q C₀ : ℝ} (hC₀ : 0 ≤ C₀) :
    localizationScale C₀ ≤ localizationTerminalMultiplier q (localizationBudgetConstant q C₀) := by
  have hc := localizationBudgetConstant_bounds (q := q) hC₀
  have hC : 0 ≤ localizationBudgetConstant q C₀ := (by norm_num : (0 : ℝ) ≤ 2).trans hc.1
  have hS : (1 / 3 : ℝ) ≤ stageSumConstant (1 / q) := le_max_left _ _
  have hm := mul_le_mul_of_nonneg_left hS (by positivity : 0 ≤ 36 * localizationBudgetConstant q C₀)
  unfold localizationTerminalMultiplier
  nlinarith only [hm, hc.2.2.1, hC]

theorem fixedThreshold_localization_bias_target (θ : OracleParameters)
    {τ C₀ R : ℝ} (hτ : 0 < τ) (hT : 0 < θ.T) (hC₀ : 0 ≤ C₀)
    (hradius : localizationTerminalMultiplier (1 - 1 / θ.p)
      (localizationBudgetConstant (1 - 1 / θ.p) C₀) *
      fixedThresholdAmplitude θ.G θ.L θ.s θ.p θ.δ τ θ.T ≤ θ.μ * R) :
    θ.s * (θ.L / τ) ^ (θ.p - 1) ≤ θ.μ * R / localizationScale C₀ := by
  have hv := fixedThresholdAmplitude_components θ hτ hT
  have hK := localizationScale_pos hC₀
  have hM := localizationTerminalMultiplier_ge_scale (q := 1 - 1 / θ.p) hC₀
  apply (le_div_iff₀ hK).mpr
  have hfirst := mul_le_mul_of_nonneg_left hv.2.2.2.2 hK.le
  have hsecond := mul_le_mul_of_nonneg_right hM hv.1.le
  nlinarith only [hfirst, hsecond, hradius]

theorem localizationPhaseBudget_eq_physical (G V s μ R q ell C₀ : ℝ) (m : ℕ) :
    localizationPhaseBudget G V s μ ((2 : ℝ) ^ (m + 1) * R) q (stageConfidence ell m) C₀ =
      ⌈localizationBudgetConstant q C₀ * physicalStageWeight (G ^ 2 + V) G s μ R (1 / q) ell m⌉₊ := rfl

end HeavyTail
