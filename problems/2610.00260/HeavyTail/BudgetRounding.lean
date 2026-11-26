import HeavyTail.LocalizationSchedule

/-! All-budget arithmetic: accepted-round rounding, small-budget cap, and
parameter-only combination of the convex and strongly convex branches. -/

noncomputable section
namespace HeavyTail

theorem accepted_round_count_bounds {T : ℕ} {ell : ℝ}
    (hell : 1 ≤ ell) (hbudget : 8 * ell ≤ T) :
    0 < T / 4 ∧ 4 * (T / 4) ≤ T ∧ ell ≤ (T / 4 : ℕ) ∧
      (T : ℝ) / 8 ≤ (T / 4 : ℕ) := by
  have hTreal : (8 : ℝ) ≤ T := by linarith
  have hTnat : 8 ≤ T := by exact_mod_cast hTreal
  have hn : 0 < T / 4 := by omega
  have hraw : 4 * (T / 4) ≤ T := by omega
  have hratioNat : T ≤ 8 * (T / 4) := by omega
  have hratio : (T : ℝ) ≤ 8 * (T / 4 : ℕ) := by exact_mod_cast hratioNat
  refine ⟨hn, hraw, ?_, ?_⟩ <;> linarith

theorem divide_budget_comparison {A : ℝ} {n T : ℕ}
    (hA : 0 ≤ A) (hn : 0 < n) (hT : 0 < T) (hratio : (T : ℝ) ≤ 8 * n) :
    A / n ≤ 8 * (A / T) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hTR : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ hnR hTR).mpr
  have hm := mul_le_mul_of_nonneg_left hratio hA
  nlinarith only [hm]

theorem root_budget_comparison {A : ℝ} {n T : ℕ}
    (hA : 0 ≤ A) (hn : 0 < n) (hT : 0 < T) (hratio : (T : ℝ) ≤ 8 * n) :
    A / Real.sqrt n ≤ 8 * (A / Real.sqrt T) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hTR : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  have hsqrt : Real.sqrt T ≤ 8 * Real.sqrt n := by
    apply (Real.sqrt_le_left (by positivity : 0 ≤ 8 * Real.sqrt n)).mpr
    rw [mul_pow, Real.sq_sqrt hnR.le]
    nlinarith only [hratio, hnR]
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ (Real.sqrt_pos.mpr hnR) (Real.sqrt_pos.mpr hTR)).mpr
  have hm := mul_le_mul_of_nonneg_left hsqrt hA
  nlinarith only [hm]

theorem power_budget_comparison {s ell q : ℝ} {n T : ℕ}
    (hs : 0 ≤ s) (hell : 0 ≤ ell) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hn : 0 < n) (hT : 0 < T) (hratio : (T : ℝ) ≤ 8 * n) :
    s * (ell / n) ^ q ≤ 8 * (s * (ell / T) ^ q) := by
  have hi := divide_budget_comparison hell hn hT hratio
  have hp := Real.rpow_le_rpow (by positivity : 0 ≤ ell / n) hi hq
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 8) (by positivity : 0 ≤ ell / T)] at hp
  have hfactor : (8 : ℝ) ^ q ≤ 8 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 8) hq1
  have hp' := hp.trans (mul_le_mul_of_nonneg_right hfactor (Real.rpow_nonneg (by positivity) q))
  have hm := mul_le_mul_of_nonneg_left hp' hs
  nlinarith only [hm]

theorem fixedThresholdAmplitude_budget_comparison (θ : OracleParameters) {τ : ℝ}
    (hτ : 0 < τ) {n T : ℕ} (hn : 0 < n) (hT : 0 < T)
    (hratio : (T : ℝ) ≤ 8 * n) :
    fixedThresholdAmplitude θ.G θ.L θ.s θ.p θ.δ τ n ≤
      8 * fixedThresholdAmplitude θ.G θ.L θ.s θ.p θ.δ τ T := by
  have hG := θ.G_pos
  have hs := θ.s_pos
  have hL : 0 < θ.L := θ.s_pos.trans_le θ.s_le_L
  have hell := confidenceLog_pos θ.δ_pos θ.δ_lt_tenth
  have hq := heavyTailExponent_mem θ.p_gt_one
  have hroot := root_budget_comparison
    (by positivity : 0 ≤ θ.G + Real.sqrt (θ.L ^ θ.p * τ ^ (2 - θ.p))) hn hT hratio
  have hlin := divide_budget_comparison (by positivity : 0 ≤ θ.G * confidenceLog θ.δ) hn hT hratio
  have hpower := power_budget_comparison θ.s_pos.le hell.le hq.1 hq.2 hn hT hratio
  have hbias : 0 ≤ θ.s * (θ.L / τ) ^ (θ.p - 1) := by positivity
  unfold fixedThresholdAmplitude
  linarith only [hroot, hlin, hpower, hbias]

theorem fixedThresholdAmplitude_accepted_rounds (θ : OracleParameters) {τ : ℝ}
    (hτ : 0 < τ) (hbudget : 8 * confidenceLog θ.δ ≤ θ.T) :
    fixedThresholdAmplitude θ.G θ.L θ.s θ.p θ.δ τ (θ.T / 4) ≤
      8 * fixedThresholdAmplitude θ.G θ.L θ.s θ.p θ.δ τ θ.T := by
  have hb := accepted_round_count_bounds (confidenceLog_ge_one θ.δ_pos θ.δ_lt_tenth) hbudget
  have hT : 0 < θ.T := by omega
  apply fixedThresholdAmplitude_budget_comparison θ hτ hb.1 hT
  linarith only [hb.2.2.2]

theorem small_budget_linear_cap {G ell : ℝ} {T : ℕ}
    (hG : 0 ≤ G) (hT : 0 < T) (hbudget : (T : ℝ) < 8 * ell) :
    G / 8 ≤ G * ell / T := by
  apply (le_div_iff₀ (Nat.cast_pos.mpr hT : (0 : ℝ) < T)).mpr
  have hm := mul_le_mul_of_nonneg_left hbudget.le hG
  nlinarith only [hm]

theorem envelope_cap_of_eighth_le {μ D G v : ℝ}
    (hμ : 0 ≤ μ) (hD : 0 ≤ D) (hG : 0 ≤ G) (hcap : G / 8 ≤ v) :
    envelope μ D G ≤ 64 * envelope μ D (min G v) := by
  have hsmall : G / 8 ≤ min G v := le_min (by linarith) hcap
  have hs := envelope_scale_lower hμ hD hG (by norm_num : (0 : ℝ) ≤ 1 / 8)
    (by norm_num : (1 / 8 : ℝ) ≤ 1)
  have hm := envelope_mono hμ hD (by positivity : 0 ≤ G / 8) hsmall
  have he : (1 / 8 : ℝ) * G = G / 8 := by ring
  rw [he] at hs
  norm_num at hs
  linarith only [hs, hm]

theorem small_budget_envelope_cap (θ : OracleParameters) {τ : ℝ}
    (hτ : 0 < τ) (hT : 0 < θ.T) (hbudget : (θ.T : ℝ) < 8 * confidenceLog θ.δ) :
    envelope θ.μ θ.D θ.G ≤ 64 * envelope θ.μ θ.D
      (min θ.G (fixedThresholdAmplitude θ.G θ.L θ.s θ.p θ.δ τ θ.T)) := by
  apply envelope_cap_of_eighth_le θ.μ_nonneg θ.D_pos.le θ.G_pos.le
  exact (small_budget_linear_cap θ.G_pos.le hT hbudget).trans
    (fixedThresholdAmplitude_components θ hτ hT).2.2.1

def parameterBranchMinimum (μ D G v Ccap Clinear Cquadratic : ℝ) : ℝ :=
  min (Ccap * envelope μ D G)
    (if μ = 0 then Clinear * (D * v)
     else min (Clinear * (D * v)) (Cquadratic * (v ^ 2 / μ)))

/-- Selecting the smallest public guarantee combines all curvature branches,
including μ=0, with an explicit universal envelope comparison. -/
theorem parameterBranchMinimum_le_envelope {μ D G v Ccap Clinear Cquadratic : ℝ}
    (hμ : 0 ≤ μ) (hD : 0 ≤ D) (hG : 0 ≤ G) (hv : 0 ≤ v)
    (hcap : 0 ≤ Ccap) (hlin : 0 ≤ Clinear) (hquad : 0 ≤ Cquadratic) :
    parameterBranchMinimum μ D G v Ccap Clinear Cquadratic ≤
      2 * max Ccap (max Clinear Cquadratic) * envelope μ D (min G v) := by
  let C := max Ccap (max Clinear Cquadratic)
  have hC : 0 ≤ C := hcap.trans (le_max_left _ _)
  have hc : Ccap ≤ C := le_max_left _ _
  have hl : Clinear ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hq : Cquadratic ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  have hmincap : parameterBranchMinimum μ D G v Ccap Clinear Cquadratic ≤
      Ccap * envelope μ D G := min_le_left _ _
  by_cases hGv : G ≤ v
  · rw [min_eq_left hGv]
    have henv := envelope_nonneg hμ hD hG
    have hm := mul_le_mul_of_nonneg_right hc henv
    have hprod := mul_nonneg hC henv
    change _ ≤ 2 * C * envelope μ D G
    nlinarith only [hmincap, hm, hprod]
  · have hvG : v ≤ G := le_of_not_ge hGv
    rw [min_eq_right hvG]
    have henv := envelope_nonneg hμ hD hv
    by_cases hz : μ = 0
    · have hb : parameterBranchMinimum μ D G v Ccap Clinear Cquadratic ≤ Clinear * (D * v) := by
        unfold parameterBranchMinimum
        rw [if_pos hz]
        exact min_le_right _ _
      have hm := mul_le_mul_of_nonneg_right hl (mul_nonneg hD hv)
      have he : envelope μ D v = D * v := by rw [hz, envelope_zero_curvature]
      rw [he] at henv ⊢
      change _ ≤ 2 * C * (D * v)
      nlinarith only [hb, hm, mul_nonneg hC henv]
    · have hμpos : 0 < μ := lt_of_le_of_ne hμ (Ne.symm hz)
      have hb : parameterBranchMinimum μ D G v Ccap Clinear Cquadratic ≤
          min (Clinear * (D * v)) (Cquadratic * (v ^ 2 / μ)) := by
        unfold parameterBranchMinimum
        rw [if_neg hz]
        exact min_le_right _ _
      have hb' : min (Clinear * (D * v)) (Cquadratic * (v ^ 2 / μ)) ≤
          C * min (D * v) (v ^ 2 / μ) := by
        rw [mul_min_of_nonneg _ _ hC]
        exact min_le_min (mul_le_mul_of_nonneg_right hl (mul_nonneg hD hv))
          (mul_le_mul_of_nonneg_right hq (div_nonneg (sq_nonneg v) hμ))
      have henv := envelope_lower_min hμpos hD hv
      have hm := mul_le_mul_of_nonneg_left henv hC
      change _ ≤ 2 * C * envelope μ D v
      nlinarith only [hb, hb', hm]

theorem envelope_min_amplitude_scale_upper {μ D G x v C : ℝ}
    (hμ : 0 ≤ μ) (hD : 0 ≤ D) (hG : 0 ≤ G) (hx : 0 ≤ x)
    (hC : 1 ≤ C) (hamp : x ≤ C * v) :
    envelope μ D (min G x) ≤ C ^ 2 * envelope μ D (min G v) := by
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hGmul : G ≤ G * C := by nlinarith [mul_le_mul_of_nonneg_left hC hG]
  have hscaled : min G x / C ≤ min G v := by
    apply le_min
    · exact (div_le_iff₀ hCpos).mpr ((min_le_left _ _).trans hGmul)
    · apply (div_le_iff₀ hCpos).mpr
      have h := (min_le_right G x).trans hamp
      nlinarith only [h]
  have hmin : 0 ≤ min G x := le_min hG hx
  have hs := envelope_scale_lower hμ hD hmin (by positivity : 0 ≤ 1 / C)
    ((div_le_one hCpos).mpr hC)
  have he : (1 / C) * min G x = min G x / C := by ring
  rw [he] at hs
  have hm := envelope_mono hμ hD (div_nonneg hmin hCpos.le) hscaled
  have he' : (1 / C) ^ 2 * envelope μ D (min G x) = envelope μ D (min G x) / C ^ 2 := by ring
  rw [he'] at hs
  have h := (div_le_iff₀ (sq_pos_of_pos hCpos)).mp (hs.trans hm)
  nlinarith only [h]

theorem commonThreshold_envelope_bound (θ : OracleParameters) (hT : 0 < θ.T) :
    envelope θ.μ θ.D (min θ.G (fixedThresholdAmplitude θ.G θ.L θ.s θ.p θ.δ
      (commonThreshold θ.G θ.L θ.s θ.p θ.T) θ.T)) ≤
      (1024 : ℝ) ^ 2 * envelope θ.μ θ.D
        (min θ.G (optimizationAmplitude θ.G θ.L θ.s θ.p θ.δ θ.T)) := by
  have hG := θ.G_pos
  have hL : 0 < θ.L := θ.s_pos.trans_le θ.s_le_L
  have hτ : 0 < commonThreshold θ.G θ.L θ.s θ.p θ.T :=
    lt_of_lt_of_le (by positivity : 0 < 64 * (4 * θ.G + θ.L))
      (commonThreshold_admissible θ.G_pos.le hL.le θ.T)
  apply envelope_min_amplitude_scale_upper θ.μ_nonneg θ.D_pos.le θ.G_pos.le
    (fixedThresholdAmplitude_components θ hτ hT).1.le (by norm_num)
  exact commonThreshold_amplitude_bound θ hT

end HeavyTail
