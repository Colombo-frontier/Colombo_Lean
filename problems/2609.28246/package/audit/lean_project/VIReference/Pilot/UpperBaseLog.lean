import VIReference.Pilot.UpperBaseAdaptiveCost

/-!
# Logarithmic bound for the base halving schedule
-/

namespace VIReference.Pilot

noncomputable section

universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def baseHalvingLogConstant (p : ℕ) : ℝ :=
  2 + (Real.log (max 1 (correctionConstant p)) + 1) / Real.log 2

theorem correctionConstant_pos (p : ℕ) : 0 < correctionConstant p := by
  unfold correctionConstant
  positivity

theorem baseHalvingCount_le_logCeil (data : VIPublicData E)
    (R delta : ℝ) (hR : 0 ≤ R) (hdelta : 0 < delta) :
    baseHalvingCount data R delta ≤
      ⌈Real.logb 2 (max 1
        (correctionConstant data.p * data.Lp * R ^ data.p / delta))⌉₊ := by
  let c := correctionConstant data.p * data.Lp * R ^ data.p / delta
  let n : ℕ := ⌈Real.logb 2 (max 1 c)⌉₊
  have hcmax : 0 < max 1 c := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hcpow : max 1 c ≤ (2 : ℝ) ^ n := by
    dsimp [n]
    exact positive_le_two_pow_natCeil_logb _ hcmax
  have hpow1 : 1 ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
  have hpowmono : (2 : ℝ) ^ n ≤ ((2 : ℝ) ^ n) ^ data.p := by
    have := pow_le_pow_right₀ hpow1
      (le_trans (by omega : 1 ≤ 2) data.p_ge_two)
    simpa using this
  have hc : c ≤ ((2 : ℝ) ^ n) ^ data.p :=
    (le_max_right 1 c).trans (hcpow.trans hpowmono)
  have hwitness : correctionConstant data.p * data.Lp *
      (R / (2 : ℝ) ^ n) ^ data.p ≤ delta := by
    have hdel0 : 0 ≤ delta := hdelta.le
    have hraw : correctionConstant data.p * data.Lp * R ^ data.p ≤
        delta * (((2 : ℝ) ^ n) ^ data.p) := by
      have := (div_le_iff₀ hdelta).1 hc
      nlinarith
    rw [div_pow]
    have hdenpos : 0 < (((2 : ℝ) ^ n) ^ data.p) := by positivity
    rw [show correctionConstant data.p * data.Lp *
        (R ^ data.p / ((2 : ℝ) ^ n) ^ data.p) =
        (correctionConstant data.p * data.Lp * R ^ data.p) /
          ((2 : ℝ) ^ n) ^ data.p by ring]
    apply (div_le_iff₀ hdenpos).2
    nlinarith
  rw [baseHalvingCount, dif_pos ⟨hR, hdelta⟩]
  exact Nat.find_min' (exists_base_halving_threshold data R delta hR hdelta)
    hwitness

theorem baseHalvingLogConstant_pos (p : ℕ) :
    0 < baseHalvingLogConstant p := by
  have hM : (1 : ℝ) ≤ max 1 (correctionConstant p) := le_max_left _ _
  have hlogM : 0 ≤ Real.log (max 1 (correctionConstant p)) :=
    Real.log_nonneg hM
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold baseHalvingLogConstant
  positivity

theorem baseHalvingCount_cast_le_strongLog (data : VIPublicData E)
    (mu delta R : ℝ) (hmu : 0 < mu) (hdelta : 0 < delta)
    (hR : 0 ≤ R) (hRD : R ≤ data.D) :
    (baseHalvingCount data R delta : ℝ) ≤
      baseHalvingLogConstant data.p * strongLog data mu delta := by
  let cc := correctionConstant data.p
  let M := max 1 cc
  let q := data.Lp * data.D ^ data.p / delta
  let s := 2 + data.Lp * data.D ^ (data.p - 1) / mu + q +
    mu * data.D / delta
  let LS := strongLog data mu delta
  let c := cc * data.Lp * R ^ data.p / delta
  have hcc : 0 < cc := by
    dsimp [cc]
    exact correctionConstant_pos _
  have hM1 : 1 ≤ M := by dsimp [M]; exact le_max_left _ _
  have hMpos : 0 < M := lt_of_lt_of_le (by norm_num) hM1
  have hq0 : 0 ≤ q := by
    dsimp [q]
    exact div_nonneg
      (mul_nonneg data.Lp_pos.le (pow_nonneg data.D_pos.le _)) hdelta.le
  have hs2 : 2 ≤ s := by
    dsimp [s, q]
    have h1 : 0 ≤ data.Lp * data.D ^ (data.p - 1) / mu :=
      div_nonneg (mul_nonneg data.Lp_pos.le (pow_nonneg data.D_pos.le _)) hmu.le
    have h2 : 0 ≤ data.Lp * data.D ^ data.p / delta :=
      div_nonneg (mul_nonneg data.Lp_pos.le (pow_nonneg data.D_pos.le _)) hdelta.le
    have h3 : 0 ≤ mu * data.D / delta :=
      div_nonneg (mul_nonneg hmu.le data.D_pos.le) hdelta.le
    linarith
  have hspos : 0 < s := lt_of_lt_of_le (by norm_num) hs2
  have hLS : LS = 1 + Real.log s := rfl
  have hLS1 : 1 ≤ LS := by
    rw [hLS]
    linarith [Real.log_nonneg (by linarith : 1 ≤ s)]
  have hRp : R ^ data.p ≤ data.D ^ data.p :=
    pow_le_pow_left₀ hR hRD data.p
  have hcq : c ≤ cc * q := by
    dsimp [c, q]
    have hmul := mul_le_mul_of_nonneg_left hRp
      (mul_nonneg hcc.le data.Lp_pos.le)
    calc
      cc * data.Lp * R ^ data.p / delta ≤
          cc * data.Lp * data.D ^ data.p / delta :=
        div_le_div_of_nonneg_right hmul hdelta.le
      _ = cc * (data.Lp * data.D ^ data.p / delta) := by ring
  have hccM : cc ≤ M := by dsimp [M]; exact le_max_right _ _
  have hcMs : c ≤ M * s := by
    calc
      c ≤ cc * q := hcq
      _ ≤ M * q := mul_le_mul_of_nonneg_right hccM hq0
      _ ≤ M * s := mul_le_mul_of_nonneg_left (by
        dsimp [s]
        have h1 : 0 ≤ data.Lp * data.D ^ (data.p - 1) / mu :=
          div_nonneg (mul_nonneg data.Lp_pos.le (pow_nonneg data.D_pos.le _)) hmu.le
        have h3 : 0 ≤ mu * data.D / delta :=
          div_nonneg (mul_nonneg hmu.le data.D_pos.le) hdelta.le
        linarith) hMpos.le
  have hmaxc : max 1 c ≤ M * s := by
    apply max_le
    · have : 1 ≤ M * s := by nlinarith
      exact this
    · exact hcMs
  have hmaxpos : 0 < max 1 c := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hlogmax : Real.log (max 1 c) ≤ Real.log M + Real.log s := by
    have hlog := Real.log_le_log hmaxpos hmaxc
    rw [Real.log_mul hMpos.ne' hspos.ne'] at hlog
    exact hlog
  have hlogmax0 : 0 ≤ Real.log (max 1 c) :=
    Real.log_nonneg (le_max_left _ _)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogb0 : 0 ≤ Real.logb 2 (max 1 c) := by
    unfold Real.logb
    positivity
  have hn := baseHalvingCount_le_logCeil data R delta hR hdelta
  have hncast : (baseHalvingCount data R delta : ℝ) ≤
      (⌈Real.logb 2 (max 1 c)⌉₊ : ℝ) := by
    exact_mod_cast hn
  have hceil := natCeil_cast_le_max_add_one
    (Real.logb 2 (max 1 c))
  rw [max_eq_right hlogb0] at hceil
  have hlogb : Real.logb 2 (max 1 c) ≤
      (Real.log M + Real.log s) / Real.log 2 := by
    unfold Real.logb
    exact div_le_div_of_nonneg_right hlogmax hlog2.le
  have hlogM0 : 0 ≤ Real.log M := Real.log_nonneg hM1
  change (baseHalvingCount data R delta : ℝ) ≤
    baseHalvingLogConstant data.p * LS
  unfold baseHalvingLogConstant
  rw [hLS] at ⊢
  dsimp [M, cc] at hlogM0 ⊢
  calc
    (baseHalvingCount data R delta : ℝ) ≤
        (⌈Real.logb 2 (max 1 c)⌉₊ : ℝ) := hncast
    _ ≤ Real.logb 2 (max 1 c) + 1 := hceil
    _ ≤ (Real.log M + Real.log s) / Real.log 2 + 1 := by linarith
    _ ≤ (2 + (Real.log (max 1 (correctionConstant data.p)) + 1) /
          Real.log 2) * (1 + Real.log s) := by
      have hlogs0 : 0 ≤ Real.log s := Real.log_nonneg (by linarith)
      field_simp [hlog2.ne']
      nlinarith

end

end VIReference.Pilot
