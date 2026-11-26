import LeanArticleAudit.Pilot.UpperRestartTransformation
import LeanArticleAudit.Pilot.UpperCost
import LeanArticleAudit.Pilot.UpperRestartLog

/-! Pure numerical bounds for the restart schedules. -/

namespace LeanArticleAudit.Pilot

noncomputable section

universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem restartHalvingCount_le_natCeil_logb (mu delta R : ℝ)
    (hmu : 0 < mu) (hdelta : 0 < delta) (hR : 0 ≤ R) :
    restartHalvingCount mu delta R ≤
      ⌈Real.logb 2 (max 1 (mu * R / (2 * delta)))⌉₊ := by
  let c := mu * R / (2 * delta)
  let n := ⌈Real.logb 2 (max 1 c)⌉₊
  have hc : 0 < max 1 c := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hpow : max 1 c ≤ (2 : ℝ) ^ n := by
    dsimp [n]
    exact positive_le_two_pow_natCeil_logb _ hc
  have hwitness : mu * (R / (2 : ℝ) ^ n) / 2 ≤ delta := by
    have hc' : mu * R / (2 * delta) ≤ (2 : ℝ) ^ n :=
      (le_max_right 1 c).trans hpow
    have hraw : mu * R ≤ (2 * delta) * (2 : ℝ) ^ n := by
      have := (div_le_iff₀ (by positivity : 0 < 2 * delta)).1 hc'
      nlinarith
    have hdenpos : 0 < 2 * (2 : ℝ) ^ n := by positivity
    calc
      mu * (R / (2 : ℝ) ^ n) / 2 =
          (mu * R) / (2 * (2 : ℝ) ^ n) := by ring
      _ ≤ delta := (div_le_iff₀ hdenpos).2 (by nlinarith)
  rw [restartHalvingCount, dif_pos ⟨hmu, hdelta, hR⟩]
  exact Nat.find_min' (exists_restart_halving_threshold mu delta R hmu hdelta hR)
    hwitness

/-- The number of inner halvings is at most three strong-log units. -/
theorem restartHalvingCount_cast_le_strongLog
    (data : VIPublicData E) (mu delta R : ℝ)
    (hmu : 0 < mu) (hdelta : 0 < delta)
    (hR : 0 ≤ R) (hRD : R ≤ data.D) :
    (restartHalvingCount mu delta R : ℝ) ≤
      3 * strongLog data mu delta := by
  let c := mu * R / (2 * delta)
  let s := 2 + data.Lp * data.D ^ (data.p - 1) / mu +
    data.Lp * data.D ^ data.p / delta + mu * data.D / delta
  let LS := strongLog data mu delta
  have hs2 : 2 ≤ s := by
    dsimp [s]
    have h1 : 0 ≤ data.Lp * data.D ^ (data.p - 1) / mu :=
      div_nonneg (mul_nonneg data.Lp_pos.le (pow_nonneg data.D_pos.le _)) hmu.le
    have h2 : 0 ≤ data.Lp * data.D ^ data.p / delta :=
      div_nonneg (mul_nonneg data.Lp_pos.le (pow_nonneg data.D_pos.le _)) hdelta.le
    have h3 : 0 ≤ mu * data.D / delta :=
      div_nonneg (mul_nonneg hmu.le data.D_pos.le) hdelta.le
    linarith
  have hspos : 0 < s := by linarith
  have hLS : LS = 1 + Real.log s := rfl
  have hLS1 : 1 ≤ LS := by
    rw [hLS]
    linarith [Real.log_nonneg (by linarith : 1 ≤ s)]
  have hc0 : 0 ≤ c := by dsimp [c]; positivity
  have hcs : max 1 c ≤ s := by
    apply max_le
    · linarith
    · dsimp [c, s]
      have hmuR : mu * R / delta ≤ mu * data.D / delta := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hRD hmu.le) hdelta.le
      have : mu * R / (2 * delta) ≤ mu * R / delta := by
        have hmr : 0 ≤ mu * R := mul_nonneg hmu.le hR
        apply div_le_div_of_nonneg_left hmr hdelta (by linarith)
      have h1 : 0 ≤ data.Lp * data.D ^ (data.p - 1) / mu :=
        div_nonneg (mul_nonneg data.Lp_pos.le (pow_nonneg data.D_pos.le _)) hmu.le
      have h2 : 0 ≤ data.Lp * data.D ^ data.p / delta :=
        div_nonneg (mul_nonneg data.Lp_pos.le (pow_nonneg data.D_pos.le _)) hdelta.le
      linarith
  have hlog : Real.log (max 1 c) ≤ Real.log s :=
    Real.log_le_log (lt_of_lt_of_le (by norm_num) (le_max_left _ _)) hcs
  have hlog0 : 0 ≤ Real.log (max 1 c) := Real.log_nonneg (le_max_left _ _)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hceil := natCeil_cast_le_max_add_one (Real.logb 2 (max 1 c))
  have hlogb0 : 0 ≤ Real.logb 2 (max 1 c) := by
    unfold Real.logb
    positivity
  rw [max_eq_right hlogb0] at hceil
  have hn := restartHalvingCount_le_natCeil_logb mu delta R hmu hdelta hR
  have hncast : (restartHalvingCount mu delta R : ℝ) ≤
      (⌈Real.logb 2 (max 1 c)⌉₊ : ℝ) := by exact_mod_cast hn
  have hhalf : (1 / 2 : ℝ) ≤ Real.log 2 :=
    (by norm_num : (1 / 2 : ℝ) ≤ 0.6931471803).trans Real.log_two_gt_d9.le
  change (restartHalvingCount mu delta R : ℝ) ≤ 3 * LS
  calc
    _ ≤ (⌈Real.logb 2 (max 1 c)⌉₊ : ℝ) := hncast
    _ ≤ Real.logb 2 (max 1 c) + 1 := hceil
    _ ≤ 2 * Real.log s + 1 := by
      unfold Real.logb
      have hlogs0 : 0 ≤ Real.log s := Real.log_nonneg (by linarith)
      have hscale := mul_le_mul_of_nonneg_left hhalf
        (by positivity : 0 ≤ 2 * Real.log s)
      have hnum : Real.log (max 1 c) ≤
          (2 * Real.log s) * Real.log 2 := hlog.trans (by nlinarith)
      simpa [add_comm] using
        add_le_add_right ((div_le_iff₀ hlog2).2 hnum) 1
    _ ≤ 3 * LS := by rw [hLS]; linarith

/-- A restart trial contains `halvings + 1` locally capped calls.  If every
real interface cost along either branch is at most `B`, ceiling overhead adds
at most one query per call. -/
theorem restartTrialCap_cast_le_uniform
    (data : VIPublicData E) (A : ResidualSolver data)
    (alpha : ℝ) (b : ℕ) (mu delta R B : ℝ) (halvings : ℕ)
    (hfinal : ∀ R', 0 ≤ residualInterfaceCost data A.leadingConstant alpha b
        R' delta ∧
      residualInterfaceCost data A.leadingConstant alpha b R' delta ≤ B)
    (hstep : ∀ R', 0 ≤ residualInterfaceCost data A.leadingConstant alpha b
        R' (mu * R' / 2) ∧
      residualInterfaceCost data A.leadingConstant alpha b
        R' (mu * R' / 2) ≤ B) :
    (restartTrialCap data A alpha b mu delta halvings R : ℝ) ≤
      ((halvings : ℝ) + 1) * (B + 1) := by
  induction halvings generalizing R with
  | zero =>
      rw [restartTrialCap]
      simp only [Nat.cast_zero, zero_add, one_mul]
      calc
        _ ≤ residualInterfaceCost data A.leadingConstant alpha b R delta + 1 :=
          (Nat.ceil_lt_add_one (hfinal R).1).le
        _ ≤ B + 1 := by
          simpa [add_comm] using add_le_add_right (hfinal R).2 1
  | succ halvings ih =>
      rw [restartTrialCap, Nat.cast_add]
      have hhead := (Nat.ceil_lt_add_one (hstep R).1).le
      have htail := ih (R / 2)
      push_cast
      nlinarith [(hstep R).2]

/-- Prefix aggregation for the public outer doubling schedule. -/
theorem adaptiveRestartCapFrom_cast_le_uniform
    (data : VIPublicData E) (A : ResidualSolver data)
    (alpha : ℝ) (b : ℕ) (mu delta : ℝ) (center : data.X)
    (remaining j : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hcap : ∀ k, j ≤ k → k ≤ j + remaining →
      ((scheduledRestartTrialCall data A alpha b mu delta center
        (adaptiveGuessRadius data mu k)).cap : ℝ) ≤ B) :
    (adaptiveRestartCapFrom data A alpha b mu delta center remaining j : ℝ) ≤
      ((remaining : ℝ) + 1) * B := by
  induction remaining generalizing j with
  | zero =>
      simpa [adaptiveRestartCapFrom] using hcap j le_rfl (by omega)
  | succ remaining ih =>
      rw [adaptiveRestartCapFrom, Nat.cast_add]
      have hhead := hcap j le_rfl (by omega)
      have htail := ih (j + 1) (fun k hjk hkj ↦ hcap k (by omega) (by omega))
      push_cast
      nlinarith

/-- The first public radius is never smaller than `min D rho`, and all later
doubling guesses inherit this lower bound. -/
theorem min_scale_le_adaptiveGuessRadius
    (data : VIPublicData E) (mu : ℝ) (hmu : 0 < mu) (j : ℕ) :
    min data.D (baseStrongScale data mu) ≤ adaptiveGuessRadius data mu j := by
  have hmono := adaptiveGuessRadius_mono data mu hmu (Nat.zero_le j)
  simpa [adaptiveGuessRadius] using hmono

/-- Since `p-1 ≥ 1`, the diameter-to-natural-scale ratio is controlled by
the strong condition number. -/
theorem diameter_div_baseStrongScale_le
    (data : VIPublicData E) (mu : ℝ) (hmu : 0 < mu) :
    data.D / baseStrongScale data mu ≤
      1 + data.Lp * data.D ^ (data.p - 1) / mu := by
  let c := data.D / baseStrongScale data mu
  let q := data.Lp * data.D ^ (data.p - 1) / mu
  have hc : 0 < c := div_pos data.D_pos (baseStrongScale_pos data mu hmu)
  have hpow : c ^ (data.p - 1) = q := by
    dsimp [c, q]
    exact diameter_scale_pow_condition data mu hmu
  by_cases hc1 : c ≤ 1
  · change c ≤ 1 + q
    have hq : 0 ≤ data.Lp * data.D ^ (data.p - 1) / mu :=
      div_nonneg (mul_nonneg data.Lp_pos.le (pow_nonneg data.D_pos.le _)) hmu.le
    change 0 ≤ q at hq
    linarith
  · have h1c : 1 ≤ c := le_of_not_ge hc1
    have hn : 1 ≤ data.p - 1 := Nat.le_sub_of_add_le data.p_ge_two
    have hcpow : c ≤ c ^ (data.p - 1) := by
      simpa using pow_le_pow_right₀ h1c hn
    rw [hpow] at hcpow
    change c ≤ 1 + q
    linarith

/-- Every installed public guess has controlled inverse radius. -/
theorem diameter_div_adaptiveGuessRadius_le
    (data : VIPublicData E) (mu : ℝ) (hmu : 0 < mu) (j : ℕ) :
    data.D / adaptiveGuessRadius data mu j ≤
      1 + data.Lp * data.D ^ (data.p - 1) / mu := by
  let rho := baseStrongScale data mu
  let R := adaptiveGuessRadius data mu j
  have hR : 0 < R := adaptiveGuessRadius_pos data mu hmu j
  have hrho : 0 < rho := baseStrongScale_pos data mu hmu
  have hlower : min data.D rho ≤ R := min_scale_le_adaptiveGuessRadius data mu hmu j
  have hratio : data.D / R ≤ data.D / min data.D rho := by
    exact div_le_div_of_nonneg_left data.D_pos.le
      (lt_min data.D_pos hrho) hlower
  rcases le_total data.D rho with h | h
  · rw [min_eq_left h] at hratio
    have hone : data.D / data.D = 1 := div_self data.D_pos.ne'
    rw [hone] at hratio
    exact hratio.trans (by
      have hq : 0 ≤ data.Lp * data.D ^ (data.p - 1) / mu :=
        div_nonneg (mul_nonneg data.Lp_pos.le (pow_nonneg data.D_pos.le _)) hmu.le
      linarith)
  · rw [min_eq_right h] at hratio
    exact hratio.trans (diameter_div_baseStrongScale_le data mu hmu)

/-- At the least restart stopping index, the final radius is either the
unhalved public guess or is strictly larger than `delta / mu`.  Consequently
its inverse-radius term is controlled by the strong logarithm's raw terms. -/
theorem restart_final_diameter_ratio_le
    (data : VIPublicData E) (mu delta : ℝ)
    (hmu : 0 < mu) (hdelta : 0 < delta) (j : ℕ) :
    data.D / (adaptiveGuessRadius data mu j /
        (2 : ℝ) ^ restartHalvingCount mu delta
          (adaptiveGuessRadius data mu j)) ≤
      1 + data.Lp * data.D ^ (data.p - 1) / mu + mu * data.D / delta := by
  let R := adaptiveGuessRadius data mu j
  have hR : 0 < R := adaptiveGuessRadius_pos data mu hmu j
  change data.D / (R / (2 : ℝ) ^ restartHalvingCount mu delta R) ≤ _
  cases hn : restartHalvingCount mu delta R with
  | zero =>
      rw [pow_zero, div_one]
      exact (diameter_div_adaptiveGuessRadius_le data mu hmu j).trans
        (le_add_of_nonneg_right (div_nonneg (mul_nonneg hmu.le data.D_pos.le)
          hdelta.le))
  | succ n =>
      have hprior := restartHalvingCount_prior mu delta R hmu hdelta hR.le n (by
        omega)
      have hfinal : 0 < R / (2 : ℝ) ^ (n + 1) :=
        div_pos hR (pow_pos (by norm_num) _)
      have hprior' : delta < mu * (R / (2 : ℝ) ^ (n + 1)) := by
        rw [pow_succ]
        convert hprior using 1 <;> ring
      have hunit : 1 ≤ mu * (R / (2 : ℝ) ^ (n + 1)) / delta := by
        exact (le_div_iff₀ hdelta).2 (by simpa using hprior'.le)
      have hdiam : data.D ≤
          (mu * data.D / delta) * (R / (2 : ℝ) ^ (n + 1)) := by
        calc
          data.D = data.D * 1 := by ring
          _ ≤ data.D * (mu * (R / (2 : ℝ) ^ (n + 1)) / delta) :=
            mul_le_mul_of_nonneg_left hunit data.D_pos.le
          _ = (mu * data.D / delta) * (R / (2 : ℝ) ^ (n + 1)) := by ring
      have hratio : data.D / (R / (2 : ℝ) ^ (n + 1)) ≤
          mu * data.D / delta := (div_le_iff₀ hfinal).2 hdiam
      exact hratio.trans (by
        have hq : 0 ≤ data.Lp * data.D ^ (data.p - 1) / mu :=
          div_nonneg (mul_nonneg data.Lp_pos.le (pow_nonneg data.D_pos.le _)) hmu.le
        linarith)

theorem restart_stage_radius_bounds
    (data : VIPublicData E) (mu r : ℝ) (hmu : 0 < mu)
    (hr : 0 ≤ r) (hrD : r ≤ data.D)
    (k : ℕ) (hk : k ≤ adaptiveCoverCount data mu r) (i : ℕ) :
    0 < adaptiveGuessRadius data mu k / (2 : ℝ) ^ i ∧
    adaptiveGuessRadius data mu k / (2 : ℝ) ^ i ≤
      adaptiveGuessRadius data mu (adaptiveCoverCount data mu r) ∧
    adaptiveGuessRadius data mu k / (2 : ℝ) ^ i ≤ data.D := by
  let Ri := adaptiveGuessRadius data mu k / (2 : ℝ) ^ i
  have hkpos := adaptiveGuessRadius_pos data mu hmu k
  have hRi : 0 < Ri := div_pos hkpos (pow_pos (by norm_num) _)
  have hdiv : Ri ≤ adaptiveGuessRadius data mu k := by
    exact div_le_self hkpos.le (one_le_pow₀ (by norm_num))
  have hmono := adaptiveGuessRadius_mono data mu hmu hk
  have hcoverD : adaptiveGuessRadius data mu (adaptiveCoverCount data mu r) ≤ data.D :=
    min_le_left _ _
  exact ⟨hRi, hdiv.trans hmono, hdiv.trans (hmono.trans hcoverD)⟩

/-- Every nonfinal subcall has the source's actual-distance condition-number
bound. -/
theorem restart_stage_condition_le_cover
    (data : VIPublicData E) (mu r : ℝ) (hmu : 0 < mu)
    (hr : 0 ≤ r) (hrD : r ≤ data.D)
    (k : ℕ) (hk : k ≤ adaptiveCoverCount data mu r) (i : ℕ) :
    residualCondition data
        (adaptiveGuessRadius data mu k / (2 : ℝ) ^ i)
        (mu * (adaptiveGuessRadius data mu k / (2 : ℝ) ^ i) / 2) ≤
      (2 : ℝ) ^ data.p *
        (1 + data.Lp * r ^ (data.p - 1) / mu) := by
  let Ri := adaptiveGuessRadius data mu k / (2 : ℝ) ^ i
  let Rc := adaptiveGuessRadius data mu (adaptiveCoverCount data mu r)
  have hb := restart_stage_radius_bounds data mu r hmu hr hrD k hk i
  have hpow : Ri ^ (data.p - 1) ≤ Rc ^ (data.p - 1) :=
    pow_le_pow_left₀ hb.1.le hb.2.1 _
  rw [residualCondition_restart_accuracy data mu Ri hmu hb.1]
  have hscaled : 2 * data.Lp * Ri ^ (data.p - 1) / mu ≤
      2 * (data.Lp * Rc ^ (data.p - 1) / mu) := by
    have hbase := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpow data.Lp_pos.le) hmu.le
    calc
      2 * data.Lp * Ri ^ (data.p - 1) / mu =
          2 * (data.Lp * Ri ^ (data.p - 1) / mu) := by ring
      _ ≤ 2 * (data.Lp * Rc ^ (data.p - 1) / mu) :=
        mul_le_mul_of_nonneg_left hbase (by norm_num)
  calc
    _ ≤ 2 * (data.Lp * Rc ^ (data.p - 1) / mu) := hscaled
    _ ≤ 2 * ((2 : ℝ) ^ (data.p - 1) *
        (1 + data.Lp * r ^ (data.p - 1) / mu)) :=
      mul_le_mul_of_nonneg_left
        (adaptiveCoverCondition_le data mu r hmu hr hrD) (by norm_num)
    _ = (2 : ℝ) ^ data.p *
        (1 + data.Lp * r ^ (data.p - 1) / mu) := by
      have hp1 : 1 ≤ data.p := le_trans (by omega : 1 ≤ 2) data.p_ge_two
      have htwo : (2 : ℝ) ^ data.p = 2 * (2 : ℝ) ^ (data.p - 1) := by
        conv_lhs => rw [show data.p = (data.p - 1) + 1 by omega, pow_succ]
        ring
      rw [htwo]
      ring

/-- The same stage condition is bounded globally by twice the argument of
`strongLog`; this is the form used only for the logarithmic factor. -/
theorem restart_stage_condition_le_two_strongArgument
    (data : VIPublicData E) (mu delta R : ℝ)
    (hmu : 0 < mu) (hdelta : 0 < delta)
    (hR : 0 < R) (hRD : R ≤ data.D) :
    residualCondition data R (mu * R / 2) ≤
      2 * restartStrongArgument data mu delta := by
  rw [residualCondition_restart_accuracy data mu R hmu hR]
  have hpow : R ^ (data.p - 1) ≤ data.D ^ (data.p - 1) :=
    pow_le_pow_left₀ hR.le hRD _
  have hq : data.Lp * R ^ (data.p - 1) / mu ≤
      data.Lp * data.D ^ (data.p - 1) / mu :=
    div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpow data.Lp_pos.le) hmu.le
  unfold restartStrongArgument
  have hqD : 0 ≤ data.Lp * data.D ^ (data.p - 1) / mu :=
    div_nonneg (mul_nonneg data.Lp_pos.le (pow_nonneg data.D_pos.le _)) hmu.le
  have h₂ : 0 ≤ data.Lp * data.D ^ data.p / delta :=
    div_nonneg (mul_nonneg data.Lp_pos.le (pow_nonneg data.D_pos.le _)) hdelta.le
  have h₃ : 0 ≤ mu * data.D / delta :=
    div_nonneg (mul_nonneg hmu.le data.D_pos.le) hdelta.le
  calc
    2 * data.Lp * R ^ (data.p - 1) / mu =
        2 * (data.Lp * R ^ (data.p - 1) / mu) := by ring
    _ ≤ 2 * (data.Lp * data.D ^ (data.p - 1) / mu) :=
      mul_le_mul_of_nonneg_left hq (by norm_num)
    _ ≤ 2 * (2 + data.Lp * data.D ^ (data.p - 1) / mu +
        data.Lp * data.D ^ data.p / delta + mu * data.D / delta) := by
      nlinarith

/-- The final-accuracy subcall satisfies the same two condition bounds as a
nonfinal call, by the least stopping threshold. -/
theorem restart_final_condition_le_step
    (data : VIPublicData E) (mu delta R : ℝ)
    (hmu : 0 < mu) (hdelta : 0 < delta) (hR : 0 < R) :
    residualCondition data
        (R / (2 : ℝ) ^ restartHalvingCount mu delta R) delta ≤
      residualCondition data
        (R / (2 : ℝ) ^ restartHalvingCount mu delta R)
        (mu * (R / (2 : ℝ) ^ restartHalvingCount mu delta R) / 2) := by
  let Rf := R / (2 : ℝ) ^ restartHalvingCount mu delta R
  have hRf : 0 < Rf := div_pos hR (pow_pos (by norm_num) _)
  have hnum : 0 ≤ data.Lp * Rf ^ data.p :=
    mul_nonneg data.Lp_pos.le (pow_nonneg hRf.le _)
  have hsmall : 0 < mu * Rf / 2 := by positivity
  have hthreshold := restartHalvingCount_threshold mu delta R hmu hdelta hR.le
  unfold residualCondition
  exact div_le_div_of_nonneg_left hnum hsmall hthreshold

/-- Every stage through the least stopping index has an inverse-radius term
bounded by the strong logarithm's argument. -/
theorem restart_stage_diameter_ratio_le_strongArgument
    (data : VIPublicData E) (mu delta : ℝ)
    (hmu : 0 < mu) (hdelta : 0 < delta) (j i : ℕ)
    (hi : i ≤ restartHalvingCount mu delta (adaptiveGuessRadius data mu j)) :
    data.D / (adaptiveGuessRadius data mu j / (2 : ℝ) ^ i) ≤
      restartStrongArgument data mu delta := by
  let R := adaptiveGuessRadius data mu j
  let n := restartHalvingCount mu delta R
  have hR : 0 < R := adaptiveGuessRadius_pos data mu hmu j
  have hpows : (2 : ℝ) ^ i ≤ (2 : ℝ) ^ n :=
    pow_le_pow_right₀ (by norm_num) hi
  have hradii : R / (2 : ℝ) ^ n ≤ R / (2 : ℝ) ^ i := by
    exact div_le_div_of_nonneg_left hR.le (pow_pos (by norm_num) _) hpows
  have hratio : data.D / (R / (2 : ℝ) ^ i) ≤ data.D / (R / (2 : ℝ) ^ n) := by
    exact div_le_div_of_nonneg_left data.D_pos.le
      (div_pos hR (pow_pos (by norm_num) _)) hradii
  have hfinal := restart_final_diameter_ratio_le data mu delta hmu hdelta j
  change data.D / (R / (2 : ℝ) ^ i) ≤ restartStrongArgument data mu delta
  change data.D / (R / (2 : ℝ) ^ n) ≤ _ at hfinal
  refine hratio.trans (hfinal.trans ?_)
  unfold restartStrongArgument
  have hqδ : 0 ≤ data.Lp * data.D ^ data.p / delta :=
    div_nonneg (mul_nonneg data.Lp_pos.le (pow_nonneg data.D_pos.le _)) hdelta.le
  linarith

/-- Scalar conversion from the condition and logarithmic bounds of one
restart subcall to the target residual-interface shape. -/
theorem residualInterfaceCost_le_restart_majorant
    (data : VIPublicData E) (C alpha : ℝ) (b : ℕ)
    (R epsilon q c LS : ℝ)
    (hC : 0 ≤ C) (halpha0 : 0 ≤ alpha) (halpha1 : alpha ≤ 1)
    (hR : 0 < R)
    (hQ0 : 0 ≤ residualCondition data R epsilon)
    (hq : 0 ≤ q) (hc : 0 ≤ c) (hLS : 0 ≤ LS)
    (hQ : residualCondition data R epsilon ≤ c * (1 + q))
    (hlog : residualLog data R epsilon ≤ 4 * LS) :
    residualInterfaceCost data C alpha b R epsilon ≤
      (C * (1 + Real.rpow c alpha) * (4 : ℝ) ^ b) *
        (1 + Real.rpow q alpha) * LS ^ b := by
  have hqa : 0 ≤ Real.rpow q alpha := Real.rpow_nonneg hq _
  have hca : 0 ≤ Real.rpow c alpha := Real.rpow_nonneg hc _
  have hQpow : Real.rpow (residualCondition data R epsilon) alpha ≤
      Real.rpow c alpha * (1 + Real.rpow q alpha) := by
    calc
      Real.rpow (residualCondition data R epsilon) alpha ≤
          Real.rpow (c * (1 + q)) alpha :=
        Real.rpow_le_rpow hQ0 hQ halpha0
      _ = Real.rpow c alpha * Real.rpow (1 + q) alpha :=
        Real.mul_rpow hc (by positivity)
      _ ≤ Real.rpow c alpha * (Real.rpow 1 alpha + Real.rpow q alpha) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_add_le_add_rpow (by norm_num) hq halpha0 halpha1) hca
      _ = Real.rpow c alpha * (1 + Real.rpow q alpha) := by simp
  have hfactor : 1 + Real.rpow (residualCondition data R epsilon) alpha ≤
      (1 + Real.rpow c alpha) * (1 + Real.rpow q alpha) := by
    nlinarith
  have hlog0 : 0 ≤ residualLog data R epsilon := by
    have hRpos : 0 < 2 + data.D / R + residualCondition data R epsilon := by
      have hDR : 0 ≤ data.D / R := div_nonneg data.D_pos.le hR.le
      linarith
    unfold residualLog
    have := Real.log_nonneg (by
      have hDR : 0 ≤ data.D / R := div_nonneg data.D_pos.le hR.le
      linarith : 1 ≤ 2 + data.D / R + residualCondition data R epsilon)
    linarith
  have hlogpow : (residualLog data R epsilon) ^ b ≤ (4 * LS) ^ b :=
    pow_le_pow_left₀ hlog0 hlog _
  unfold residualInterfaceCost
  calc
    C * (1 + Real.rpow (residualCondition data R epsilon) alpha) *
        residualLog data R epsilon ^ b ≤
      C * ((1 + Real.rpow c alpha) * (1 + Real.rpow q alpha)) *
        (4 * LS) ^ b := by gcongr
    _ = (C * (1 + Real.rpow c alpha) * (4 : ℝ) ^ b) *
        (1 + Real.rpow q alpha) * LS ^ b := by
      rw [mul_pow]
      ring

/-- Stage-indexed cap aggregation; unlike a global uniform-radius premise,
this version is directly instantiable by the finite restart schedule. -/
theorem restartTrialCap_cast_le_stagewise
    (data : VIPublicData E) (A : ResidualSolver data)
    (alpha : ℝ) (b : ℕ) (mu delta R B : ℝ) (halvings : ℕ)
    (hfinal : 0 ≤ residualInterfaceCost data A.leadingConstant alpha b
        (R / (2 : ℝ) ^ halvings) delta ∧
      residualInterfaceCost data A.leadingConstant alpha b
        (R / (2 : ℝ) ^ halvings) delta ≤ B)
    (hstep : ∀ i < halvings,
      0 ≤ residualInterfaceCost data A.leadingConstant alpha b
          (R / (2 : ℝ) ^ i) (mu * (R / (2 : ℝ) ^ i) / 2) ∧
      residualInterfaceCost data A.leadingConstant alpha b
          (R / (2 : ℝ) ^ i) (mu * (R / (2 : ℝ) ^ i) / 2) ≤ B) :
    (restartTrialCap data A alpha b mu delta halvings R : ℝ) ≤
      ((halvings : ℝ) + 1) * (B + 1) := by
  induction halvings generalizing R with
  | zero =>
      rw [restartTrialCap]
      simp only [pow_zero, div_one] at hfinal
      simp only [Nat.cast_zero, zero_add, one_mul]
      exact (Nat.ceil_lt_add_one hfinal.1).le.trans (by
        simpa [add_comm] using add_le_add_right hfinal.2 1)
  | succ n ih =>
      rw [restartTrialCap, Nat.cast_add]
      have hhead := hstep 0 (by omega)
      simp only [pow_zero, div_one] at hhead
      have hfinal' : 0 ≤ residualInterfaceCost data A.leadingConstant alpha b
          ((R / 2) / (2 : ℝ) ^ n) delta ∧
        residualInterfaceCost data A.leadingConstant alpha b
          ((R / 2) / (2 : ℝ) ^ n) delta ≤ B := by
        convert hfinal using 1 <;> rw [pow_succ] <;> ring
      have hstep' : ∀ i < n,
          0 ≤ residualInterfaceCost data A.leadingConstant alpha b
            ((R / 2) / (2 : ℝ) ^ i)
              (mu * ((R / 2) / (2 : ℝ) ^ i) / 2) ∧
          residualInterfaceCost data A.leadingConstant alpha b
            ((R / 2) / (2 : ℝ) ^ i)
              (mu * ((R / 2) / (2 : ℝ) ^ i) / 2) ≤ B := by
        intro i hi
        have hs := hstep (i + 1) (by omega)
        convert hs using 1 <;> rw [pow_succ'] <;> ring
      have htail := ih (R / 2) hfinal' hstep'
      have hceil := (Nat.ceil_lt_add_one hhead.1).le
      push_cast
      nlinarith [hhead.2]

noncomputable def restartCallLeadingConstant
    (p : ℕ) (C alpha : ℝ) (b : ℕ) : ℝ :=
  C * (1 + Real.rpow ((2 : ℝ) ^ p) alpha) * (4 : ℝ) ^ b

noncomputable def restartLeadingConstant
    (p : ℕ) (C alpha : ℝ) (b : ℕ) : ℝ :=
  4 * (2 + 1 / Real.log 2) *
    (restartCallLeadingConstant p C alpha b + 1)

theorem restartCallLeadingConstant_nonneg
    (p : ℕ) (C alpha : ℝ) (b : ℕ) (hC : 0 ≤ C) :
    0 ≤ restartCallLeadingConstant p C alpha b := by
  unfold restartCallLeadingConstant
  exact mul_nonneg
    (mul_nonneg hC (add_nonneg (by norm_num)
      (Real.rpow_nonneg (pow_nonneg (by norm_num) _) _)))
    (pow_nonneg (by norm_num) _)

theorem restart_stage_interfaceCost_le
    (data : VIPublicData E) (A : ResidualSolver data)
    (alpha : ℝ) (b : ℕ) (mu delta r : ℝ)
    (hmu : 0 < mu) (hdelta : 0 < delta)
    (hr : 0 ≤ r) (hrD : r ≤ data.D)
    (halpha0 : 0 ≤ alpha) (halpha1 : alpha ≤ 1)
    (k : ℕ) (hk : k ≤ adaptiveCoverCount data mu r)
    (i : ℕ) (hi : i < restartHalvingCount mu delta
      (adaptiveGuessRadius data mu k)) :
    residualInterfaceCost data A.leadingConstant alpha b
        (adaptiveGuessRadius data mu k / (2 : ℝ) ^ i)
        (mu * (adaptiveGuessRadius data mu k / (2 : ℝ) ^ i) / 2) ≤
      restartCallLeadingConstant data.p A.leadingConstant alpha b *
        (1 + Real.rpow (data.Lp * r ^ (data.p - 1) / mu) alpha) *
        (strongLog data mu delta) ^ b := by
  let Ri := adaptiveGuessRadius data mu k / (2 : ℝ) ^ i
  let q := data.Lp * r ^ (data.p - 1) / mu
  let c := (2 : ℝ) ^ data.p
  let LS := strongLog data mu delta
  have hb := restart_stage_radius_bounds data mu r hmu hr hrD k hk i
  have hQ0 : 0 ≤ residualCondition data Ri (mu * Ri / 2) := by
    unfold residualCondition
    exact div_nonneg (mul_nonneg data.Lp_pos.le (pow_nonneg hb.1.le _))
      (div_nonneg (mul_nonneg hmu.le hb.1.le) (by norm_num))
  have hq : 0 ≤ q := by
    dsimp [q]
    exact div_nonneg (mul_nonneg data.Lp_pos.le (pow_nonneg hr _)) hmu.le
  have hQcover : residualCondition data Ri (mu * Ri / 2) ≤ c * (1 + q) := by
    dsimp [Ri, c, q]
    exact restart_stage_condition_le_cover data mu r hmu hr hrD k hk i
  have hglobal := restart_stage_condition_le_two_strongArgument data mu delta Ri
    hmu hdelta hb.1 hb.2.2
  have hinv := restart_stage_diameter_ratio_le_strongArgument data mu delta
    hmu hdelta k i hi.le
  have hlog := residualLog_le_four_strongLog_of_bounds data mu delta Ri
    (mu * Ri / 2) hmu hdelta hb.1
      (div_pos (mul_pos hmu hb.1) (by norm_num)) hinv hglobal
  have hmajor := residualInterfaceCost_le_restart_majorant data A.leadingConstant
    alpha b Ri (mu * Ri / 2) q c LS A.leadingConstant_pos.le halpha0
      halpha1 hb.1 hQ0 hq (pow_nonneg (by norm_num) _)
      (le_trans (by norm_num) (strongLog_one_le data mu delta hmu hdelta))
      hQcover hlog
  simpa [restartCallLeadingConstant, q, c, LS, Ri, mul_assoc] using hmajor

theorem restart_final_interfaceCost_le
    (data : VIPublicData E) (A : ResidualSolver data)
    (alpha : ℝ) (b : ℕ) (mu delta r : ℝ)
    (hmu : 0 < mu) (hdelta : 0 < delta)
    (hr : 0 ≤ r) (hrD : r ≤ data.D)
    (halpha0 : 0 ≤ alpha) (halpha1 : alpha ≤ 1)
    (k : ℕ) (hk : k ≤ adaptiveCoverCount data mu r) :
    let n := restartHalvingCount mu delta (adaptiveGuessRadius data mu k)
    residualInterfaceCost data A.leadingConstant alpha b
        (adaptiveGuessRadius data mu k / (2 : ℝ) ^ n) delta ≤
      restartCallLeadingConstant data.p A.leadingConstant alpha b *
        (1 + Real.rpow (data.Lp * r ^ (data.p - 1) / mu) alpha) *
        (strongLog data mu delta) ^ b := by
  dsimp only
  let R := adaptiveGuessRadius data mu k
  let n := restartHalvingCount mu delta R
  let Rf := R / (2 : ℝ) ^ n
  let q := data.Lp * r ^ (data.p - 1) / mu
  let c := (2 : ℝ) ^ data.p
  let LS := strongLog data mu delta
  have hb := restart_stage_radius_bounds data mu r hmu hr hrD k hk n
  have hQ0 : 0 ≤ residualCondition data Rf delta := by
    unfold residualCondition
    exact div_nonneg (mul_nonneg data.Lp_pos.le (pow_nonneg hb.1.le _)) hdelta.le
  have hq : 0 ≤ q := by
    dsimp [q]
    exact div_nonneg (mul_nonneg data.Lp_pos.le (pow_nonneg hr _)) hmu.le
  have hstepCover := restart_stage_condition_le_cover data mu r hmu hr hrD k hk n
  have hfinalStep := restart_final_condition_le_step data mu delta R hmu hdelta
    (adaptiveGuessRadius_pos data mu hmu k)
  have hQcover : residualCondition data Rf delta ≤ c * (1 + q) := by
    exact hfinalStep.trans (by simpa [R, n, Rf, c, q] using hstepCover)
  have hstepGlobal := restart_stage_condition_le_two_strongArgument data mu delta Rf
    hmu hdelta hb.1 hb.2.2
  have hglobal : residualCondition data Rf delta ≤
      2 * restartStrongArgument data mu delta := hfinalStep.trans (by
        simpa [R, n, Rf] using hstepGlobal)
  have hinv := restart_stage_diameter_ratio_le_strongArgument data mu delta
    hmu hdelta k n le_rfl
  have hlog := residualLog_le_four_strongLog_of_bounds data mu delta Rf delta
    hmu hdelta hb.1 hdelta (by simpa [R, n, Rf] using hinv) hglobal
  have hmajor := residualInterfaceCost_le_restart_majorant data A.leadingConstant
    alpha b Rf delta q c LS A.leadingConstant_pos.le halpha0 halpha1 hb.1
      hQ0 hq (pow_nonneg (by norm_num) _)
      (le_trans (by norm_num) (strongLog_one_le data mu delta hmu hdelta))
      hQcover hlog
  simpa [restartCallLeadingConstant, R, n, Rf, q, c, LS, mul_assoc] using hmajor

theorem residualInterfaceCost_nonneg_of_pos
    (data : VIPublicData E) (C alpha : ℝ) (b : ℕ) (R epsilon : ℝ)
    (hC : 0 ≤ C) (hR : 0 < R) (hepsilon : 0 < epsilon) :
    0 ≤ residualInterfaceCost data C alpha b R epsilon := by
  unfold residualInterfaceCost
  exact mul_nonneg
    (mul_nonneg hC (add_nonneg (by norm_num)
      (Real.rpow_nonneg (by
        unfold residualCondition
        exact div_nonneg
          (mul_nonneg data.Lp_pos.le (pow_nonneg hR.le _)) hepsilon.le) _)))
    (pow_nonneg
      ((by norm_num : (0 : ℝ) ≤ 1).trans
        (residualLog_one_le data R epsilon hR hepsilon)) _)

/-- Cost of one complete scheduled restart trial at any radius guess up to
the first covering guess. -/
theorem scheduledRestartTrialCap_le
    (data : VIPublicData E) (A : ResidualSolver data)
    (alpha : ℝ) (b : ℕ) (mu delta r : ℝ) (center : data.X)
    (hmu : 0 < mu) (hdelta : 0 < delta)
    (hr : 0 ≤ r) (hrD : r ≤ data.D)
    (halpha0 : 0 ≤ alpha) (halpha1 : alpha ≤ 1)
    (k : ℕ) (hk : k ≤ adaptiveCoverCount data mu r) :
    ((scheduledRestartTrialCall data A alpha b mu delta center
      (adaptiveGuessRadius data mu k)).cap : ℝ) ≤
      4 * (restartCallLeadingConstant data.p A.leadingConstant alpha b + 1) *
        (1 + Real.rpow (data.Lp * r ^ (data.p - 1) / mu) alpha) *
        (strongLog data mu delta) ^ (b + 1) := by
  let R := adaptiveGuessRadius data mu k
  let n := restartHalvingCount mu delta R
  let K := restartCallLeadingConstant data.p A.leadingConstant alpha b
  let qα := Real.rpow (data.Lp * r ^ (data.p - 1) / mu) alpha
  let LS := strongLog data mu delta
  let B := K * (1 + qα) * LS ^ b
  have hR : 0 < R := adaptiveGuessRadius_pos data mu hmu k
  have hLS : 1 ≤ LS := strongLog_one_le data mu delta hmu hdelta
  have hK : 0 ≤ K := restartCallLeadingConstant_nonneg _ _ _ _ A.leadingConstant_pos.le
  have hq : 0 ≤ data.Lp * r ^ (data.p - 1) / mu :=
    div_nonneg (mul_nonneg data.Lp_pos.le (pow_nonneg hr _)) hmu.le
  have hqα : 0 ≤ qα := Real.rpow_nonneg hq _
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hfinalUpper : residualInterfaceCost data A.leadingConstant alpha b
      (R / (2 : ℝ) ^ n) delta ≤ B := by
    dsimp [R, n, B, K, qα, LS]
    exact restart_final_interfaceCost_le data A alpha b mu delta r hmu hdelta
      hr hrD halpha0 halpha1 k hk
  have hfinalPos : 0 < R / (2 : ℝ) ^ n := div_pos hR (pow_pos (by norm_num) _)
  have hfinal : 0 ≤ residualInterfaceCost data A.leadingConstant alpha b
      (R / (2 : ℝ) ^ n) delta ∧
      residualInterfaceCost data A.leadingConstant alpha b
        (R / (2 : ℝ) ^ n) delta ≤ B :=
    ⟨residualInterfaceCost_nonneg_of_pos data A.leadingConstant alpha b _ _
      A.leadingConstant_pos.le hfinalPos hdelta, hfinalUpper⟩
  have hstep : ∀ i < n,
      0 ≤ residualInterfaceCost data A.leadingConstant alpha b
          (R / (2 : ℝ) ^ i) (mu * (R / (2 : ℝ) ^ i) / 2) ∧
      residualInterfaceCost data A.leadingConstant alpha b
          (R / (2 : ℝ) ^ i) (mu * (R / (2 : ℝ) ^ i) / 2) ≤ B := by
    intro i hi
    have hRi : 0 < R / (2 : ℝ) ^ i := div_pos hR (pow_pos (by norm_num) _)
    constructor
    · exact residualInterfaceCost_nonneg_of_pos data A.leadingConstant alpha b _ _
        A.leadingConstant_pos.le hRi (div_pos (mul_pos hmu hRi) (by norm_num))
    · dsimp [R, n, B, K, qα, LS] at hi ⊢
      exact restart_stage_interfaceCost_le data A alpha b mu delta r hmu hdelta
        hr hrD halpha0 halpha1 k hk i hi
  have hcap := restartTrialCap_cast_le_stagewise data A alpha b mu delta R B n
    hfinal hstep
  have hn := restartHalvingCount_cast_le_strongLog data mu delta R hmu hdelta
    hR.le (min_le_left _ _)
  have hn1 : (n : ℝ) + 1 ≤ 4 * LS := by
    dsimp [n, R, LS] at hn ⊢
    linarith [strongLog_one_le data mu delta hmu hdelta]
  have hX : 1 ≤ (1 + qα) * LS ^ b := by
    have hpow : 1 ≤ LS ^ b := one_le_pow₀ hLS
    nlinarith
  have hB1 : B + 1 ≤ (K + 1) * (1 + qα) * LS ^ b := by
    dsimp [B]
    nlinarith
  dsimp [scheduledRestartTrialCall, restartTrialCall]
  calc
    (restartTrialCap data A alpha b mu delta n R : ℝ) ≤
        ((n : ℝ) + 1) * (B + 1) := hcap
    _ ≤ (4 * LS) * ((K + 1) * (1 + qα) * LS ^ b) := by gcongr
    _ = 4 * (K + 1) * (1 + qα) * LS ^ (b + 1) := by
      rw [pow_succ]
      ring
    _ = 4 * (restartCallLeadingConstant data.p A.leadingConstant alpha b + 1) *
        (1 + Real.rpow (data.Lp * r ^ (data.p - 1) / mu) alpha) *
        (strongLog data mu delta) ^ (b + 1) := rfl

/-- Canonical prefix cost at the first radius covering the unknown true
distance.  This is the numerical headline consumed by the executable restart
transformation. -/
theorem adaptiveRestartPrefixCap_le
    (data : VIPublicData E) (A : ResidualSolver data)
    (alpha : ℝ) (b : ℕ) (mu delta r : ℝ) (center : data.X)
    (hmu : 0 < mu) (hdelta : 0 < delta)
    (hr : 0 ≤ r) (hrD : r ≤ data.D)
    (halpha0 : 0 ≤ alpha) (halpha1 : alpha ≤ 1) :
    (adaptiveRestartCapFrom data A alpha b mu delta center
        (adaptiveCoverCount data mu r) 0 : ℝ) ≤
      restartLeadingConstant data.p A.leadingConstant alpha b *
        (1 + Real.rpow (data.Lp * r ^ (data.p - 1) / mu) alpha) *
        (strongLog data mu delta) ^ (b + 2) := by
  let j := adaptiveCoverCount data mu r
  let K := restartCallLeadingConstant data.p A.leadingConstant alpha b
  let qα := Real.rpow (data.Lp * r ^ (data.p - 1) / mu) alpha
  let LS := strongLog data mu delta
  let Ag := 2 + 1 / Real.log 2
  let B := 4 * (K + 1) * (1 + qα) * LS ^ (b + 1)
  have hLS : 1 ≤ LS := strongLog_one_le data mu delta hmu hdelta
  have hK : 0 ≤ K := restartCallLeadingConstant_nonneg _ _ _ _
    A.leadingConstant_pos.le
  have hq : 0 ≤ data.Lp * r ^ (data.p - 1) / mu :=
    div_nonneg (mul_nonneg data.Lp_pos.le (pow_nonneg hr _)) hmu.le
  have hqα : 0 ≤ qα := Real.rpow_nonneg hq _
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hprefix := adaptiveRestartCapFrom_cast_le_uniform data A alpha b mu delta
    center j 0 B hB (by
      intro k _hk0 hk
      have hk' : k ≤ adaptiveCoverCount data mu r := by
        dsimp [j] at hk
        omega
      exact scheduledRestartTrialCap_le data A alpha b mu delta r center hmu hdelta
        hr hrD halpha0 halpha1 k hk')
  have hguesses := adaptiveCoverCount_add_one_le_strongLog data mu delta r
    hmu hdelta hr hrD
  change (j : ℝ) + 1 ≤ Ag * LS at hguesses
  have hAg : 0 ≤ Ag := by
    dsimp [Ag]
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  change (adaptiveRestartCapFrom data A alpha b mu delta center j 0 : ℝ) ≤ _
  calc
    _ ≤ ((j : ℝ) + 1) * B := hprefix
    _ ≤ (Ag * LS) * B := mul_le_mul_of_nonneg_right hguesses hB
    _ = restartLeadingConstant data.p A.leadingConstant alpha b *
        (1 + Real.rpow (data.Lp * r ^ (data.p - 1) / mu) alpha) *
        (strongLog data mu delta) ^ (b + 2) := by
      dsimp [B, Ag, K, qα, LS, restartLeadingConstant]
      rw [pow_succ, pow_succ]
      ring

end

end LeanArticleAudit.Pilot
