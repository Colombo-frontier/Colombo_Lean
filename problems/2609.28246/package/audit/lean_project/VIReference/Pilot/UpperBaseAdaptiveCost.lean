import VIReference.Pilot.UpperBaseSuccess
import VIReference.Pilot.UpperCost
import VIReference.Pilot.UpperBaseCost
import Mathlib.Analysis.MeanInequalitiesPow

open Set
open scoped RealInnerProductSpace BigOperators

namespace VIReference.Pilot
noncomputable section
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_adaptive_guess_cover (data : VIPublicData E) (mu r : ℝ)
    (hmu : 0 < mu) (hr : 0 ≤ r) (hrD : r ≤ data.D) :
    ∃ j ≤ adaptiveGuessCount data mu, r ≤ adaptiveGuessRadius data mu j := by
  exact ⟨adaptiveGuessCount data mu, le_rfl, by
    rw [adaptiveGuessRadius_last data mu hmu]
    exact hrD⟩

/-- Analytical first covering index. It is not supplied to the implementation;
it only names the stopping prefix in the cost proof. -/
noncomputable def adaptiveCoverCount (data : VIPublicData E) (mu r : ℝ) : ℕ :=
  if h : ∃ j ≤ adaptiveGuessCount data mu,
      r ≤ adaptiveGuessRadius data mu j then Nat.find h else 0

theorem adaptiveCoverCount_le (data : VIPublicData E) (mu r : ℝ)
    (hmu : 0 < mu) (hr : 0 ≤ r) (hrD : r ≤ data.D) :
    adaptiveCoverCount data mu r ≤ adaptiveGuessCount data mu := by
  let h := exists_adaptive_guess_cover data mu r hmu hr hrD
  rw [adaptiveCoverCount, dif_pos h]
  exact (Nat.find_spec h).1

theorem adaptiveCoverCount_covers (data : VIPublicData E) (mu r : ℝ)
    (hmu : 0 < mu) (hr : 0 ≤ r) (hrD : r ≤ data.D) :
    r ≤ adaptiveGuessRadius data mu (adaptiveCoverCount data mu r) := by
  let h := exists_adaptive_guess_cover data mu r hmu hr hrD
  rw [adaptiveCoverCount, dif_pos h]
  exact (Nat.find_spec h).2

theorem adaptiveCoverCount_prior_lt (data : VIPublicData E) (mu r : ℝ)
    (hmu : 0 < mu) (hr : 0 ≤ r) (hrD : r ≤ data.D)
    (j : ℕ) (hj : j < adaptiveCoverCount data mu r) :
    adaptiveGuessRadius data mu j < r := by
  let h := exists_adaptive_guess_cover data mu r hmu hr hrD
  rw [adaptiveCoverCount, dif_pos h] at hj
  exact lt_of_not_ge (fun hjcover => Nat.find_min h hj
    ⟨(Nat.lt_of_lt_of_le hj (Nat.find_spec h).1).le, hjcover⟩)

theorem adaptiveGuessRadius_succ_le_two (data : VIPublicData E)
    (mu : ℝ) (hmu : 0 < mu) (j : ℕ) :
    adaptiveGuessRadius data mu (j + 1) ≤
      2 * adaptiveGuessRadius data mu j := by
  unfold adaptiveGuessRadius
  have hrho : 0 < baseStrongScale data mu := baseStrongScale_pos data mu hmu
  by_cases hD : data.D ≤ (2 : ℝ) ^ j * baseStrongScale data mu
  · rw [min_eq_left hD]
    have hleft : min data.D ((2 : ℝ) ^ (j + 1) * baseStrongScale data mu) ≤
        data.D := min_le_left _ _
    linarith [data.D_pos]
  · have hpow : (2 : ℝ) ^ j * baseStrongScale data mu ≤ data.D := le_of_not_ge hD
    rw [min_eq_right hpow]
    calc
      min data.D ((2 : ℝ) ^ (j + 1) * baseStrongScale data mu) ≤
          (2 : ℝ) ^ (j + 1) * baseStrongScale data mu :=
        min_le_right _ _
      _ = 2 * ((2 : ℝ) ^ j * baseStrongScale data mu) := by rw [pow_succ]; ring

theorem adaptiveGuessRadius_mono (data : VIPublicData E) (mu : ℝ)
    (hmu : 0 < mu) : Monotone (adaptiveGuessRadius data mu) := by
  intro i j hij
  unfold adaptiveGuessRadius
  apply min_le_min_left
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hij)
    (baseStrongScale_pos data mu hmu).le

theorem adaptiveCoverRadius_le_two_max (data : VIPublicData E) (mu r : ℝ)
    (hmu : 0 < mu) (hr : 0 ≤ r) (hrD : r ≤ data.D) :
    adaptiveGuessRadius data mu (adaptiveCoverCount data mu r) ≤
      2 * max r (baseStrongScale data mu) := by
  cases hk : adaptiveCoverCount data mu r with
  | zero =>
      have hguess : adaptiveGuessRadius data mu 0 ≤ baseStrongScale data mu := by
        unfold adaptiveGuessRadius
        simpa using min_le_right data.D (baseStrongScale data mu)
      exact hguess.trans (by
        have := le_max_right r (baseStrongScale data mu)
        linarith [baseStrongScale_pos data mu hmu])
  | succ k =>
      have hprior := adaptiveCoverCount_prior_lt data mu r hmu hr hrD k (by omega)
      have hstep := adaptiveGuessRadius_succ_le_two data mu hmu k
      have hrmax : r ≤ max r (baseStrongScale data mu) := le_max_left _ _
      exact hstep.trans (mul_le_mul_of_nonneg_left (hprior.le.trans hrmax) (by norm_num))

theorem adaptiveGuessCount_le_natCeil_logb (data : VIPublicData E)
    (mu : ℝ) (hmu : 0 < mu) :
    adaptiveGuessCount data mu ≤
      ⌈Real.logb 2 (data.D / baseStrongScale data mu)⌉₊ := by
  let rho := baseStrongScale data mu
  have hrho : 0 < rho := baseStrongScale_pos data mu hmu
  have hc : 0 < data.D / rho := div_pos data.D_pos hrho
  let n : ℕ := ⌈Real.logb 2 (data.D / rho)⌉₊
  have hpow := positive_le_two_pow_natCeil_logb (data.D / rho) hc
  have hreach : data.D ≤ (2 : ℝ) ^ n * rho := by
    have := mul_le_mul_of_nonneg_right hpow hrho.le
    rw [div_mul_cancel₀ data.D hrho.ne'] at this
    exact this
  rw [adaptiveGuessCount, dif_pos hmu]
  exact Nat.find_min' (exists_doubling_reaches_diameter data mu hmu) hreach

/-- The actual no-distance solver succeeds at the first analytical covering
guess and pays only the corresponding prefix, not the later installed caps. -/
theorem baseStrongSolver_succeeds_at_first_cover
    (data : VIPublicData E) (G : E → E)
    (oracle : FeasibleExactSymmetricJetOracle data G)
    (hG : IsAdmissibleOperator data G)
    (center : data.X) (mu delta : ℝ)
    (hmu : 0 < mu) (hdelta : 0 < delta)
    (hstrong : StronglyMonotoneOn data G mu)
    (zStar : E) (hz : IsVISolution data G zStar) :
    ∃ used cert,
      ((baseStrongSolver data).solve center mu delta).execute data G oracle =
        .finished used (some cert) ∧
      cert.IsVerifiedFor data G delta ∧
      used ≤ adaptiveBaseCapFrom data mu delta center
        (adaptiveCoverCount data mu ‖center.1 - zStar‖) 0 := by
  have hr : 0 ≤ ‖center.1 - zStar‖ := norm_nonneg _
  have hrD : ‖center.1 - zStar‖ ≤ data.D := by
    simpa [dist_eq_norm] using data.diameter_le center.1 center.2 zStar hz.1
  exact baseStrongSolver_succeeds_at_guess data G oracle hG center mu delta hmu
    hdelta hstrong zStar hz (adaptiveCoverCount data mu ‖center.1 - zStar‖)
      (adaptiveCoverCount_le data mu _ hmu hr hrD)
      (adaptiveCoverCount_covers data mu _ hmu hr hrD)

/-- Crude but explicit prefix aggregation: `remaining + 1` adaptive trials
cost at most that many copies of any uniform per-trial bound. -/
theorem adaptiveBaseCapFrom_cast_le_uniform
    (data : VIPublicData E) (mu delta : ℝ) (center : data.X)
    (remaining j : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hcap : ∀ k, j ≤ k → k ≤ j + remaining →
      ((scheduledBaseTrialCall data mu delta center
        (adaptiveGuessRadius data mu k)).cap : ℝ) ≤ B) :
    (adaptiveBaseCapFrom data mu delta center remaining j : ℝ) ≤
      ((remaining : ℝ) + 1) * B := by
  induction remaining generalizing j with
  | zero =>
      simpa [adaptiveBaseCapFrom] using hcap j le_rfl (by omega)
  | succ remaining ih =>
      rw [adaptiveBaseCapFrom, Nat.cast_add]
      have hhead := hcap j le_rfl (by omega)
      have htail := ih (j + 1) (fun k hjk hkj ↦ hcap k (by omega) (by omega))
      rw [Nat.cast_add, Nat.cast_one]
      nlinarith


theorem baseStrongScale_pow (data : VIPublicData E) (mu : ℝ) (hmu : 0 < mu) :
    (baseStrongScale data mu) ^ (data.p - 1) = mu / data.Lp := by
  unfold baseStrongScale
  have hn : data.p - 1 ≠ 0 :=
    Nat.sub_ne_zero_iff_lt.mpr (lt_of_lt_of_le (by omega : 1 < 2) data.p_ge_two)
  convert Real.rpow_inv_natCast_pow (div_nonneg hmu.le data.Lp_pos.le) hn using 1
  simp [one_div]

theorem baseStrongScale_condition_eq_one (data : VIPublicData E)
    (mu : ℝ) (hmu : 0 < mu) :
    data.Lp * (baseStrongScale data mu) ^ (data.p - 1) / mu = 1 := by
  rw [baseStrongScale_pow data mu hmu]
  field_simp [data.Lp_pos.ne', hmu.ne']

theorem max_pow_le_add_pow (a b : ℝ) (n : ℕ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    max a b ^ n ≤ a ^ n + b ^ n := by
  rcases le_total a b with hab | hba
  · rw [max_eq_right hab]
    exact le_add_of_nonneg_left (pow_nonneg ha _)
  · rw [max_eq_left hba]
    exact le_add_of_nonneg_right (pow_nonneg hb _)

theorem adaptiveCoverCondition_le (data : VIPublicData E) (mu r : ℝ)
    (hmu : 0 < mu) (hr : 0 ≤ r) (hrD : r ≤ data.D) :
    data.Lp * (adaptiveGuessRadius data mu (adaptiveCoverCount data mu r)) ^
        (data.p - 1) / mu ≤
      (2 : ℝ) ^ (data.p - 1) *
        (1 + data.Lp * r ^ (data.p - 1) / mu) := by
  let rho := baseStrongScale data mu
  let R := adaptiveGuessRadius data mu (adaptiveCoverCount data mu r)
  have hrho : 0 ≤ rho := (baseStrongScale_pos data mu hmu).le
  have hR : 0 ≤ R := (adaptiveGuessRadius_pos data mu hmu _).le
  have hRbound : R ≤ 2 * max r rho := adaptiveCoverRadius_le_two_max data mu r hmu hr hrD
  have hpow : R ^ (data.p - 1) ≤ (2 * max r rho) ^ (data.p - 1) :=
    pow_le_pow_left₀ hR hRbound _
  have hmax : max r rho ^ (data.p - 1) ≤
      r ^ (data.p - 1) + rho ^ (data.p - 1) :=
    max_pow_le_add_pow r rho _ hr hrho
  have hscale : data.Lp * rho ^ (data.p - 1) / mu = 1 := by
    dsimp [rho]
    exact baseStrongScale_condition_eq_one data mu hmu
  calc
    data.Lp * R ^ (data.p - 1) / mu ≤
        data.Lp * (2 * max r rho) ^ (data.p - 1) / mu := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpow data.Lp_pos.le) hmu.le
    _ = (2 : ℝ) ^ (data.p - 1) *
        (data.Lp * max r rho ^ (data.p - 1) / mu) := by rw [mul_pow]; ring
    _ ≤ (2 : ℝ) ^ (data.p - 1) *
        (data.Lp * (r ^ (data.p - 1) + rho ^ (data.p - 1)) / mu) := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by norm_num) _)
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hmax data.Lp_pos.le) hmu.le
    _ = (2 : ℝ) ^ (data.p - 1) *
        (1 + data.Lp * r ^ (data.p - 1) / mu) := by
      rw [mul_add, add_div, ← hscale]
      ring

noncomputable def baseCoverHalvingConstant (p : ℕ) : ℝ :=
  baseHalvingLeadingConstant p *
    Real.rpow ((2 : ℝ) ^ (p - 1)) (baseHalvingExponent p)

theorem baseHalvingExponent_nonneg (p : ℕ) : 0 ≤ baseHalvingExponent p := by
  unfold baseHalvingExponent
  positivity

theorem baseHalvingExponent_le_one (p : ℕ) (hp : 2 ≤ p) :
    baseHalvingExponent p ≤ 1 := by
  unfold baseHalvingExponent
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  rw [div_le_one (by positivity : (0 : ℝ) < p + 1)]
  linarith

theorem cover_halvingThreshold_le (data : VIPublicData E) (mu r : ℝ)
    (hmu : 0 < mu) (hr : 0 ≤ r) (hrD : r ≤ data.D) :
    halvingThreshold data.p data.Lp
        (adaptiveGuessRadius data mu (adaptiveCoverCount data mu r)) mu ≤
      baseCoverHalvingConstant data.p *
        (1 + Real.rpow (data.Lp * r ^ (data.p - 1) / mu)
          (baseHalvingExponent data.p)) := by
  let R := adaptiveGuessRadius data mu (adaptiveCoverCount data mu r)
  let q := data.Lp * r ^ (data.p - 1) / mu
  let c := (2 : ℝ) ^ (data.p - 1)
  let gamma := baseHalvingExponent data.p
  have hR : 0 ≤ R := (adaptiveGuessRadius_pos data mu hmu _).le
  have hq : 0 ≤ q := by
    dsimp [q]
    exact div_nonneg (mul_nonneg data.Lp_pos.le (pow_nonneg hr _)) hmu.le
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hgamma0 : 0 ≤ gamma := baseHalvingExponent_nonneg data.p
  have hgamma1 : gamma ≤ 1 := baseHalvingExponent_le_one data.p data.p_ge_two
  have hcond : data.Lp * R ^ (data.p - 1) / mu ≤ c * (1 + q) := by
    dsimp [R, c, q]
    exact adaptiveCoverCondition_le data mu r hmu hr hrD
  have hrpow : Real.rpow (data.Lp * R ^ (data.p - 1) / mu) gamma ≤
      Real.rpow c gamma * (1 + Real.rpow q gamma) := by
    calc
      Real.rpow (data.Lp * R ^ (data.p - 1) / mu) gamma ≤
          Real.rpow (c * (1 + q)) gamma := by
        exact Real.rpow_le_rpow
          (div_nonneg (mul_nonneg data.Lp_pos.le (pow_nonneg hR _)) hmu.le)
          hcond hgamma0
      _ = Real.rpow c gamma * Real.rpow (1 + q) gamma :=
        Real.mul_rpow hc (by positivity)
      _ ≤ Real.rpow c gamma * (Real.rpow 1 gamma + Real.rpow q gamma) := by
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_add_le_add_rpow (by norm_num) hq hgamma0 hgamma1)
          (Real.rpow_nonneg hc _)
      _ = Real.rpow c gamma * (1 + Real.rpow q gamma) := by
        simp
  rw [halvingThreshold_factor data.p data.Lp R mu data.Lp_pos.le hR hmu]
  unfold baseCoverHalvingConstant
  dsimp [gamma, c, q] at hrpow ⊢
  rw [mul_assoc]
  have hbeta : 0 ≤ tensorBetaCoefficient data.p := by
    unfold tensorBetaCoefficient
    exact div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
      (Nat.cast_nonneg _)
  exact mul_le_mul_of_nonneg_left hrpow (by
    unfold baseHalvingLeadingConstant
    exact Real.rpow_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hbeta)
        (Real.rpow_nonneg (by norm_num) _)) _)

theorem adaptiveGuess_halvingThreshold_le_cover_bound
    (data : VIPublicData E) (mu r : ℝ)
    (hmu : 0 < mu) (hr : 0 ≤ r) (hrD : r ≤ data.D)
    (j : ℕ) (hj : j ≤ adaptiveCoverCount data mu r) :
    halvingThreshold data.p data.Lp (adaptiveGuessRadius data mu j) mu ≤
      baseCoverHalvingConstant data.p *
        (1 + Real.rpow (data.Lp * r ^ (data.p - 1) / mu)
          (baseHalvingExponent data.p)) := by
  exact (halvingThreshold_mono_radius data.p data.Lp mu
      (adaptiveGuessRadius data mu j)
      (adaptiveGuessRadius data mu (adaptiveCoverCount data mu r))
      data.Lp_pos.le hmu (adaptiveGuessRadius_pos data mu hmu j).le
      (adaptiveGuessRadius_mono data mu hmu hj)).trans
    (cover_halvingThreshold_le data mu r hmu hr hrD)

theorem adaptivePrefixCost_of_count_bounds
    (data : VIPublicData E) (mu delta r : ℝ)
    (center : data.X) (hmu : 0 < mu) (hdelta : 0 < delta)
    (hr : 0 ≤ r) (hrD : r ≤ data.D)
    (LS Aguess Ahalve : ℝ) (hLS : 1 ≤ LS)
    (hAg : 0 ≤ Aguess) (hAh : 0 ≤ Ahalve)
    (hguesses : ((adaptiveCoverCount data mu r : ℝ) + 1) ≤ Aguess * LS)
    (hhalvings : ∀ k ≤ adaptiveCoverCount data mu r,
      (baseHalvingCount data (adaptiveGuessRadius data mu k) delta : ℝ) ≤
        Ahalve * LS) :
    (adaptiveBaseCapFrom data mu delta center (adaptiveCoverCount data mu r) 0 : ℝ) ≤
      (2 * Aguess * (1 + Ahalve) * (baseCoverHalvingConstant data.p + 1)) *
        (1 + Real.rpow (data.Lp * r ^ (data.p - 1) / mu)
          (baseHalvingExponent data.p)) * LS ^ 2 := by
  let qpow := Real.rpow (data.Lp * r ^ (data.p - 1) / mu)
    (baseHalvingExponent data.p)
  let C := baseCoverHalvingConstant data.p
  let B := 2 + 2 * (Ahalve * LS) * (C * (1 + qpow) + 1)
  have hqbase : 0 ≤ data.Lp * r ^ (data.p - 1) / mu :=
    div_nonneg (mul_nonneg data.Lp_pos.le (pow_nonneg hr _)) hmu.le
  have hqpow : 0 ≤ qpow := Real.rpow_nonneg hqbase _
  have hC : 0 ≤ C := by
    unfold C baseCoverHalvingConstant
    have hbeta : 0 ≤ tensorBetaCoefficient data.p := by
      unfold tensorBetaCoefficient
      positivity
    have hlead : 0 ≤ baseHalvingLeadingConstant data.p := by
      unfold baseHalvingLeadingConstant
      exact Real.rpow_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) hbeta)
          (Real.rpow_nonneg (by norm_num) _)) _
    exact mul_nonneg hlead (Real.rpow_nonneg (pow_nonneg (by norm_num) _) _)
  have hLS0 : 0 ≤ LS := le_trans (by norm_num) hLS
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hprefix :
      (adaptiveBaseCapFrom data mu delta center
        (adaptiveCoverCount data mu r) 0 : ℝ) ≤
        ((adaptiveCoverCount data mu r : ℝ) + 1) * B := by
    apply adaptiveBaseCapFrom_cast_le_uniform data mu delta center
      (adaptiveCoverCount data mu r) 0 B hB
    intro k hk0 hk
    have hk' : k ≤ adaptiveCoverCount data mu r := by omega
    have hcap := baseTrialCap_cast_le_initial_radius data mu hmu
      (baseHalvingCount data (adaptiveGuessRadius data mu k) delta)
      (adaptiveGuessRadius data mu k) (adaptiveGuessRadius_pos data mu hmu k).le
    have hcount := hhalvings k hk'
    have hthreshold := adaptiveGuess_halvingThreshold_le_cover_bound
      data mu r hmu hr hrD k hk'
    dsimp [scheduledBaseTrialCall, baseTrialCall]
    dsimp [B, C, qpow]
    calc
      (baseTrialCap data mu
        (baseHalvingCount data (adaptiveGuessRadius data mu k) delta)
        (adaptiveGuessRadius data mu k) : ℝ) ≤
          2 + 2 * (baseHalvingCount data
            (adaptiveGuessRadius data mu k) delta : ℝ) *
            (halvingThreshold data.p data.Lp
              (adaptiveGuessRadius data mu k) mu + 1) := hcap
      _ ≤ 2 + 2 * (Ahalve * LS) *
          (baseCoverHalvingConstant data.p * (1 + qpow) + 1) := by
        have hth0 : 0 ≤ halvingThreshold data.p data.Lp
            (adaptiveGuessRadius data mu k) mu :=
          halvingThreshold_nonneg data.p data.Lp _ mu data.Lp_pos.le
            (adaptiveGuessRadius_pos data mu hmu k).le hmu.le
        have hright0 : 0 ≤ halvingThreshold data.p data.Lp
            (adaptiveGuessRadius data mu k) mu + 1 := by linarith
        have hsum : halvingThreshold data.p data.Lp
            (adaptiveGuessRadius data mu k) mu + 1 ≤
            baseCoverHalvingConstant data.p * (1 + qpow) + 1 := by
          simpa [qpow] using add_le_add_left hthreshold 1
        have hmul := mul_le_mul hcount hsum
          hright0 (mul_nonneg hAh hLS0)
        nlinarith
  have hBbound : B ≤
      2 * (1 + Ahalve) * (C + 1) * (1 + qpow) * LS := by
    dsimp [B]
    have hinner : C * (1 + qpow) + 1 ≤ (C + 1) * (1 + qpow) := by
      nlinarith
    have hK : 1 ≤ (C + 1) * (1 + qpow) := by nlinarith
    calc
      2 + 2 * (Ahalve * LS) * (C * (1 + qpow) + 1) ≤
          2 * ((C + 1) * (1 + qpow)) * LS +
            2 * (Ahalve * LS) * ((C + 1) * (1 + qpow)) := by
        apply add_le_add
        · nlinarith
        · exact mul_le_mul_of_nonneg_left hinner (by positivity)
      _ = 2 * (1 + Ahalve) * (C + 1) * (1 + qpow) * LS := by ring
  calc
    (adaptiveBaseCapFrom data mu delta center
      (adaptiveCoverCount data mu r) 0 : ℝ) ≤
        ((adaptiveCoverCount data mu r : ℝ) + 1) * B := hprefix
    _ ≤ (Aguess * LS) * B := mul_le_mul_of_nonneg_right hguesses hB
    _ ≤ (Aguess * LS) *
        (2 * (1 + Ahalve) * (C + 1) * (1 + qpow) * LS) :=
      mul_le_mul_of_nonneg_left hBbound (mul_nonneg hAg hLS0)
    _ = (2 * Aguess * (1 + Ahalve) * (baseCoverHalvingConstant data.p + 1)) *
        (1 + Real.rpow (data.Lp * r ^ (data.p - 1) / mu)
          (baseHalvingExponent data.p)) * LS ^ 2 := by
      dsimp [C, qpow]
      ring

theorem diameter_scale_pow_condition (data : VIPublicData E)
    (mu : ℝ) (hmu : 0 < mu) :
    (data.D / baseStrongScale data mu) ^ (data.p - 1) =
      data.Lp * data.D ^ (data.p - 1) / mu := by
  rw [div_pow, baseStrongScale_pow data mu hmu]
  field_simp [data.Lp_pos.ne', hmu.ne']

theorem adaptiveCoverCount_add_one_le_strongLog
    (data : VIPublicData E) (mu delta r : ℝ)
    (hmu : 0 < mu) (hdelta : 0 < delta)
    (hr : 0 ≤ r) (hrD : r ≤ data.D) :
    ((adaptiveCoverCount data mu r : ℝ) + 1) ≤
      (2 + 1 / Real.log 2) * strongLog data mu delta := by
  let c := data.D / baseStrongScale data mu
  let qD := data.Lp * data.D ^ (data.p - 1) / mu
  let LS := strongLog data mu delta
  have hc : 0 < c := div_pos data.D_pos (baseStrongScale_pos data mu hmu)
  have hqD : 0 < qD := by
    dsimp [qD]
    exact div_pos (mul_pos data.Lp_pos (pow_pos data.D_pos _)) hmu
  have hLS : 1 ≤ LS := strongLog_one_le data mu delta hmu hdelta
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogpow : ((data.p - 1 : ℕ) : ℝ) * Real.log c = Real.log qD := by
    rw [← Real.log_pow, diameter_scale_pow_condition data mu hmu]
  have hlogqD_le : Real.log qD ≤ LS := by
    have harg : qD ≤ 2 + qD + data.Lp * data.D ^ data.p / delta +
        mu * data.D / delta := by
      have hA : 0 ≤ data.Lp * data.D ^ data.p / delta :=
        div_nonneg (mul_nonneg data.Lp_pos.le (pow_nonneg data.D_pos.le _)) hdelta.le
      have hB : 0 ≤ mu * data.D / delta :=
        div_nonneg (mul_nonneg hmu.le data.D_pos.le) hdelta.le
      linarith
    have hargpos : 0 < 2 + qD + data.Lp * data.D ^ data.p / delta +
        mu * data.D / delta := lt_of_lt_of_le hqD harg
    have hlog := Real.strictMonoOn_log.monotoneOn hqD hargpos harg
    dsimp [LS, strongLog]
    dsimp [qD] at hlog ⊢
    linarith
  have hmaxlogb : max 0 (Real.logb 2 c) ≤ LS / Real.log 2 := by
    by_cases hlogc : 0 ≤ Real.log c
    · have hn : (1 : ℝ) ≤ (data.p - 1 : ℕ) := by
        exact_mod_cast Nat.le_sub_of_add_le data.p_ge_two
      have hclog : Real.log c ≤ Real.log qD := by
        rw [← hlogpow]
        nlinarith
      rw [max_eq_right]
      · unfold Real.logb
        exact div_le_div_of_nonneg_right (hclog.trans hlogqD_le) hlog2.le
      · unfold Real.logb
        exact div_nonneg hlogc hlog2.le
    · have hlogc' : Real.log c < 0 := lt_of_not_ge hlogc
      rw [max_eq_left]
      · exact div_nonneg (le_trans (by norm_num) hLS) hlog2.le
      · unfold Real.logb
        exact (div_neg_of_neg_of_pos hlogc' hlog2).le
  have hcoverNat := adaptiveCoverCount_le data mu r hmu hr hrD
  have hguessNat := adaptiveGuessCount_le_natCeil_logb data mu hmu
  have hceil := natCeil_cast_le_max_add_one (Real.logb 2 c)
  have hcoverReal : (adaptiveCoverCount data mu r : ℝ) ≤
      (⌈Real.logb 2 c⌉₊ : ℝ) := by exact_mod_cast hcoverNat.trans hguessNat
  have hraw : (adaptiveCoverCount data mu r : ℝ) + 1 ≤
      LS / Real.log 2 + 2 := by linarith
  have hcoef : 0 ≤ 1 / Real.log 2 := by positivity
  dsimp [LS] at hraw hLS ⊢
  rw [div_eq_mul_inv] at hraw
  rw [div_eq_mul_inv]
  nlinarith


end
end VIReference.Pilot
