import LeanArticleAudit.Pilot.UpperBoostCost

/-!
# Strong-log control for the boost transformation

This file isolates the scalar estimate which compares every regularized
strong call made by the boost wrapper with the public residual logarithm.
-/

namespace LeanArticleAudit.Pilot

noncomputable section

universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A reusable logarithm compressor.  The deliberately coarse exponent is
chosen so later cap proofs do not depend on fragile numerical simplification.
-/
theorem one_add_log_le_natPower_scale {T x : ℝ} {n : ℕ}
    (hT : 2 ≤ T) (hx : 0 < x) (hpow : x ≤ T ^ n) :
    1 + Real.log x ≤ (n + 1 : ℝ) * (1 + Real.log T) := by
  have hTpos : 0 < T := lt_of_lt_of_le (by norm_num) hT
  have hlog := Real.log_le_log hx hpow
  rw [Real.log_pow] at hlog
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  push_cast at hlog ⊢
  nlinarith

theorem one_add_harmonicR_le_two_mul (K : ℕ) :
    1 + harmonicR (K + 1) ≤ 2 * (K + 1 : ℝ) := by
  have hn : 1 ≤ K + 1 := by omega
  have hh := harmonicR_le_one_add_log (K + 1) hn
  have hpos : (0 : ℝ) < K + 1 := by positivity
  have hlog := Real.log_le_sub_one_of_pos hpos
  push_cast at hh hlog ⊢
  linarith

theorem boostStepsize_le_simple {R epsilon : ℝ}
    (hR : 0 ≤ R) (hepsilon : 0 < epsilon) (K : ℕ) :
    boostStepsize R epsilon K ≤ 16 * R / epsilon := by
  rw [boostStepsize]
  have hden : 0 < epsilon * (K + 1 : ℝ) := by positivity
  apply (div_le_iff₀ hden).2
  have hh := one_add_harmonicR_le_two_mul K
  calc
    8 * R * (1 + harmonicR (K + 1)) ≤
        8 * R * (2 * (K + 1 : ℝ)) :=
      mul_le_mul_of_nonneg_left hh (mul_nonneg (by norm_num) hR)
    _ = 16 * R / epsilon * (epsilon * (K + 1 : ℝ)) := by
      field_simp [hepsilon.ne']
      ring

theorem boost_strong_log_argument_power_bound (p : ℕ) (hp : 2 ≤ p)
    {d q T : ℝ} (hd : 0 ≤ d) (hq : 0 ≤ q)
    (hT : T = 2 + d + q) :
    2 + 16 * q * d ^ (p - 1) +
          1296 * q * d ^ p * T ^ 4 + 81 * d * T ^ 4 ≤
      T ^ (p + 16) := by
  have hT2 : 2 ≤ T := by rw [hT]; linarith
  have hT0 : 0 ≤ T := hT2.trans' (by norm_num)
  have hdT : d ≤ T := by rw [hT]; linarith
  have hqT : q ≤ T := by rw [hT]; linarith
  have hdp : d ^ p ≤ T ^ p := pow_le_pow_left₀ hd hdT p
  have hdpred : d ^ (p - 1) ≤ T ^ (p - 1) :=
    pow_le_pow_left₀ hd hdT (p - 1)
  have hTp : T ^ p ≤ T ^ (p + 5) := by
    exact pow_le_pow_right₀ (by linarith) (by omega)
  have hT5 : T ^ 5 ≤ T ^ (p + 5) := by
    exact pow_le_pow_right₀ (by linarith) (by omega)
  have hqdp : q * d ^ (p - 1) ≤ T ^ p := by
    calc
      q * d ^ (p - 1) ≤ T * T ^ (p - 1) :=
        mul_le_mul hqT hdpred (pow_nonneg hd _) hT0
      _ = T ^ p := by
        calc
          T * T ^ (p - 1) = T ^ (p - 1) * T := by ring
          _ = T ^ ((p - 1) + 1) := (pow_succ T (p - 1)).symm
          _ = T ^ p := by congr 1; omega
  have hqd : q * d ^ p * T ^ 4 ≤ T ^ (p + 5) := by
    calc
      q * d ^ p * T ^ 4 ≤ T * T ^ p * T ^ 4 := by
        gcongr
      _ = T ^ (p + 5) := by
        calc
          T * T ^ p * T ^ 4 = T ^ 1 * T ^ p * T ^ 4 := by simp
          _ = T ^ (1 + p + 4) := by rw [pow_add, pow_add]
          _ = T ^ (p + 5) := by congr 1; omega
  have hd4 : d * T ^ 4 ≤ T ^ 5 := by
    calc
      d * T ^ 4 ≤ T * T ^ 4 :=
        mul_le_mul_of_nonneg_right hdT (pow_nonneg hT0 _)
      _ = T ^ 5 := by ring
  have hbase1 : 1 ≤ T ^ (p + 5) := one_le_pow₀ (by linarith)
  have hsum :
      2 + 16 * q * d ^ (p - 1) +
          1296 * q * d ^ p * T ^ 4 + 81 * d * T ^ 4 ≤
        1395 * T ^ (p + 5) := by
    nlinarith
  have hconst : (2048 : ℝ) ≤ T ^ 11 := by
    calc
      (2048 : ℝ) = 2 ^ 11 := by norm_num
      _ ≤ T ^ 11 := pow_le_pow_left₀ (by norm_num) hT2 11
  calc
    2 + 16 * q * d ^ (p - 1) +
          1296 * q * d ^ p * T ^ 4 + 81 * d * T ^ 4 ≤
        1395 * T ^ (p + 5) := hsum
    _ ≤ 2048 * T ^ (p + 5) := by
      exact mul_le_mul_of_nonneg_right (by norm_num) (pow_nonneg hT0 _)
    _ ≤ T ^ 11 * T ^ (p + 5) :=
      mul_le_mul_of_nonneg_right hconst (pow_nonneg hT0 _)
    _ = T ^ (p + 16) := by
      rw [← pow_add]
      congr 1
      omega

theorem boost_scale_first_identity (p : ℕ) (hp : 1 ≤ p)
    {Lp D R epsilon : ℝ} (hR : R ≠ 0) (hepsilon : epsilon ≠ 0) :
    Lp * D ^ (p - 1) * (16 * R / epsilon) =
      16 * (Lp * R ^ p / epsilon) * (D / R) ^ (p - 1) := by
  rw [div_pow]
  field_simp
  have hpow : R ^ (p - 1) * R = R ^ p := by
    rw [← pow_succ]
    congr 1
    omega
  calc
    Lp * D ^ (p - 1) * R * R ^ (p - 1) =
        Lp * D ^ (p - 1) * (R ^ (p - 1) * R) := by ring
    _ = Lp * D ^ (p - 1) * R ^ p := by rw [hpow]

theorem boost_scale_second_identity (p : ℕ)
    {Lp D R epsilon : ℝ} (hR : R ≠ 0) (hepsilon : epsilon ≠ 0) :
    Lp * D ^ p * (16 * R / epsilon) / R =
      16 * (Lp * R ^ p / epsilon) * (D / R) ^ p := by
  rw [div_pow]
  field_simp

/-- Every strong logarithm used by the specialized boost call is controlled
by the public residual logarithm.  The factor `20 (p+1)` is uniform in the
dimension, domain, operator, radius, and target accuracy. -/
theorem boost_strongLog_le_residualLog (data : VIPublicData E)
    (gamma R epsilon : ℝ) (hgamma : 0 < gamma) (hgamma1 : gamma ≤ 1)
    (hR : 0 < R) (hRD : R ≤ data.D) (hepsilon : 0 < epsilon) :
    let K := boostHorizon data gamma R epsilon
    let eta := boostStepsize R epsilon K
    let e := boostOuterError R K
    strongLog data (1 / eta) (e / eta) ≤
      20 * (data.p + 1 : ℝ) * residualLog data R epsilon := by
  dsimp only
  let p := data.p
  let q := residualCondition data R epsilon
  let d := data.D / R
  let T := 2 + d + q
  let alpha := boostAlpha gamma
  let K := boostHorizon data gamma R epsilon
  let eta := boostStepsize R epsilon K
  let e := boostOuterError R K
  have hp : 2 ≤ p := data.p_ge_two
  have hLp : 0 < data.Lp := data.Lp_pos
  have hD : 0 < data.D := data.D_pos
  have hd0 : 0 ≤ d := div_nonneg hD.le hR.le
  have hq : 0 < q := by
    dsimp [q, residualCondition]
    positivity
  have hT : T = 2 + d + q := rfl
  have hT2 : 2 ≤ T := by rw [hT]; linarith
  have halpha0 : 0 ≤ alpha := by
    dsimp [alpha, boostAlpha]
    positivity
  have halpha1 : alpha ≤ 1 := by
    dsimp [alpha, boostAlpha]
    exact (div_le_one (by linarith)).2 (by linarith)
  have heta : 0 < eta := by
    dsimp [eta, K]
    exact boostStepsize_pos hR hepsilon _
  have he : 0 < e := by
    dsimp [e, K]
    exact boostOuterError_pos hR _
  have heta_le : eta ≤ 16 * R / epsilon := by
    dsimp [eta]
    exact boostStepsize_le_simple hR.le hepsilon K
  have hKraw := (boostHorizon_bounds data gamma R epsilon hq.le).2
  have hqa : Real.rpow q alpha ≤ 1 + q :=
    rpow_le_one_add_self hq halpha0 halpha1
  have hK2T : (K + 2 : ℝ) ≤ 3 * T := by
    dsimp [K] at hKraw
    dsimp [q, alpha] at hKraw hqa
    push_cast at hKraw ⊢
    dsimp [T, d, q]
    linarith [hd0]
  have hK2nonneg : 0 ≤ (K + 2 : ℝ) := by positivity
  have hKpow : (K + 2 : ℝ) ^ 4 ≤ 81 * T ^ 4 := by
    have := pow_le_pow_left₀ hK2nonneg hK2T 4
    norm_num at this ⊢
    nlinarith
  let A := data.Lp * data.D ^ (p - 1) / (1 / eta)
  let B := data.Lp * data.D ^ p / (e / eta)
  let C := (1 / eta) * data.D / (e / eta)
  have hAeq : A = data.Lp * data.D ^ (p - 1) * eta := by
    dsimp [A]
    field_simp [heta.ne']
  have hAle : A ≤ 16 * q * d ^ (p - 1) := by
    rw [hAeq]
    calc
      data.Lp * data.D ^ (p - 1) * eta ≤
          data.Lp * data.D ^ (p - 1) * (16 * R / epsilon) := by
        gcongr
      _ = 16 * q * d ^ (p - 1) := by
        exact boost_scale_first_identity p (by omega) hR.ne' hepsilon.ne'
  have hBeq : B = data.Lp * data.D ^ p * eta / e := by
    dsimp [B]
    field_simp [heta.ne', he.ne']
  have hBle0 : B ≤ data.Lp * data.D ^ p * (16 * R / epsilon) / e := by
    rw [hBeq]
    gcongr
  have hedef : e = R / (K + 2 : ℝ) ^ 4 := rfl
  have hBscale : data.Lp * data.D ^ p * (16 * R / epsilon) / e =
      16 * q * d ^ p * (K + 2 : ℝ) ^ 4 := by
    rw [hedef]
    have hid := boost_scale_second_identity p (Lp := data.Lp) (D := data.D)
      (R := R) (epsilon := epsilon) hR.ne' hepsilon.ne'
    field_simp [hR.ne'] at ⊢
    dsimp [q, d, residualCondition]
    field_simp [hR.ne', hepsilon.ne'] at hid ⊢
    nlinarith
  have hBle : B ≤ 1296 * q * d ^ p * T ^ 4 := by
    calc
      B ≤ data.Lp * data.D ^ p * (16 * R / epsilon) / e := hBle0
      _ = 16 * q * d ^ p * (K + 2 : ℝ) ^ 4 := hBscale
      _ ≤ 16 * q * d ^ p * (81 * T ^ 4) := by
        gcongr
      _ = 1296 * q * d ^ p * T ^ 4 := by ring
  have hCeq : C = d * (K + 2 : ℝ) ^ 4 := by
    dsimp [C, d]
    rw [hedef]
    field_simp [heta.ne', hR.ne']
  have hCle : C ≤ 81 * d * T ^ 4 := by
    rw [hCeq]
    calc
      d * (K + 2 : ℝ) ^ 4 ≤ d * (81 * T ^ 4) :=
        mul_le_mul_of_nonneg_left hKpow hd0
      _ = 81 * d * T ^ 4 := by ring
  let x := 2 + A + B + C
  have hxpos : 0 < x := by
    have hA0 : 0 ≤ A := by
      dsimp [A]
      positivity
    have hB0 : 0 ≤ B := by
      dsimp [B]
      positivity
    have hC0 : 0 ≤ C := by
      dsimp [C]
      positivity
    dsimp [x]
    linarith
  have hxpow : x ≤ T ^ (p + 16) := by
    apply le_trans (show x ≤
      2 + 16 * q * d ^ (p - 1) +
        1296 * q * d ^ p * T ^ 4 + 81 * d * T ^ 4 by
          dsimp [x]
          linarith)
    exact boost_strong_log_argument_power_bound p hp hd0 hq.le hT
  have hlog := one_add_log_le_natPower_scale hT2 hxpos hxpow
  have hcoef : ((p + 16 : ℕ) : ℝ) + 1 ≤ 20 * (p + 1 : ℝ) := by
    push_cast
    nlinarith [hp]
  have hLA0 : 0 ≤ residualLog data R epsilon := by
    unfold residualLog
    have : 1 ≤ 2 + data.D / R + residualCondition data R epsilon := by
      have hd : 0 ≤ data.D / R := div_nonneg data.D_pos.le hR.le
      have hq0 : 0 ≤ residualCondition data R epsilon := by
        unfold residualCondition
        positivity
      linarith
    linarith [Real.log_nonneg this]
  change 1 + Real.log x ≤ 20 * (p + 1 : ℝ) * residualLog data R epsilon
  calc
    1 + Real.log x ≤ (((p + 16 : ℕ) : ℝ) + 1) *
        (1 + Real.log T) := hlog
    _ ≤ 20 * (p + 1 : ℝ) * (1 + Real.log T) :=
      mul_le_mul_of_nonneg_right hcoef (by
        linarith [Real.log_nonneg (by linarith : 1 ≤ T)])
    _ = 20 * (p + 1 : ℝ) * residualLog data R epsilon := by
      rfl

end

end LeanArticleAudit.Pilot
