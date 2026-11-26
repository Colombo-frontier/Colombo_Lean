import LeanArticleAudit.Pilot.UpperBoost
import LeanArticleAudit.Pilot.UpperCost

/-!
# Scalar logarithmic bounds for the boost transformation

This module is kept separate from the executable boost trace.  It supplies
the base-two block-count and harmonic estimates needed to compress the
explicit shared cap to the public residual-interface logarithm.
-/

open Finset

namespace LeanArticleAudit.Pilot

noncomputable section

universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The installed horizon is within two of the continuous balancing scale,
while never falling below it. -/
theorem boostHorizon_bounds (data : VIPublicData E) (gamma R epsilon : ℝ)
    (hQ : 0 ≤ residualCondition data R epsilon) :
    Real.rpow (residualCondition data R epsilon) (boostAlpha gamma) ≤
        (boostHorizon data gamma R epsilon : ℝ) ∧
      (boostHorizon data gamma R epsilon : ℝ) ≤
        Real.rpow (residualCondition data R epsilon) (boostAlpha gamma) + 2 := by
  exact max_two_natCeil_bounds _
    (Real.rpow_nonneg hQ (boostAlpha gamma))

theorem rpow_le_one_add_self {q alpha : ℝ} (hq : 0 < q)
    (ha0 : 0 ≤ alpha) (ha1 : alpha ≤ 1) :
    Real.rpow q alpha ≤ 1 + q := by
  by_cases hq1 : q ≤ 1
  · exact (Real.rpow_le_one hq.le hq1 ha0).trans (by linarith)
  · have h1q : 1 ≤ q := le_of_not_ge hq1
    exact (Real.rpow_le_self_of_one_le h1q ha1).trans (by linarith)

/-- The chosen horizon and all logarithms appearing in `U_a` are controlled
by the residual logarithm.  This deliberately uses coarse constants so the
result is stable under ceiling arithmetic. -/
theorem boostHorizon_log_bounds (data : VIPublicData E) (gamma R epsilon : ℝ)
    (hR : 0 < R) (hQ : 0 < residualCondition data R epsilon)
    (ha0 : 0 ≤ boostAlpha gamma) (ha1 : boostAlpha gamma ≤ 1) :
    let K := boostHorizon data gamma R epsilon
    let LA := residualLog data R epsilon
    (K + 1 : ℝ) ≤ 3 * (1 + Real.rpow (residualCondition data R epsilon)
        (boostAlpha gamma)) ∧
      Real.log K ≤ 2 * LA ∧
      1 + Real.log (K + 2 : ℝ) ≤ 3 * LA := by
  dsimp only
  let Q := residualCondition data R epsilon
  let qa := Real.rpow Q (boostAlpha gamma)
  let K := boostHorizon data gamma R epsilon
  let T := 2 + data.D / R + Q
  let LA := residualLog data R epsilon
  have hqa0 : 0 ≤ qa := Real.rpow_nonneg hQ.le _
  have hK := (boostHorizon_bounds data gamma R epsilon hQ.le).2
  have hK2 : 2 ≤ K := boostHorizon_ge_two data gamma R epsilon
  have hK1 : (K + 1 : ℝ) ≤ 3 * (1 + qa) := by
    push_cast
    linarith
  have hqaQ : qa ≤ 1 + Q := rpow_le_one_add_self hQ ha0 ha1
  have hDR0 : 0 ≤ data.D / R := div_nonneg data.D_pos.le hR.le
  have hT2 : 2 ≤ T := by
    linarith
  have hK2T : (K + 2 : ℝ) ≤ 3 * T := by
    push_cast at hK ⊢
    have hKT : (K : ℝ) ≤ Q + 3 := hK.trans (by linarith)
    linarith [hDR0, hQ]
  have hTpos : 0 < T := lt_of_lt_of_le (by norm_num) hT2
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have hK2pos : (0 : ℝ) < K + 2 := by positivity
  have hlogK2 := Real.log_le_log hK2pos hK2T
  have hlog3T : Real.log (3 * T) = Real.log 3 + Real.log T := by
    rw [Real.log_mul (by norm_num) (ne_of_gt hTpos)]
  rw [hlog3T] at hlogK2
  have hlog3 : Real.log (3 : ℝ) ≤ 2 :=
    (Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)).trans_eq (by norm_num)
  have hlogT0 : 0 ≤ Real.log T := Real.log_nonneg (by linarith : 1 ≤ T)
  have hLA : LA = 1 + Real.log T := rfl
  have hlogK : Real.log K ≤ 2 * LA := by
    have hKK2 : (K : ℝ) ≤ K + 2 := by norm_num
    have := Real.log_le_log hKpos hKK2
    rw [hLA]
    linarith
  refine ⟨hK1, hlogK, ?_⟩
  change 1 + Real.log (K + 2 : ℝ) ≤ 3 * LA
  rw [hLA]
  linarith

/-- The number of dyadic blocks is controlled by the natural logarithm, with
the exact conversion factor `log 2`. -/
theorem natLog_two_cast_le_real_log_div (K : ℕ) (hK : 2 ≤ K) :
    (Nat.log 2 K : ℝ) ≤ Real.log K / Real.log 2 := by
  have hpowNat : 2 ^ Nat.log 2 K ≤ K :=
    Nat.pow_log_le_self 2 (by omega : K ≠ 0)
  have hpow : ((2 : ℝ) ^ Nat.log 2 K) ≤ (K : ℝ) := by
    exact_mod_cast hpowNat
  have hlog := Real.log_le_log
    (by positivity : 0 < (2 : ℝ) ^ Nat.log 2 K) hpow
  rw [Real.log_pow] at hlog
  exact (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).2 hlog

/-- Every harmonic factor in a public dyadic block is uniformly bounded by
the final logarithmic scale.  The explicit constant `3` is intentionally
coarse and independent of `K` and the dimension. -/
theorem dyadic_harmonic_le_log_scale (K j : ℕ) (hK : 2 ≤ K)
    (hj : j ∈ Finset.Icc 1 (Nat.log 2 K)) :
    1 + harmonicR (2 ^ (j + 1)) ≤
      3 * (1 + Real.log (K + 2 : ℝ)) := by
  have hj' := Finset.mem_Icc.mp hj
  have hn1 : 1 ≤ 2 ^ (j + 1) :=
    Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by norm_num))
  have hh := harmonicR_le_one_add_log (2 ^ (j + 1)) hn1
  have hpowNat : 2 ^ (j + 1) ≤ 2 * K := by
    have hjpow : 2 ^ j ≤ K :=
      (Nat.pow_le_pow_right (by omega) hj'.2).trans
        (Nat.pow_log_le_self 2 (by omega : K ≠ 0))
    simpa [pow_succ, mul_comm] using Nat.mul_le_mul_left 2 hjpow
  have hpow : ((2 ^ (j + 1) : ℕ) : ℝ) ≤ (2 * K : ℕ) := by
    exact_mod_cast hpowNat
  have hlogpow := Real.log_le_log
    (by positivity : 0 < ((2 ^ (j + 1) : ℕ) : ℝ)) hpow
  have h2Kpos : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have hlog2K : Real.log ((2 * K : ℕ) : ℝ) =
      Real.log 2 + Real.log K := by
    push_cast
    rw [Real.log_mul (by norm_num) (ne_of_gt h2Kpos)]
  rw [hlog2K] at hlogpow
  have hKle : (K : ℝ) ≤ K + 2 := by norm_num
  have hlogKle := Real.log_le_log h2Kpos hKle
  have hlogK2 : 0 ≤ Real.log (K + 2 : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ K + 2 by omega))
  have hlog2 : Real.log (2 : ℝ) ≤ 1 :=
    Real.log_two_lt_d9.le.trans (by norm_num)
  linarith

/-- Explicit logarithmic majorant for the complete `U_a(K)` sum.  The lower
range assumption `a ≥ 2/3` is precisely what makes the dyadic geometric
factor nonincreasing; the upper range `a ≤ 2` is used earlier by the power
mean estimate and is not needed again here. -/
theorem boostUa_le_explicit_log (a : ℝ) (K : ℕ)
    (ha0 : 0 ≤ a) (ha23 : 2 / 3 ≤ a) (hK : 2 ≤ K) :
    boostUa a K ≤
      2 * Real.rpow 3 a + Real.rpow 16 a *
        (Real.log K / Real.log 2) *
          Real.rpow (3 * (1 + Real.log (K + 2 : ℝ))) a := by
  unfold boostUa
  have hscale0 : 0 ≤ 3 * (1 + Real.log (K + 2 : ℝ)) := by
    have : 0 ≤ Real.log (K + 2 : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ K + 2 by omega))
    positivity
  have hterm : ∀ j ∈ Finset.Icc 1 (Nat.log 2 K),
      Real.rpow (1 + harmonicR (2 ^ (j + 1))) a *
          Real.rpow (2 : ℝ) (j * (1 - 3 * a / 2)) ≤
        Real.rpow (3 * (1 + Real.log (K + 2 : ℝ))) a := by
    intro j hj
    have hH0 : 0 ≤ 1 + harmonicR (2 ^ (j + 1)) := by
      linarith [harmonicR_nonneg (2 ^ (j + 1))]
    have hHpow := Real.rpow_le_rpow hH0
      (dyadic_harmonic_le_log_scale K j hK hj) ha0
    have hexp : (j : ℝ) * (1 - 3 * a / 2) ≤ 0 := by
      have : 1 - 3 * a / 2 ≤ 0 := by linarith
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity) this
    have htwo := Real.rpow_le_one_of_one_le_of_nonpos
      (by norm_num : (1 : ℝ) ≤ 2) hexp
    calc
      Real.rpow (1 + harmonicR (2 ^ (j + 1))) a *
          Real.rpow (2 : ℝ) (j * (1 - 3 * a / 2)) ≤
        Real.rpow (1 + harmonicR (2 ^ (j + 1))) a * 1 := by
          exact mul_le_mul_of_nonneg_left htwo (Real.rpow_nonneg hH0 a)
      _ ≤ Real.rpow (3 * (1 + Real.log (K + 2 : ℝ))) a := by
        simpa using hHpow
  have hsum :
      (∑ j ∈ Finset.Icc 1 (Nat.log 2 K),
        Real.rpow (1 + harmonicR (2 ^ (j + 1))) a *
          Real.rpow (2 : ℝ) (j * (1 - 3 * a / 2))) ≤
      (Nat.log 2 K : ℝ) *
        Real.rpow (3 * (1 + Real.log (K + 2 : ℝ))) a := by
    calc
      _ ≤ ∑ _j ∈ Finset.Icc 1 (Nat.log 2 K),
          Real.rpow (3 * (1 + Real.log (K + 2 : ℝ))) a :=
        Finset.sum_le_sum hterm
      _ ≤ (Nat.log 2 K : ℝ) *
          Real.rpow (3 * (1 + Real.log (K + 2 : ℝ))) a := by
        rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]
        have hcard : Nat.log 2 K + 1 - 1 ≤ Nat.log 2 K := by omega
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
          (Real.rpow_nonneg hscale0 a)
  have hlog := natLog_two_cast_le_real_log_div K hK
  have hpow0 := Real.rpow_nonneg hscale0 a
  have hsum' :
      (∑ j ∈ Finset.Icc 1 (Nat.log 2 K),
        Real.rpow (1 + harmonicR (2 ^ (j + 1))) a *
          Real.rpow (2 : ℝ) (j * (1 - 3 * a / 2))) ≤
      (Real.log K / Real.log 2) *
        Real.rpow (3 * (1 + Real.log (K + 2 : ℝ))) a :=
    hsum.trans (mul_le_mul_of_nonneg_right hlog hpow0)
  have hscaled := mul_le_mul_of_nonneg_left hsum'
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 16) a)
  calc
    2 * Real.rpow 3 a + Real.rpow 16 a *
        (∑ j ∈ Finset.Icc 1 (Nat.log 2 K),
          Real.rpow (1 + harmonicR (2 ^ (j + 1))) a *
            Real.rpow (2 : ℝ) (j * (1 - 3 * a / 2))) ≤
      2 * Real.rpow 3 a + Real.rpow 16 a *
        ((Real.log K / Real.log 2) *
          Real.rpow (3 * (1 + Real.log (K + 2 : ℝ))) a) := by
      simpa [add_comm] using add_le_add_right hscaled (2 * Real.rpow 3 a)
    _ = _ := by ring

/-- Polynomial-log compression of the explicit dyadic sum at the chosen
horizon.  The exponent range is exactly the boost range. -/
theorem boostUa_at_horizon_le (data : VIPublicData E) (gamma R epsilon a : ℝ)
    (hR : 0 < R) (hQ : 0 < residualCondition data R epsilon)
    (halpha0 : 0 ≤ boostAlpha gamma) (halpha1 : boostAlpha gamma ≤ 1)
    (ha0 : 0 ≤ a) (ha23 : 2 / 3 ≤ a) (ha2 : a ≤ 2) :
    boostUa a (boostHorizon data gamma R epsilon) ≤
      83000 * (residualLog data R epsilon) ^ 3 := by
  let K := boostHorizon data gamma R epsilon
  let LA := residualLog data R epsilon
  have hK : 2 ≤ K := boostHorizon_ge_two data gamma R epsilon
  obtain ⟨_hKsize, hlogK, hlogK2⟩ :=
    boostHorizon_log_bounds data gamma R epsilon hR hQ halpha0 halpha1
  have hT2 : 2 ≤ 2 + data.D / R + residualCondition data R epsilon := by
    have hDR0 : 0 ≤ data.D / R := div_nonneg data.D_pos.le hR.le
    linarith
  have hLA1 : 1 ≤ LA := by
    change 1 ≤ 1 + Real.log
      (2 + data.D / R + residualCondition data R epsilon)
    linarith [Real.log_nonneg (by linarith :
      1 ≤ 2 + data.D / R + residualCondition data R epsilon)]
  have h3a : Real.rpow 3 a ≤ 9 := by
    calc
      Real.rpow 3 a ≤ Real.rpow 3 2 :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) ha2
      _ = 9 := by norm_num [Real.rpow_two]
  have h16a : Real.rpow 16 a ≤ 256 := by
    calc
      Real.rpow 16 a ≤ Real.rpow 16 2 :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) ha2
      _ = 256 := by norm_num [Real.rpow_two]
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    exact (by norm_num : (1 / 2 : ℝ) ≤ 0.6931471803).trans
      Real.log_two_gt_d9.le
  have hlogdiv : Real.log K / Real.log 2 ≤ 4 * LA := by
    have hlog20 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    apply (div_le_iff₀ hlog20).2
    have hlogK0 : 0 ≤ Real.log K :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ K by omega))
    nlinarith
  let scale := 3 * (1 + Real.log (K + 2 : ℝ))
  have hscale1 : 1 ≤ scale := by
    have : 0 ≤ Real.log (K + 2 : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ K + 2 by omega))
    dsimp [scale]
    linarith
  have hscale : scale ≤ 9 * LA := by
    dsimp [scale]
    linarith
  have hscalePow : Real.rpow scale a ≤ 81 * LA ^ 2 := by
    calc
      Real.rpow scale a ≤ Real.rpow scale 2 :=
        Real.rpow_le_rpow_of_exponent_le hscale1 ha2
      _ = scale ^ 2 := Real.rpow_two scale
      _ ≤ (9 * LA) ^ 2 := by nlinarith
      _ = 81 * LA ^ 2 := by ring
  have hexplicit := boostUa_le_explicit_log a K ha0 ha23 hK
  have hlogdiv0 : 0 ≤ Real.log K / Real.log 2 :=
    div_nonneg (Real.log_nonneg (by exact_mod_cast (show 1 ≤ K by omega)))
      (Real.log_pos (by norm_num)).le
  have hscalePow0 : 0 ≤ Real.rpow scale a := Real.rpow_nonneg (by linarith) a
  have hLA0 : 0 ≤ LA := hLA1.trans' (by norm_num)
  change boostUa a K ≤ 83000 * LA ^ 3
  calc
    boostUa a K ≤ 2 * Real.rpow 3 a + Real.rpow 16 a *
        (Real.log K / Real.log 2) * Real.rpow scale a := by
      simpa [scale] using hexplicit
    _ ≤ 2 * 9 + 256 * (4 * LA) * (81 * LA ^ 2) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left h3a (by norm_num)
      · calc
          Real.rpow 16 a * (Real.log K / Real.log 2) * Real.rpow scale a ≤
              256 * (Real.log K / Real.log 2) * Real.rpow scale a := by
                exact mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_right h16a hlogdiv0) hscalePow0
          _ ≤ 256 * (4 * LA) * Real.rpow scale a := by
                exact mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left hlogdiv (by norm_num)) hscalePow0
          _ ≤ 256 * (4 * LA) * (81 * LA ^ 2) := by
                exact mul_le_mul_of_nonneg_left hscalePow
                  (mul_nonneg (by norm_num) (mul_nonneg (by norm_num) hLA0))
    _ ≤ 83000 * LA ^ 3 := by
      have hLA3 : 1 ≤ LA ^ 3 := one_le_pow₀ hLA1
      nlinarith

/-- The horizon balances the regularization factor: after raising to
`gamma`, `Q/(K+1)` costs at most the target residual exponent. -/
theorem boost_balance (data : VIPublicData E) (gamma R epsilon : ℝ)
    (hgamma : 0 < gamma)
    (hQ : 0 < residualCondition data R epsilon) :
    Real.rpow (residualCondition data R epsilon /
        (boostHorizon data gamma R epsilon + 1 : ℝ)) gamma ≤
      1 + Real.rpow (residualCondition data R epsilon) (boostAlpha gamma) := by
  let Q := residualCondition data R epsilon
  let alpha := boostAlpha gamma
  let K := boostHorizon data gamma R epsilon
  change Real.rpow (Q / (K + 1 : ℝ)) gamma ≤ 1 + Real.rpow Q alpha
  have hQlocal : 0 < Q := by simpa [Q] using hQ
  have hgamma0 : 0 ≤ gamma := hgamma.le
  have halpha0 : 0 ≤ alpha := by
    dsimp [alpha, boostAlpha]
    positivity
  have halpha1 : alpha ≤ 1 := by
    dsimp [alpha, boostAlpha]
    have hden : 0 < 1 + gamma := by linarith
    exact (div_le_one hden).2 (by linarith)
  have hKpos : 0 < (K + 1 : ℝ) := by positivity
  have hratio0 : 0 ≤ Q / (K + 1 : ℝ) := div_nonneg hQlocal.le hKpos.le
  by_cases hQ1 : Q ≤ 1
  · have hratio1 : Q / (K + 1 : ℝ) ≤ 1 := by
      apply (div_le_one hKpos).2
      have : (1 : ℝ) ≤ K + 1 := by
        exact_mod_cast (show 1 ≤ K + 1 by omega)
      linarith
    calc
      Real.rpow (Q / (K + 1 : ℝ)) gamma ≤ 1 :=
        Real.rpow_le_one hratio0 hratio1 hgamma0
      _ ≤ 1 + Real.rpow Q alpha :=
        le_add_of_nonneg_right (Real.rpow_nonneg hQlocal.le alpha)
  · have h1Q : 1 ≤ Q := le_of_not_ge hQ1
    have hqaK : Real.rpow Q alpha ≤ (K : ℝ) := by
      exact (boostHorizon_bounds data gamma R epsilon hQ.le).1
    have hdenqa : 0 < Real.rpow Q alpha := Real.rpow_pos_of_pos hQlocal alpha
    have hratio : Q / (K + 1 : ℝ) ≤ Q / Real.rpow Q alpha := by
      apply div_le_div_of_nonneg_left hQlocal.le hdenqa
      linarith
    have hsub : Q / Real.rpow Q alpha = Real.rpow Q (1 - alpha) := by
      symm
      calc
        Real.rpow Q (1 - alpha) = Real.rpow Q 1 / Real.rpow Q alpha :=
          Real.rpow_sub hQlocal 1 alpha
        _ = Q / Real.rpow Q alpha := by
          congr 1
          exact Real.rpow_one Q
    have hpow := Real.rpow_le_rpow hratio0 hratio hgamma0
    rw [hsub] at hpow
    have hexp : (1 - alpha) * gamma = alpha := by
      dsimp [alpha, boostAlpha]
      field_simp
      ring
    have hnested : Real.rpow (Real.rpow Q (1 - alpha)) gamma =
        Real.rpow Q alpha := by
      calc
        Real.rpow (Real.rpow Q (1 - alpha)) gamma =
            Real.rpow Q ((1 - alpha) * gamma) :=
              (Real.rpow_mul hQlocal.le (1 - alpha) gamma).symm
        _ = Real.rpow Q alpha := by rw [hexp]
    calc
      Real.rpow (Q / (K + 1 : ℝ)) gamma ≤
          Real.rpow (Real.rpow Q (1 - alpha)) gamma := hpow
      _ = Real.rpow Q alpha := hnested
      _ ≤ 1 + Real.rpow Q alpha := by linarith

/-- The complete regularization prefactor in the explicit cap is balanced by
the chosen horizon, with one residual-log factor for the harmonic stepsize. -/
theorem boost_regularization_factor_le
    (data : VIPublicData E) (gamma R epsilon : ℝ)
    (hgamma : 0 < gamma) (hgamma1 : gamma ≤ 1)
    (hR : 0 < R) (hepsilon : 0 < epsilon) :
    let K := boostHorizon data gamma R epsilon
    Real.rpow (boostStepsize R epsilon K * data.Lp) gamma *
        Real.rpow R (((data.p - 1 : ℕ) : ℝ) * gamma) ≤
      32 * residualLog data R epsilon *
        (1 + Real.rpow (residualCondition data R epsilon) (boostAlpha gamma)) := by
  dsimp only
  let Q := residualCondition data R epsilon
  let alpha := boostAlpha gamma
  let K := boostHorizon data gamma R epsilon
  let LA := residualLog data R epsilon
  let h := 1 + harmonicR (K + 1)
  have hQ : 0 < Q := by
    dsimp [Q, residualCondition]
    exact div_pos (mul_pos data.Lp_pos (pow_pos hR _)) hepsilon
  have hgamma0 : 0 ≤ gamma := hgamma.le
  have halpha0 : 0 ≤ alpha := by
    dsimp [alpha, boostAlpha]
    positivity
  have halpha1 : alpha ≤ 1 := by
    dsimp [alpha, boostAlpha]
    exact (div_le_one (by linarith : 0 < 1 + gamma)).2 (by linarith)
  have hK : 2 ≤ K := boostHorizon_ge_two data gamma R epsilon
  obtain ⟨_hKsize, _hlogK, hlogK2⟩ :=
    boostHorizon_log_bounds data gamma R epsilon hR hQ halpha0 halpha1
  have hlogK2' : 1 + Real.log (K + 2 : ℝ) ≤ 3 * LA := by
    simpa [K, LA] using hlogK2
  have hT2 : 2 ≤ 2 + data.D / R + Q := by
    have hDR0 : 0 ≤ data.D / R := div_nonneg data.D_pos.le hR.le
    linarith [hlogK2']
  have hLA1 : 1 ≤ LA := by
    change 1 ≤ 1 + Real.log (2 + data.D / R + Q)
    linarith [Real.log_nonneg (by linarith : 1 ≤ 2 + data.D / R + Q)]
  have hh : h ≤ 4 * LA := by
    have hharm := harmonicR_le_one_add_log (K + 1) (by omega)
    have hlogmono := Real.log_le_log
      (by positivity : (0 : ℝ) < K + 1)
      (by norm_num : (K + 1 : ℝ) ≤ K + 2)
    norm_num at hharm hlogmono hlogK2'
    dsimp [h]
    linarith [hlogK2']
  have hh0 : 0 ≤ h := by
    dsimp [h]
    linarith [harmonicR_nonneg (K + 1)]
  have hKpos : 0 < (K + 1 : ℝ) := by positivity
  have hstepIdentity :
      boostStepsize R epsilon K * data.Lp * R ^ (data.p - 1) =
        8 * h * (Q / (K + 1 : ℝ)) := by
    have hpow : R ^ data.p = R ^ (data.p - 1) * R := by
      calc
        R ^ data.p = R ^ ((data.p - 1) + 1) :=
          congrArg (fun n : ℕ => R ^ n)
            (Nat.sub_add_cancel (by
              have hp2 := data.p_ge_two
              omega : 1 ≤ data.p)).symm
        _ = R ^ (data.p - 1) * R := pow_succ _ _
    dsimp [boostStepsize, h, Q, residualCondition]
    rw [hpow]
    field_simp
  have hleftIdentity :
      Real.rpow (boostStepsize R epsilon K * data.Lp) gamma *
          Real.rpow R (((data.p - 1 : ℕ) : ℝ) * gamma) =
        Real.rpow (8 * h * (Q / (K + 1 : ℝ))) gamma := by
    have hrpow : Real.rpow R (((data.p - 1 : ℕ) : ℝ) * gamma) =
        Real.rpow (R ^ (data.p - 1)) gamma :=
      Real.rpow_natCast_mul hR.le (data.p - 1) gamma
    rw [hrpow]
    calc
      Real.rpow (boostStepsize R epsilon K * data.Lp) gamma *
          Real.rpow (R ^ (data.p - 1)) gamma =
        Real.rpow ((boostStepsize R epsilon K * data.Lp) *
          R ^ (data.p - 1)) gamma :=
            (Real.mul_rpow
              (mul_nonneg (boostStepsize_pos hR hepsilon K).le data.Lp_pos.le)
              (pow_nonneg hR.le (data.p - 1))).symm
      _ = Real.rpow (8 * h * (Q / (K + 1 : ℝ))) gamma := by
        rw [hstepIdentity]
  have hratio0 : 0 ≤ Q / (K + 1 : ℝ) := div_nonneg hQ.le hKpos.le
  have hbaseBound : 8 * h * (Q / (K + 1 : ℝ)) ≤
      (32 * LA) * (Q / (K + 1 : ℝ)) := by
    exact mul_le_mul_of_nonneg_right (by nlinarith) hratio0
  have hbase0 : 0 ≤ 8 * h * (Q / (K + 1 : ℝ)) := by positivity
  have hpowBound := Real.rpow_le_rpow hbase0 hbaseBound hgamma0
  have h32LA1 : 1 ≤ 32 * LA := by nlinarith
  have h32pow : Real.rpow (32 * LA) gamma ≤ 32 * LA :=
    Real.rpow_le_self_of_one_le h32LA1 hgamma1
  have hratioPow0 : 0 ≤ Real.rpow (Q / (K + 1 : ℝ)) gamma :=
    Real.rpow_nonneg hratio0 gamma
  have hsplit : Real.rpow ((32 * LA) * (Q / (K + 1 : ℝ))) gamma =
      Real.rpow (32 * LA) gamma *
        Real.rpow (Q / (K + 1 : ℝ)) gamma :=
    Real.mul_rpow (by positivity) hratio0
  have hbalance := boost_balance data gamma R epsilon hgamma hQ
  change Real.rpow (boostStepsize R epsilon K * data.Lp) gamma *
      Real.rpow R (((data.p - 1 : ℕ) : ℝ) * gamma) ≤
        32 * LA * (1 + Real.rpow Q alpha)
  rw [hleftIdentity]
  calc
    Real.rpow (8 * h * (Q / (K + 1 : ℝ))) gamma ≤
        Real.rpow ((32 * LA) * (Q / (K + 1 : ℝ))) gamma := hpowBound
    _ = Real.rpow (32 * LA) gamma *
        Real.rpow (Q / (K + 1 : ℝ)) gamma := hsplit
    _ ≤ (32 * LA) * Real.rpow (Q / (K + 1 : ℝ)) gamma :=
      mul_le_mul_of_nonneg_right h32pow hratioPow0
    _ ≤ 32 * LA * (1 + Real.rpow Q alpha) :=
      mul_le_mul_of_nonneg_left hbalance (by positivity)

/-- The entire parenthesized work factor of the explicit shared cap has the
target residual exponent and four residual-log powers. -/
theorem boost_work_factor_le
    (data : VIPublicData E) (gamma R epsilon : ℝ)
    (hgamma : 0 < gamma) (hgamma1 : gamma ≤ 1)
    (hR : 0 < R) (hepsilon : 0 < epsilon)
    (ha23 : 2 / 3 ≤ ((data.p - 1 : ℕ) : ℝ) * gamma)
    (ha2 : ((data.p - 1 : ℕ) : ℝ) * gamma ≤ 2) :
    let K := boostHorizon data gamma R epsilon
    K + 1 + Real.rpow (boostStepsize R epsilon K * data.Lp) gamma *
        Real.rpow R (((data.p - 1 : ℕ) : ℝ) * gamma) *
          boostUa (((data.p - 1 : ℕ) : ℝ) * gamma) K ≤
      2656003 *
        (1 + Real.rpow (residualCondition data R epsilon) (boostAlpha gamma)) *
          (residualLog data R epsilon) ^ 4 := by
  dsimp only
  let Q := residualCondition data R epsilon
  let alpha := boostAlpha gamma
  let K := boostHorizon data gamma R epsilon
  let LA := residualLog data R epsilon
  let a := ((data.p - 1 : ℕ) : ℝ) * gamma
  have hQ : 0 < Q := by
    dsimp [Q, residualCondition]
    exact div_pos (mul_pos data.Lp_pos (pow_pos hR _)) hepsilon
  have halpha0 : 0 ≤ alpha := by
    dsimp [alpha, boostAlpha]
    positivity
  have halpha1 : alpha ≤ 1 := by
    dsimp [alpha, boostAlpha]
    exact (div_le_one (by linarith : 0 < 1 + gamma)).2 (by linarith)
  have hKsize := (boostHorizon_log_bounds data gamma R epsilon hR hQ
    halpha0 halpha1).1
  have hreg := boost_regularization_factor_le data gamma R epsilon
    hgamma hgamma1 hR hepsilon
  have ha0 : 0 ≤ a := by
    dsimp [a]
    positivity
  have hUa := boostUa_at_horizon_le data gamma R epsilon a hR hQ
    halpha0 halpha1 ha0 (by simpa [a] using ha23) (by simpa [a] using ha2)
  have hT2 : 2 ≤ 2 + data.D / R + Q := by
    have hDR0 : 0 ≤ data.D / R := div_nonneg data.D_pos.le hR.le
    linarith
  have hLA1 : 1 ≤ LA := by
    change 1 ≤ 1 + Real.log (2 + data.D / R + Q)
    linarith [Real.log_nonneg (by linarith : 1 ≤ 2 + data.D / R + Q)]
  have hqa0 : 0 ≤ Real.rpow Q alpha := Real.rpow_nonneg hQ.le alpha
  have htarget0 : 0 ≤ 1 + Real.rpow Q alpha := by positivity
  have hLA0 : 0 ≤ LA := by linarith
  have hreg0 : 0 ≤ Real.rpow (boostStepsize R epsilon K * data.Lp) gamma *
      Real.rpow R a := mul_nonneg
        (Real.rpow_nonneg
          (mul_nonneg (boostStepsize_pos hR hepsilon K).le data.Lp_pos.le) gamma)
        (Real.rpow_nonneg hR.le a)
  have hUa0 : 0 ≤ boostUa a K := by
    unfold boostUa
    apply add_nonneg
    · exact mul_nonneg (by norm_num) (Real.rpow_nonneg (by norm_num) a)
    · apply mul_nonneg (Real.rpow_nonneg (by norm_num) a)
      apply Finset.sum_nonneg
      intro j hj
      exact mul_nonneg (Real.rpow_nonneg (by
        linarith [harmonicR_nonneg (2 ^ (j + 1))]) a)
        (Real.rpow_nonneg (by norm_num) _)
  have hregUpper0 : 0 ≤ 32 * LA * (1 + Real.rpow Q alpha) := by positivity
  change (K : ℝ) + 1 +
      Real.rpow (boostStepsize R epsilon K * data.Lp) gamma *
        Real.rpow R a * boostUa a K ≤
      2656003 * (1 + Real.rpow Q alpha) * LA ^ 4
  have hprod :
      Real.rpow (boostStepsize R epsilon K * data.Lp) gamma *
          Real.rpow R a * boostUa a K ≤
        2656000 * (1 + Real.rpow Q alpha) * LA ^ 4 := by
    calc
      _ ≤ (32 * LA * (1 + Real.rpow Q alpha)) * (83000 * LA ^ 3) :=
        mul_le_mul hreg (by simpa [a, K, LA] using hUa) (by
          simpa [a, K] using hUa0) hregUpper0
      _ = 2656000 * (1 + Real.rpow Q alpha) * LA ^ 4 := by ring
  calc
    (K : ℝ) + 1 + Real.rpow (boostStepsize R epsilon K * data.Lp) gamma *
        Real.rpow R a * boostUa a K ≤
      3 * (1 + Real.rpow Q alpha) +
        2656000 * (1 + Real.rpow Q alpha) * LA ^ 4 :=
          add_le_add (by simpa [K, Q, alpha] using hKsize) hprod
    _ ≤ 2656003 * (1 + Real.rpow Q alpha) * LA ^ 4 := by
      have hLA4 : 1 ≤ LA ^ 4 := one_le_pow₀ hLA1
      nlinarith [mul_nonneg htarget0 (sub_nonneg.mpr (by linarith : 0 ≤ LA ^ 4 - 1))]

end


end LeanArticleAudit.Pilot
