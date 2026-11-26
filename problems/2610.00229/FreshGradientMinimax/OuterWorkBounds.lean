import FreshGradientMinimax.OuterComplete
import FreshGradientMinimax.OuterLogBounds

/-! The complete program's actual expected call count is bounded with a
G-independent logarithmic multiplier and a single cold-start logarithm. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
noncomputable section
namespace FreshGradientMinimax

theorem outer_solver_work_bound (p : Parameters) {η E : ℝ} (hη : 0 < η) (hE : 0 ≤ E)
    (hlog : valueLogFactor (3 * p.L) p.σ p.μ η ≤ 10000000 * logarithmicEnvelope p) :
    scscSolverWork (3 * p.L) p.L p.σ p.μ (η / 2) E ≤
      10 ^ 170 * logarithmicEnvelope p ^ 8 *
        (Real.sqrt ((3 * p.L) / p.μ) * Real.log (2 + ((3 * p.L) / p.μ) * E / η) + p.σ ^ 2 / (p.μ * η)) := by
  have hL := parameter_L_pos p
  have hμ := p.μ_pos
  have h := scscSolverWork_half_rate (ℓ := 3 * p.L) (α := p.L) (σ := p.σ)
    hμ (by linarith [p.μ_le_L]) hL (by linarith) hη hE
  have hv : 0 ≤ valueLogFactor (3 * p.L) p.σ p.μ η :=
    le_trans (by norm_num) (valueLogFactor_bounds (by positivity) hμ hη).1
  have hB : 0 ≤ Real.sqrt ((3 * p.L) / p.μ) * Real.log (2 + ((3 * p.L) / p.μ) * E / η) +
      p.σ ^ 2 / (p.μ * η) := by
    have hx : 0 ≤ ((3 * p.L) / p.μ) * E / η := by positivity
    have hl := Real.log_nonneg (show 1 ≤ 2 + ((3 * p.L) / p.μ) * E / η by linarith)
    positivity
  apply h.trans
  calc
    _ ≤ 10 ^ 114 * (10000000 * logarithmicEnvelope p) ^ 8 *
        (Real.sqrt ((3 * p.L) / p.μ) * Real.log (2 + ((3 * p.L) / p.μ) * E / η) + p.σ ^ 2 / (p.μ * η)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hv hlog 8) (by norm_num)) hB
    _ = _ := by ring

theorem outerRunWork_le_stage_bounds (L σ μ η Ec Ew bc bw : ℝ) {T : ℕ} (hT : 0 < T)
    (hbw : 0 ≤ bw)
    (hc : scscSolverWork (3 * L) L σ μ (η / 2) Ec ≤ bc)
    (hw : scscSolverWork (3 * L) L σ μ (η / 2) Ew ≤ bw) :
    outerRunWork L σ μ η Ec Ew T ≤ bc + T * bw := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hT)
  rw [outerRunWork_succ]
  have hn := mul_le_mul_of_nonneg_left hw (Nat.cast_nonneg n)
  push_cast
  nlinarith only [hc, hn, hbw]

theorem refinedOuterWork_rate (p : Parameters) (hreg : p.ε ^ 2 ≤ p.L * p.gap) :
    refinedOuterWork p.L p.σ p.μ p.gap p.G p.ε ≤ 10 ^ 190 * logarithmicEnvelope p ^ 10 * upperRate p := by
  let ηc := outerCoarseTolerance p.L p.ε
  let ηf := outerFineTolerance p.L p.μ p.ε
  let T := outerStepCount p.L p.gap p.ε
  let Ec := outerColdEnvelope p.L p.μ p.gap p.G ηc
  let Ew := outerWarmEnvelope p.gap ηc T
  let Λ := logarithmicEnvelope p
  let R := Real.sqrt ((3 * p.L) / p.μ)
  let C := 10 ^ 170 * Λ ^ 8
  let lc := Real.log (2 + ((3 * p.L) / p.μ) * Ec / ηc)
  let lw := Real.log (2 + ((3 * p.L) / p.μ) * Ew / ηc)
  let lf := Real.log (2 + ((3 * p.L) / p.μ) * (6 * ηc) / ηf)
  let nc := p.σ ^ 2 / (p.μ * ηc)
  let nf := p.σ ^ 2 / (p.μ * ηf)
  have hL := parameter_L_pos p
  have hμ := p.μ_pos
  have hηc : 0 < ηc := outerCoarseTolerance_pos hL p.ε_pos
  have hηf : 0 < ηf := outerFineTolerance_pos hL hμ p.ε_pos
  have hκ := p.condition_ge_one
  have hΔ : 0 < p.gap := by nlinarith [sq_pos_of_pos p.ε_pos]
  have hT : 0 < T := outerStepCount_pos hL hΔ p.ε_pos
  have hEc : 0 ≤ Ec := by dsimp [Ec, outerColdEnvelope]; positivity
  have hEw : 0 ≤ Ew := (NCObjective.outerWarmEnvelope_pos p.gap_nonneg hηc T).le
  have hΛ : 1 ≤ Λ := (logarithmicEnvelope_bounds p).1
  have hΛ0 : 0 ≤ Λ := by linarith
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  have hnc : 0 ≤ nc := by dsimp [nc]; positivity
  have hnf : 0 ≤ nf := by dsimp [nf]; positivity
  have hlw : 0 ≤ lw := by
    apply Real.log_nonneg
    have hx : 0 ≤ ((3 * p.L) / p.μ) * Ew / ηc := by positivity
    linarith
  have hc : scscSolverWork (3 * p.L) p.L p.σ p.μ (ηc / 2) Ec ≤ C * (R * lc + nc) :=
    outer_solver_work_bound p hηc hEc (outer_coarse_logfactor p)
  have hw : scscSolverWork (3 * p.L) p.L p.σ p.μ (ηc / 2) Ew ≤ C * (R * lw + nc) :=
    outer_solver_work_bound p hηc hEw (outer_coarse_logfactor p)
  have hf : scscSolverWork (3 * p.L) p.L p.σ p.μ (ηf / 2) (6 * ηc) ≤ C * (R * lf + nf) :=
    outer_solver_work_bound p hηf (by positivity) (outer_fine_logfactor p)
  have hcoarse := outerRunWork_le_stage_bounds p.L p.σ p.μ ηc Ec Ew _ _ hT (by positivity) hc hw
  have htotal : refinedOuterWork p.L p.σ p.μ p.gap p.G p.ε ≤
      C * (R * lc + nc + T * (R * lw + nc) + R * lf + nf) := by
    have h := add_le_add hcoarse hf
    change refinedOuterWork p.L p.σ p.μ p.gap p.G p.ε ≤ _ at h
    convert h using 1; ring
  have hA := outerGapRatio_one p hreg
  have hAp : 0 ≤ outerGapRatio p := outerGapRatio_nonneg p
  have hr := outer_sqrt_condition p
  have htc := outerStepCount_rate p hreg
  have hlc : lc ≤ 40000000 * outerColdLog p := outer_cold_log p hreg
  have hlw' : lw ≤ 300000000 * Λ := outer_warm_log p hreg
  have hlf : lf ≤ 100 * Λ := outer_fine_log p
  have hI : 0 ≤ outerColdLog p := by linarith [outerColdLog_half p]
  have hdet : Real.sqrt p.κ * outerGapRatio p = p.deterministic := (outer_deterministic_identity p).symm
  have hCold : R * lc ≤ 80000000 * (Real.sqrt p.κ * outerColdLog p) := by
    have h1 := mul_le_mul_of_nonneg_left hlc hR
    have h2 := mul_le_mul_of_nonneg_right hr (show 0 ≤ 40000000 * outerColdLog p by positivity)
    dsimp only [R] at *
    nlinarith only [h1, h2]
  have hWarm : (T : ℝ) * (R * lw) ≤ 600000600000000 * Λ * p.deterministic := by
    have h1 := mul_le_mul_of_nonneg_left hlw' hR
    have h2 := mul_le_mul_of_nonneg_right hr (show 0 ≤ 300000000 * Λ by positivity)
    have h3 : R * lw ≤ 600000000 * Λ * Real.sqrt p.κ := by nlinarith only [h1, h2]
    have h4 := mul_le_mul htc h3 (mul_nonneg hR hlw) (show 0 ≤ 1000001 * outerGapRatio p by positivity)
    rw [outer_deterministic_identity]
    nlinarith only [h4]
  have hFine : R * lf ≤ 200 * Λ * p.deterministic := by
    have h1 := mul_le_mul_of_nonneg_left hlf hR
    have h2 := mul_le_mul_of_nonneg_right hr (show 0 ≤ 100 * Λ by positivity)
    have h3 := mul_le_mul_of_nonneg_left hA (show 0 ≤ 200 * Λ * Real.sqrt p.κ by positivity)
    rw [outer_deterministic_identity]
    nlinarith only [h1, h2, h3]
  have hncEq : nc = 1000000 * (p.κ * p.σ ^ 2 / p.ε ^ 2) := outer_coarse_noise_identity p
  have hnfEq : nf = 1000000 * p.testing := outer_fine_noise_identity p
  have hU : 0 ≤ p.κ * p.σ ^ 2 / p.ε ^ 2 := by
    have : 0 ≤ p.κ := by linarith
    positivity
  have hNc : nc ≤ 1000000 * p.stochastic := by
    have h := mul_le_mul_of_nonneg_right hA hU
    rw [hncEq, outer_stochastic_identity]
    nlinarith only [h]
  have hTNc : (T : ℝ) * nc ≤ 1000001000000 * p.stochastic := by
    have h := mul_le_mul_of_nonneg_right htc hnc
    rw [hncEq] at h ⊢
    rw [outer_stochastic_identity]
    nlinarith only [h]
  have hp := upperRate_components p
  have hds := mul_le_mul_of_nonneg_right hΛ hp.2.1
  have hdu := mul_le_mul_of_nonneg_right hΛ hp.2.2.1
  have hdi := mul_le_mul_of_nonneg_right hΛ hp.2.2.2
  have hdd : 0 ≤ Λ * p.deterministic := mul_nonneg hΛ0 hp.1
  have hinner : R * lc + nc + T * (R * lw + nc) + R * lf + nf ≤ 10 ^ 16 * Λ * upperRate p := by
    rw [upperRate_identity]
    nlinarith only [hCold, hWarm, hFine, hNc, hTNc, hnfEq, hds, hdu, hdi, hdd,
      mul_nonneg hΛ0 hp.2.1, mul_nonneg hΛ0 hp.2.2.1, mul_nonneg hΛ0 hp.2.2.2]
  have hrate : 0 ≤ upperRate p := le_trans (by norm_num) (upperRate_one p hreg)
  have hpow : Λ ^ 9 ≤ Λ ^ 10 := pow_le_pow_right₀ hΛ (by decide)
  calc
    _ ≤ C * (10 ^ 16 * Λ * upperRate p) := htotal.trans (mul_le_mul_of_nonneg_left hinner hC)
    _ = 10 ^ 186 * Λ ^ 9 * upperRate p := by dsimp [C]; ring
    _ ≤ 10 ^ 186 * Λ ^ 10 * upperRate p :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by norm_num)) hrate
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_right (by norm_num : (10 ^ 186 : ℝ) ≤ 10 ^ 190)
        (show 0 ≤ Λ ^ 10 * upperRate p by positivity)
      simpa only [mul_assoc] using h

end FreshGradientMinimax
