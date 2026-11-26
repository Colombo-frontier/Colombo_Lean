import NCBall.FullChainBound

/-! # Absorbing the finite room union into a logarithmic dimension condition -/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace NCBall

theorem exponential_prefactor_bound {n : ℕ} {P : ℝ} (hP : 0 < P)
    (hlog : 8 * Real.log (4 * P) ≤ n) : P * Real.exp (-(n : ℝ) / 8) ≤ 1 / 4 := by
  have he : 4 * P ≤ Real.exp ((n : ℝ) / 8) := by
    rw [← Real.exp_log (by positivity : 0 < 4 * P)]
    exact Real.exp_le_exp.mpr (by linarith)
  have hm := mul_le_mul_of_nonneg_right he (Real.exp_pos (-(n : ℝ) / 8)).le
  have hid : Real.exp ((n : ℝ) / 8) * Real.exp (-(n : ℝ) / 8) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  rw [hid] at hm
  nlinarith

theorem chain_prefactor_log {M q₀ N n : ℕ} (hq : 0 < q₀) (hN : N < M * q₀)
    (hlog : 40 * Real.log (2 + (M * q₀ : ℕ)) ≤ n) :
    8 * Real.log (4 * ((N : ℝ) + 1) * M * ((M : ℝ) + 1)) ≤ n := by
  have hM : 0 < M := by nlinarith
  have hMq : M ≤ M * q₀ := Nat.le_mul_of_pos_right M hq
  have hNc : (N : ℝ) + 1 ≤ (M * q₀ : ℕ) := by exact_mod_cast hN
  have hMc : (M : ℝ) ≤ (M * q₀ : ℕ) := by exact_mod_cast hMq
  let a : ℝ := 2 + (M * q₀ : ℕ)
  have ha : 2 ≤ a := by dsimp [a]; linarith [Nat.cast_nonneg (α := ℝ) (M * q₀)]
  have hn' : (N : ℝ) + 1 ≤ a := by dsimp [a]; linarith
  have hm' : (M : ℝ) ≤ a := by dsimp [a]; linarith
  have hm1 : (M : ℝ) + 1 ≤ a := by dsimp [a]; linarith
  have hprod : ((N : ℝ) + 1) * M * ((M : ℝ) + 1) ≤ a ^ 3 := by
    have h1 := mul_le_mul hn' hm' (Nat.cast_nonneg M) (by linarith : 0 ≤ a)
    have h2 := mul_le_mul h1 hm1 (by positivity : 0 ≤ (M : ℝ) + 1)
      (by positivity : 0 ≤ a * a)
    nlinarith
  have hfour : 4 ≤ a ^ 2 := by nlinarith
  have hpow : 4 * (((N : ℝ) + 1) * M * ((M : ℝ) + 1)) ≤ a ^ 5 := by
    have hp := mul_le_mul_of_nonneg_right hfour (by positivity : 0 ≤ a ^ 3)
    nlinarith
  have hp : 0 < 4 * ((N : ℝ) + 1) * M * ((M : ℝ) + 1) := by positivity
  have hl := Real.log_le_log hp (show 4 * ((N : ℝ) + 1) * M * ((M : ℝ) + 1) ≤ a ^ 5 by nlinarith)
  rw [Real.log_pow] at hl
  dsimp only [a] at hl
  norm_num only [Nat.cast_ofNat] at hl
  linarith

theorem full_chain_terminal_quarter {R : Type*} [MeasurableSpace R]
    {n H M q₀ N : ℕ} (ν : Measure R) [IsProbabilityMeasure ν]
    (p : RoomQueryPolicy R n H) (hq : 0 < q₀) (hN : N < M * q₀) (hn : 0 < n)
    {ρ σ : ℝ} (hρ : 0 < ρ) (hσ : 0 < σ) (γ lam : ℝ)
    (hqcap : (q₀ : ℝ) ≤ n * σ ^ 2 / 16)
    (hlog : 40 * Real.log (2 + (M * q₀ : ℕ)) ≤ n)
    (out : LinearHistory R N → Space n) (hout : Measurable out) :
    (ν.prod (roomLatentLaw n H M))
      (fullRealTerminalEvent p ρ γ lam σ (Real.sqrt (n : ℝ))⁻¹ N out) ≤ 1 / 4 := by
  have hM : 0 < M := by nlinarith
  have hp := exponential_prefactor_bound
    (show 0 < ((N : ℝ) + 1) * M * ((M : ℝ) + 1) by positivity)
    (by simpa only [mul_assoc] using chain_prefactor_log hq hN hlog)
  apply (full_chain_terminal_bound ν p hq hN hn hρ hσ γ lam hqcap out hout).trans
  have he := ENNReal.ofReal_le_ofReal hp
  simpa only [ENNReal.ofReal_mul (by positivity : 0 ≤ ((N : ℝ) + 1) * M * ((M : ℝ) + 1)),
    ENNReal.ofReal_mul (by positivity : 0 ≤ ((N : ℝ) + 1) * M),
    ENNReal.ofReal_mul (by positivity : 0 ≤ (N : ℝ) + 1),
    ENNReal.ofReal_add (by positivity : 0 ≤ (N : ℝ)) (by norm_num : (0 : ℝ) ≤ 1),
    ENNReal.ofReal_add (by positivity : 0 ≤ (M : ℝ)) (by norm_num : (0 : ℝ) ≤ 1),
    ENNReal.ofReal_natCast, ENNReal.ofReal_one,
    ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4), ENNReal.ofReal_ofNat] using he

end NCBall
