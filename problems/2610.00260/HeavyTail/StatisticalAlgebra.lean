import HeavyTail.ThresholdChoice

/-! Exact split-amplitude identities and constant comparisons for the
statistical corollaries. These lemmas have only scalar hypotheses. -/
noncomputable section
namespace HeavyTail

def heavyAmplitude (L s p δ : ℝ) (T : ℕ) : ℝ :=
  s * ((L ^ 2 / s ^ 2 + confidenceLog δ) / T) ^ (1 - 1 / p)

def heavyDimensionTerm (L s p : ℝ) (T : ℕ) : ℝ :=
  s * (L ^ 2 / s ^ 2) ^ (1 - 1 / p) / (T : ℝ) ^ (1 - 1 / p)

def heavyConfidenceTerm (s p δ : ℝ) (T : ℕ) : ℝ :=
  s * (confidenceLog δ) ^ (1 - 1 / p) / (T : ℝ) ^ (1 - 1 / p)

def heavySquareScale (L s p δ : ℝ) (T : ℕ) : ℝ :=
  ((s * (L ^ 2 / s ^ 2) ^ (1 - 1 / p)) ^ 2 +
    s ^ 2 * (confidenceLog δ) ^ (2 * (1 - 1 / p))) /
      (T : ℝ) ^ (2 * (1 - 1 / p))

def quadraticStatisticalScale (L s p δ : ℝ) (T : ℕ) : ℝ :=
  L ^ 2 / T + heavySquareScale L s p δ T

theorem rpow_square_of_nonneg {x q : ℝ} (hx : 0 ≤ x) (hq : 0 ≤ q) :
    (x ^ q) ^ 2 = x ^ (2 * q) := by
  rw [show 2 * q = q + q by ring, Real.rpow_add_of_nonneg hx hq hq, pow_two]

theorem heavyAmplitude_split (θ : OracleParameters) :
    heavyAmplitude θ.L θ.s θ.p θ.δ θ.T ≤
        heavyDimensionTerm θ.L θ.s θ.p θ.T + heavyConfidenceTerm θ.s θ.p θ.δ θ.T ∧
    heavyDimensionTerm θ.L θ.s θ.p θ.T + heavyConfidenceTerm θ.s θ.p θ.δ θ.T ≤
        2 * heavyAmplitude θ.L θ.s θ.p θ.δ θ.T := by
  let e := θ.L ^ 2 / θ.s ^ 2
  let ell := confidenceLog θ.δ
  let q := 1 - 1 / θ.p
  have he : 0 ≤ e := by dsimp [e]; positivity
  have hell : 0 ≤ ell := (confidenceLog_pos θ.δ_pos θ.δ_lt_tenth).le
  have hq := heavyTailExponent_mem θ.p_gt_one
  have ht : 0 ≤ (θ.T : ℝ) := Nat.cast_nonneg _
  have hspos := θ.s_pos
  have hu : heavyAmplitude θ.L θ.s θ.p θ.δ θ.T = θ.s * (e + ell) ^ q / (θ.T : ℝ) ^ q := by
    unfold heavyAmplitude
    rw [Real.div_rpow (add_nonneg he hell) ht, mul_div_assoc]
  rw [hu]
  change θ.s * (e + ell) ^ q / (θ.T : ℝ) ^ q ≤
      θ.s * e ^ q / (θ.T : ℝ) ^ q + θ.s * ell ^ q / (θ.T : ℝ) ^ q ∧ _
  have hsub := Real.rpow_add_le_add_rpow he hell hq.1 hq.2
  have h1 := Real.rpow_le_rpow he (le_add_of_nonneg_right hell) hq.1
  have h2 := Real.rpow_le_rpow hell (le_add_of_nonneg_left he) hq.1
  have hs : 0 ≤ θ.s / (θ.T : ℝ) ^ q := by positivity
  change (e + ell) ^ q ≤ e ^ q + ell ^ q at hsub
  have hboth : e ^ q + ell ^ q ≤ 2 * (e + ell) ^ q := by
    dsimp only [q]
    linarith only [h1, h2]
  constructor
  · convert mul_le_mul_of_nonneg_left hsub hs using 1 <;> ring
  · change θ.s * e ^ q / (θ.T : ℝ) ^ q + θ.s * ell ^ q / (θ.T : ℝ) ^ q ≤ _
    convert mul_le_mul_of_nonneg_left hboth hs using 1 <;> ring

theorem heavySquareScale_eq (θ : OracleParameters) :
    heavySquareScale θ.L θ.s θ.p θ.δ θ.T =
      (heavyDimensionTerm θ.L θ.s θ.p θ.T) ^ 2 + (heavyConfidenceTerm θ.s θ.p θ.δ θ.T) ^ 2 := by
  have hq := (heavyTailExponent_mem θ.p_gt_one).1
  have hell := (confidenceLog_pos θ.δ_pos θ.δ_lt_tenth).le
  unfold heavySquareScale heavyDimensionTerm heavyConfidenceTerm
  simp only [div_pow, mul_pow]
  rw [rpow_square_of_nonneg (Nat.cast_nonneg _) hq,
    rpow_square_of_nonneg hell hq]
  ring

theorem heavyAmplitude_square_comparison (θ : OracleParameters) :
    heavySquareScale θ.L θ.s θ.p θ.δ θ.T ≤ 4 * (heavyAmplitude θ.L θ.s θ.p θ.δ θ.T) ^ 2 ∧
    (heavyAmplitude θ.L θ.s θ.p θ.δ θ.T) ^ 2 ≤ 2 * heavySquareScale θ.L θ.s θ.p θ.δ θ.T := by
  have hs := θ.s_pos
  have hell := (confidenceLog_pos θ.δ_pos θ.δ_lt_tenth).le
  have hx : 0 ≤ heavyDimensionTerm θ.L θ.s θ.p θ.T := by unfold heavyDimensionTerm; positivity
  have hy : 0 ≤ heavyConfidenceTerm θ.s θ.p θ.δ θ.T := by unfold heavyConfidenceTerm; positivity
  have hu : 0 ≤ heavyAmplitude θ.L θ.s θ.p θ.δ θ.T := by unfold heavyAmplitude; positivity
  have hb := heavyAmplitude_split θ
  rw [heavySquareScale_eq]
  have hupper := pow_le_pow_left₀ hu hb.1 2
  have hlower := pow_le_pow_left₀ (add_nonneg hx hy) hb.2 2
  constructor
  · nlinarith only [hlower, mul_nonneg hx hy]
  · nlinarith only [hupper, sq_nonneg (heavyDimensionTerm θ.L θ.s θ.p θ.T - heavyConfidenceTerm θ.s θ.p θ.δ θ.T)]

theorem statisticalAmplitude_eq_trace_heavy (L s p δ : ℝ) (T : ℕ) :
    statisticalAmplitude L s p δ T = L / Real.sqrt T + heavyAmplitude L s p δ T := rfl

end HeavyTail
