import HeavyTail.LocalizationTuning

/-! The manuscript's scalar online tuning, including the optimization residual.
The bounds here are algebraic consequences of the displayed parameters; no
regret, stochastic, or final error estimate is assumed. -/
noncomputable section
namespace HeavyTail

def onlineStep (p M V s R ell n : ℝ) : ℝ :=
  min (1 / (16 * M * R))
    (min (ell / (R * Real.sqrt (n * (V + M ^ 2))))
      ((ell / n) ^ (1 / p) / (s * R)))

def onlineSmoothing (R ell : ℝ) : ℝ := R / Real.sqrt ell
def onlineQuadratic (η M R n : ℝ) : ℝ := η * M * Real.sqrt n / R
def onlineResidual (η M R n : ℝ) : ℝ := η * M * R / (8 * n)

theorem onlineStep_pos {p M V s R ell n : ℝ} (hM : 0 < M) (hV : 0 ≤ V)
    (hs : 0 < s) (hR : 0 < R) (hell : 0 < ell) (hn : 0 < n) :
    0 < onlineStep p M V s R ell n := by
  unfold onlineStep
  have hA : 0 < V + M ^ 2 := by positivity
  exact lt_min (by positivity) (lt_min (by positivity)
    (div_pos (Real.rpow_pos_of_pos (div_pos hell hn) _) (mul_pos hs hR)))

theorem onlineStep_bounds (p M V s R ell n : ℝ) :
    onlineStep p M V s R ell n ≤ 1 / (16 * M * R) ∧
    onlineStep p M V s R ell n ≤ ell / (R * Real.sqrt (n * (V + M ^ 2))) ∧
    onlineStep p M V s R ell n ≤ (ell / n) ^ (1 / p) / (s * R) := by
  exact ⟨min_le_left _ _, (min_le_right _ _).trans (min_le_left _ _),
    (min_le_right _ _).trans (min_le_right _ _)⟩

theorem onlineStep_admissible {p M V s R ell n : ℝ} (hM : 0 < M) (hR : 0 < R) :
    onlineStep p M V s R ell n * M * R ≤ 1 / 16 := by
  have h := mul_le_mul_of_nonneg_right
    (onlineStep_bounds p M V s R ell n).1 (mul_pos hM hR).le
  have he : 1 / (16 * M * R) * (M * R) = 1 / 16 := by field_simp; ring
  rw [he] at h
  simpa only [mul_assoc] using h

theorem onlineSmoothing_bounds {R ell : ℝ} (hR : 0 < R) (hell : 1 ≤ ell) :
    0 < onlineSmoothing R ell ∧ onlineSmoothing R ell ≤ R ∧
    (onlineSmoothing R ell) ^ 2 = R ^ 2 / ell := by
  have he : 0 < ell := lt_of_lt_of_le zero_lt_one hell
  have hs : 1 ≤ Real.sqrt ell := by simpa using Real.sqrt_le_sqrt hell
  refine ⟨div_pos hR (Real.sqrt_pos.2 he), ?_, ?_⟩
  · exact (div_le_iff₀ (Real.sqrt_pos.2 he)).2 (by nlinarith)
  · unfold onlineSmoothing
    rw [div_pow, Real.sq_sqrt he.le]

theorem onlineQuadratic_pos {η M R n : ℝ} (hη : 0 < η) (hM : 0 < M)
    (hR : 0 < R) (hn : 0 < n) : 0 < onlineQuadratic η M R n := by
  unfold onlineQuadratic
  positivity

theorem online_beta_balance {η M R n : ℝ} (hη : 0 < η) (hM : 0 < M)
    (hR : 0 < R) (hn : 0 < n) :
    ((onlineQuadratic η M R n) * R ^ 2 / 2 +
      n * (η ^ 2 * M ^ 2 / (2 * onlineQuadratic η M R n))) / (η * n) =
      M * R / Real.sqrt n := by
  have hs : Real.sqrt n ≠ 0 := (Real.sqrt_pos.2 hn).ne'
  have hsq := Real.sq_sqrt hn.le
  unfold onlineQuadratic
  field_simp
  nlinarith only [congrArg (fun t : ℝ => 2 * η ^ 2 * M ^ 2 * R ^ 2 * Real.sqrt n * t) hsq]

theorem online_residual_balance {η M R n : ℝ} (hη : 0 < η) (hn : 0 < n) :
    onlineResidual η M R n / η = M * R / (8 * n) := by
  unfold onlineResidual
  field_simp
  <;> ring

theorem online_power_balance {p η s R ell n : ℝ} (hp : 1 < p) (hη : 0 < η)
    (hs : 0 < s) (hR : 0 < R) (hell : 0 < ell) (hn : 0 < n)
    (hstep : η ≤ (ell / n) ^ (1 / p) / (s * R)) :
    η ^ (p - 1) * (s * R) ^ p ≤ s * R * (ell / n) ^ (1 - 1 / p) := by
  have hsr := mul_pos hs hR
  have he : (1 / p) * (p - 1) = 1 - 1 / p := by field_simp
  have hh : η * (s * R) ≤ (ell / n) ^ (1 / p) := (le_div_iff₀ hsr).mp hstep
  have hpow := mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow (mul_pos hη hsr).le hh (by linarith : 0 ≤ p - 1)) hsr.le
  rw [Real.mul_rpow hη.le hsr.le, ← Real.rpow_mul (div_pos hell hn).le, he,
    Real.rpow_sub_one hsr.ne' p] at hpow
  have hid : η ^ (p - 1) * ((s * R) ^ p / (s * R)) * (s * R) =
      η ^ (p - 1) * (s * R) ^ p := by field_simp
  simpa only [hid, mul_comm (s * R)] using hpow

theorem online_trace_balance {η M V R ell n : ℝ} (hM : 0 < M) (hV : 0 ≤ V)
    (hR : 0 < R) (hell : 0 < ell) (hn : 0 < n)
    (hstep : η ≤ ell / (R * Real.sqrt (n * (V + M ^ 2)))) :
    η * R ^ 2 * (V + M ^ 2) / ell ≤ R * Real.sqrt ((V + M ^ 2) / n) := by
  have hA : 0 < V + M ^ 2 := by positivity
  have hsN : 0 < Real.sqrt n := Real.sqrt_pos.2 hn
  have hsA : 0 < Real.sqrt (V + M ^ 2) := Real.sqrt_pos.2 hA
  calc
    _ ≤ (ell / (R * Real.sqrt (n * (V + M ^ 2)))) * R ^ 2 *
        (V + M ^ 2) / ell := by gcongr
    _ = _ := by
      rw [Real.sqrt_mul hn.le, Real.sqrt_div hA.le]
      field_simp
      nlinarith only [congrArg (fun t : ℝ => ell * R ^ 2 * Real.sqrt n * t)
        (Real.sq_sqrt hA.le)]

theorem online_trace_rate {M V n : ℝ} (hM : 0 ≤ M) (hV : 0 ≤ V) (hn : 0 < n) :
    Real.sqrt ((V + M ^ 2) / n) ≤ (M + Real.sqrt V) / Real.sqrt n := by
  rw [Real.sqrt_div (by positivity : 0 ≤ V + M ^ 2)]
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg n)
  apply (Real.sqrt_le_iff).2
  constructor
  · positivity
  · nlinarith [Real.sq_sqrt hV, mul_nonneg hM (Real.sqrt_nonneg V)]

theorem online_inverse_heavy_identity {p s R ell n : ℝ} (hs : 0 < s)
    (hR : 0 < R) (hell : 0 < ell) (hn : 0 < n) :
    ell / (((ell / n) ^ (1 / p) / (s * R)) * n) =
      s * R * (ell / n) ^ (1 - 1 / p) := by
  have hx := div_pos hell hn
  rw [Real.rpow_sub hx 1 (1 / p), Real.rpow_one]
  field_simp
  <;> ring

theorem online_inverse_trace_identity {M V R ell n : ℝ} (hM : 0 < M)
    (hV : 0 ≤ V) (hR : 0 < R) (hell : 0 < ell) (hn : 0 < n) :
    ell / ((ell / (R * Real.sqrt (n * (V + M ^ 2)))) * n) =
      R * Real.sqrt ((V + M ^ 2) / n) := by
  have hA : 0 < V + M ^ 2 := by positivity
  rw [Real.sqrt_mul hn.le, Real.sqrt_div hA.le]
  have hsq := Real.sq_sqrt hn.le
  have hsN : Real.sqrt n ≠ 0 := (Real.sqrt_pos.2 hn).ne'
  field_simp
  nlinarith only [congrArg (fun t : ℝ => ell * R * Real.sqrt (V + M ^ 2) * t) hsq]

theorem online_inverse_balance {p M V s R ell n : ℝ} (hM : 0 < M)
    (hV : 0 ≤ V) (hs : 0 < s) (hR : 0 < R) (hell : 0 < ell) (hn : 0 < n) :
    ell / (onlineStep p M V s R ell n * n) ≤
      16 * M * R * ell / n + R * Real.sqrt ((V + M ^ 2) / n) +
        s * R * (ell / n) ^ (1 - 1 / p) := by
  have hfirst : ell / ((1 / (16 * M * R)) * n) = 16 * M * R * ell / n := by
    field_simp
    <;> ring
  have htrace := online_inverse_trace_identity hM hV hR hell hn
  have hheavy := online_inverse_heavy_identity (p := p) hs hR hell hn
  have h1 : 0 ≤ 16 * M * R * ell / n := by positivity
  have h2 : 0 ≤ R * Real.sqrt ((V + M ^ 2) / n) := by positivity
  have h3 : 0 ≤ s * R * (ell / n) ^ (1 - 1 / p) := by positivity
  unfold onlineStep
  rcases le_total (1 / (16 * M * R))
      (min (ell / (R * Real.sqrt (n * (V + M ^ 2))))
        ((ell / n) ^ (1 / p) / (s * R))) with h | h
  · rw [min_eq_left h, hfirst]
    linarith
  · rw [min_eq_right h]
    rcases le_total (ell / (R * Real.sqrt (n * (V + M ^ 2))))
        ((ell / n) ^ (1 / p) / (s * R)) with h | h
    · rw [min_eq_left h, htrace]
      linarith
    · rw [min_eq_right h, hheavy]
      linarith

end HeavyTail
