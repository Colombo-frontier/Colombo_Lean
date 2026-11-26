import HeavyTail.StageBudgets
import HeavyTail.ConfidenceCalibration

/-! Scalar tuning of the manuscript's localization phase. The explicit ceiling
budget controls all three primitive terms; the public warm-radius inequality
also implies n≥ell. No stochastic estimate is assumed in this module. -/
noncomputable section
namespace HeavyTail

def localizationScale (C₀ : ℝ) : ℝ := 32 * (C₀ + 1)

def localizationBudgetConstant (q C₀ : ℝ) : ℝ :=
  2 * (localizationScale C₀) ^ 2 + localizationScale C₀ +
    (localizationScale C₀) ^ (1 / q) + 2

def localizationPhaseWeight (G V s μ R q ell : ℝ) : ℝ :=
  (G ^ 2 + V) / (μ ^ 2 * R ^ 2) + G * ell / (μ * R) +
    ell * (s / (μ * R)) ^ (1 / q)

def localizationPhaseBudget (G V s μ R q ell C₀ : ℝ) : ℕ :=
  ⌈localizationBudgetConstant q C₀ * localizationPhaseWeight G V s μ R q ell⌉₊

theorem localizationScale_pos {C₀ : ℝ} (hC₀ : 0 ≤ C₀) : 0 < localizationScale C₀ := by
  unfold localizationScale
  positivity

theorem localizationBudgetConstant_bounds {q C₀ : ℝ} (hC₀ : 0 ≤ C₀) :
    2 ≤ localizationBudgetConstant q C₀ ∧
    2 * (localizationScale C₀) ^ 2 ≤ localizationBudgetConstant q C₀ ∧
    localizationScale C₀ ≤ localizationBudgetConstant q C₀ ∧
    (localizationScale C₀) ^ (1 / q) ≤ localizationBudgetConstant q C₀ := by
  have hK := (localizationScale_pos hC₀).le
  have hp := Real.rpow_nonneg hK (1 / q)
  unfold localizationBudgetConstant
  constructor
  · linarith [sq_nonneg (localizationScale C₀)]
  constructor
  · linarith [sq_nonneg (localizationScale C₀)]
  constructor <;> linarith [sq_nonneg (localizationScale C₀)]

theorem power_term_of_budget {s ell n ε q : ℝ} (hs : 0 ≤ s) (hell : 0 ≤ ell)
    (hn : 0 < n) (hε : 0 < ε) (hq : 0 < q)
    (hbudget : ell * (s / ε) ^ (1 / q) ≤ n) :
    s * (ell / n) ^ q ≤ ε := by
  by_cases hs0 : s = 0
  · simp [hs0, hε.le]
  have hspos : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
  let A := (s / ε) ^ (1 / q)
  have hA : 0 < A := Real.rpow_pos_of_pos (div_pos hspos hε) _
  have hratio : ell / n ≤ A⁻¹ := by
    apply (div_le_iff₀ hn).mpr
    have hh := mul_le_mul_of_nonneg_left hbudget (inv_nonneg.mpr hA.le)
    have he : A⁻¹ * (ell * A) = ell := by field_simp
    change A⁻¹ * (ell * A) ≤ A⁻¹ * n at hh
    rwa [he] at hh
  have hp := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (div_nonneg hell hn.le) hratio hq.le) hs
  apply hp.trans_eq
  dsimp [A]
  rw [Real.inv_rpow (Real.rpow_nonneg (div_nonneg hs hε.le) _), ← Real.rpow_mul (div_nonneg hs hε.le),
    one_div_mul_cancel hq.ne', Real.rpow_one]
  field_simp

theorem root_term_of_budget {G V a K n : ℝ} (hG : 0 ≤ G) (hV : 0 ≤ V)
    (ha : 0 < a) (hK : 0 < K) (hn : 0 < n)
    (hbudget : 2 * K ^ 2 * (G ^ 2 + V) / a ^ 2 ≤ n) :
    (G + Real.sqrt V) / Real.sqrt n ≤ a / K := by
  have hsV := Real.sq_sqrt hV
  have hsum : (G + Real.sqrt V) ^ 2 ≤ 2 * (G ^ 2 + V) := by
    nlinarith only [sq_nonneg (G - Real.sqrt V), hsV]
  have hprod := mul_le_mul_of_nonneg_left hsum (sq_nonneg K)
  have hb := (div_le_iff₀ (sq_pos_of_pos ha)).mp hbudget
  have hsquare : (K * (G + Real.sqrt V)) ^ 2 ≤ (a * Real.sqrt n) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hn.le]
    nlinarith only [hprod, hb]
  have hlin := (sq_le_sq₀ (mul_nonneg hK.le (add_nonneg hG (Real.sqrt_nonneg _)))
    (mul_nonneg ha.le (Real.sqrt_nonneg _))).mp hsquare
  apply (div_le_iff₀ (Real.sqrt_pos.mpr hn)).mpr
  have hd := (le_div_iff₀ hK).mpr
    (show (G + Real.sqrt V) * K ≤ a * Real.sqrt n by simpa only [mul_comm K] using hlin)
  convert hd using 1 <;> ring

theorem localizationPhaseWeight_nonneg {G V s μ R q ell : ℝ}
    (hG : 0 ≤ G) (hV : 0 ≤ V) (hs : 0 ≤ s) (hμ : 0 < μ) (hR : 0 < R)
    (hell : 0 ≤ ell) : 0 ≤ localizationPhaseWeight G V s μ R q ell := by
  unfold localizationPhaseWeight
  positivity

/-- The ceiling budget dominates each term separately. -/
theorem localizationPhaseBudget_components {G V s μ R q ell C₀ : ℝ}
    (hG : 0 ≤ G) (hV : 0 ≤ V) (hs : 0 ≤ s) (hμ : 0 < μ) (hR : 0 < R)
    (hell : 0 ≤ ell) (hC₀ : 0 ≤ C₀) :
    let n := (localizationPhaseBudget G V s μ R q ell C₀ : ℝ)
    2 * (localizationScale C₀) ^ 2 * (G ^ 2 + V) / (μ * R) ^ 2 ≤ n ∧
    localizationScale C₀ * G * ell / (μ * R) ≤ n ∧
    ell * (s / (μ * R / localizationScale C₀)) ^ (1 / q) ≤ n ∧
    2 * G * ell / (μ * R) ≤ n := by
  let C := localizationBudgetConstant q C₀
  let w := localizationPhaseWeight G V s μ R q ell
  let n := (localizationPhaseBudget G V s μ R q ell C₀ : ℝ)
  have hn : C * w ≤ n := Nat.le_ceil _
  have hw0 : 0 ≤ w := localizationPhaseWeight_nonneg hG hV hs hμ hR hell
  have hc := localizationBudgetConstant_bounds (q := q) hC₀
  have hA : 0 ≤ (G ^ 2 + V) / (μ ^ 2 * R ^ 2) := by positivity
  have hL : 0 ≤ G * ell / (μ * R) := by positivity
  have hP : 0 ≤ ell * (s / (μ * R)) ^ (1 / q) := by positivity
  have h1 : (G ^ 2 + V) / (μ ^ 2 * R ^ 2) ≤ w := by dsimp [w, localizationPhaseWeight]; linarith
  have h2 : G * ell / (μ * R) ≤ w := by dsimp [w, localizationPhaseWeight]; linarith
  have h3 : ell * (s / (μ * R)) ^ (1 / q) ≤ w := by dsimp [w, localizationPhaseWeight]; linarith
  have hC : 0 ≤ C := (by norm_num : (0 : ℝ) ≤ 2).trans hc.1
  have hb1 := (mul_le_mul hc.2.1 h1 (by positivity) hC).trans hn
  have hb2 := (mul_le_mul hc.2.2.1 h2 (by positivity) hC).trans hn
  have hb3 := (mul_le_mul hc.2.2.2 h3 (by positivity) hC).trans hn
  have hb4 := (mul_le_mul hc.1 h2 (by positivity) hC).trans hn
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [mul_pow, mul_div_assoc] using hb1
  · simpa only [mul_div_assoc, mul_assoc] using hb2
  · have he : s / (μ * R / localizationScale C₀) =
        localizationScale C₀ * (s / (μ * R)) := by field_simp; ring
    rw [he, Real.mul_rpow (localizationScale_pos hC₀).le (by positivity)]
    nlinarith only [hb3]
  · simpa only [mul_div_assoc, mul_assoc] using hb4

/-- Warm-start radius ensures the rounded accepted budget is at least the
confidence logarithm, so the primitive's confidence-size condition is met. -/
theorem localizationPhaseBudget_ge_confidence {G V s μ R q ell C₀ : ℝ}
    (hG : 0 ≤ G) (hV : 0 ≤ V) (hs : 0 ≤ s) (hμ : 0 < μ) (hR : 0 < R)
    (hell : 0 ≤ ell) (hC₀ : 0 ≤ C₀) (hwarm : R ≤ Real.sqrt 2 * G / μ) :
    ell ≤ (localizationPhaseBudget G V s μ R q ell C₀ : ℝ) := by
  have hroot : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hw := (le_div_iff₀ hμ).mp hwarm
  have hmul := mul_le_mul_of_nonneg_right hroot hG
  have hbase : μ * R ≤ 2 * G := by nlinarith only [hw, hmul]
  have hterm : ell ≤ 2 * G * ell / (μ * R) := by
    apply (le_div_iff₀ (mul_pos hμ hR)).mpr
    nlinarith only [mul_le_mul_of_nonneg_right hbase hell]
  exact hterm.trans (localizationPhaseBudget_components hG hV hs hμ hR hell hC₀).2.2.2

/-- Explicit scalar phase tuning yields the error required to halve radius. -/
theorem localizationPhaseBudget_error {G V s μ R q ell C₀ B : ℝ}
    (hG : 0 ≤ G) (hV : 0 ≤ V) (hs : 0 ≤ s) (hμ : 0 < μ) (hR : 0 < R)
    (hq : 0 < q) (hell : 1 ≤ ell) (hC₀ : 0 ≤ C₀)
    (hwarm : R ≤ Real.sqrt 2 * G / μ)
    (hB : B ≤ μ * R / localizationScale C₀) :
    let n := (localizationPhaseBudget G V s μ R q ell C₀ : ℝ)
    C₀ * R * ((G + Real.sqrt V) / Real.sqrt n + G * ell / n +
      s * (ell / n) ^ q + B) ≤ μ * R ^ 2 / 8 := by
  let n := (localizationPhaseBudget G V s μ R q ell C₀ : ℝ)
  let K := localizationScale C₀
  have hK : 0 < K := localizationScale_pos hC₀
  have hn : 0 < n := lt_of_lt_of_le zero_lt_one
    (hell.trans (localizationPhaseBudget_ge_confidence hG hV hs hμ hR
      (zero_le_one.trans hell) hC₀ hwarm))
  have hc := localizationPhaseBudget_components (q := q) hG hV hs hμ hR (zero_le_one.trans hell) hC₀
  have hfirst := root_term_of_budget hG hV (mul_pos hμ hR) hK hn hc.1
  have hsecond : G * ell / n ≤ μ * R / K := by
    apply (div_le_iff₀ hn).mpr
    have hh := (div_le_iff₀ (mul_pos hμ hR)).mp hc.2.1
    have hd := (le_div_iff₀ hK).mpr
      (show G * ell * K ≤ n * (μ * R) by nlinarith only [hh])
    convert hd using 1 <;> ring
  have hthird := power_term_of_budget hs (zero_le_one.trans hell) hn (div_pos (mul_pos hμ hR) hK) hq hc.2.2.1
  have hsum : (G + Real.sqrt V) / Real.sqrt n + G * ell / n + s * (ell / n) ^ q + B ≤
      4 * (μ * R / K) := by linarith only [hfirst, hsecond, hthird, hB]
  apply (mul_le_mul_of_nonneg_left hsum (mul_nonneg hC₀ hR.le)).trans
  have hC : 32 * C₀ ≤ K := by dsimp [K, localizationScale]; linarith
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 8)).mpr
  have he : C₀ * R * (4 * (μ * R / K)) * 8 = (32 * C₀) / K * (μ * R ^ 2) := by ring
  rw [he]
  have hratio : (32 * C₀) / K ≤ 1 := (div_le_one hK).mpr hC
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hratio (by positivity : 0 ≤ μ * R ^ 2)

end HeavyTail
