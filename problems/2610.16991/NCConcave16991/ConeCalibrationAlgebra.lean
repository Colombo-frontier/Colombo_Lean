import NCConcave16991.TheoremStatements
import Mathlib.Algebra.Order.Floor.Semifield

/-! # Actual capped-radius and integer-stage calibration for the cone family -/

noncomputable section

namespace NCConcave16991.ConeCalibration

def quarterRoot (n : ℝ) : ℝ := Real.sqrt (Real.sqrt n)
def radius (n B C : ℝ) : ℝ := min (B / C) (quarterRoot n)
def clockRatio (n B C : ℝ) : ℝ := Real.sqrt n / radius n B C
def stageCount (A K q : ℝ) : ℕ := ⌊A / (200 * K * q)⌋₊
def stageIndex (A K q : ℝ) : ℕ := stageCount A K q - 1

theorem quarterRoot_sq {n : ℝ} (hn : 0 ≤ n) : quarterRoot n ^ 2 = Real.sqrt n :=
  Real.sq_sqrt (Real.sqrt_nonneg n)

theorem quarterRoot_rpow {n : ℝ} (hn : 0 ≤ n) : quarterRoot n = n ^ (1 / 4 : ℝ) := by
  rw [quarterRoot, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hn]
  norm_num

theorem half_mul_quarter {n : ℝ} (hn : 0 < n) : Real.sqrt n * quarterRoot n = n ^ (3 / 4 : ℝ) := by
  rw [quarterRoot_rpow hn.le, Real.sqrt_eq_rpow, ← Real.rpow_add hn]
  norm_num

theorem quarterRoot_ge_sixteen {n : ℝ} (hn : 65536 ≤ n) : 16 ≤ quarterRoot n := by
  have hn0 : 0 ≤ n := by linarith
  have hs : 256 ≤ Real.sqrt n := by nlinarith [Real.sq_sqrt hn0, Real.sqrt_nonneg n]
  have hq := quarterRoot_sq hn0
  have hq0 : 0 ≤ quarterRoot n := Real.sqrt_nonneg _
  nlinarith

theorem radius_bounds {n B C : ℝ} (hn : 65536 ≤ n) (hC : 1 ≤ C) (hB : C ≤ B) :
    1 ≤ radius n B C ∧ radius n B C ≤ B / C ∧ radius n B C ≤ quarterRoot n := by
  have hC0 : 0 < C := by linarith
  have hBC : 1 ≤ B / C := (le_div_iff₀ hC0).mpr (by simpa using hB)
  exact ⟨le_min hBC (by linarith [quarterRoot_ge_sixteen hn]), min_le_left _ _, min_le_right _ _⟩

theorem clockRatio_bounds {n B C : ℝ} (hn : 65536 ≤ n) (hC : 1 ≤ C) (hB : C ≤ B) :
    16 ≤ clockRatio n B C ∧ Real.sqrt n ≤ clockRatio n B C ^ 2 ∧
      Real.sqrt n = clockRatio n B C * radius n B C := by
  have hn0 : 0 ≤ n := by linarith
  have hr := radius_bounds hn hC hB
  have hr0 : 0 < radius n B C := by linarith
  have hroot0 : 0 ≤ quarterRoot n := Real.sqrt_nonneg _
  have hqge : quarterRoot n ≤ clockRatio n B C := by
    apply (le_div_iff₀ hr0).mpr
    have hh := mul_le_mul_of_nonneg_left hr.2.2 hroot0
    nlinarith [quarterRoot_sq hn0]
  refine ⟨(quarterRoot_ge_sixteen hn).trans hqge, ?_, ?_⟩
  · nlinarith [quarterRoot_sq hn0, quarterRoot_ge_sixteen hn]
  · exact (div_mul_cancel₀ (Real.sqrt n) hr0.ne').symm

theorem n_div_clockRatio {n B C : ℝ} (hn : 65536 ≤ n) (hC : 1 ≤ C) (hB : C ≤ B) :
    n / clockRatio n B C = Real.sqrt n * radius n B C := by
  have hn0 : 0 < n := by linarith
  have hr := (radius_bounds hn hC hB).1
  have hr0 : 0 < radius n B C := by linarith
  have hs0 := Real.sqrt_pos.mpr hn0
  unfold clockRatio
  apply (div_eq_iff (div_pos hs0 hr0).ne').mpr
  have he : (Real.sqrt n * radius n B C) * (Real.sqrt n / radius n B C) = (Real.sqrt n) ^ 2 := by
    field_simp
  rw [he, Real.sq_sqrt hn0.le]

theorem optimization_scale_bound {n B C : ℝ} (hn : 65536 ≤ n) (hC : 1 ≤ C) (hB : C ≤ B) :
    optimizationLower n B ≤ C * (n / clockRatio n B C) := by
  have hn0 : 0 < n := by linarith
  have hC0 : 0 < C := by linarith
  have hCq : quarterRoot n ≤ C * quarterRoot n := by
    have hh := mul_le_mul_of_nonneg_right hC (Real.sqrt_nonneg (Real.sqrt n))
    simpa only [one_mul, quarterRoot] using hh
  have he : C * radius n B C = min B (C * quarterRoot n) := by
    rw [radius, mul_min_of_nonneg _ _ hC0.le]
    congr 1
    field_simp
  have hm : min B (quarterRoot n) ≤ C * radius n B C := by
    rw [he]
    exact min_le_min le_rfl hCq
  have hh := mul_le_mul_of_nonneg_left hm (Real.sqrt_nonneg n)
  rw [mul_min_of_nonneg _ _ (Real.sqrt_nonneg n), half_mul_quarter hn0] at hh
  rw [n_div_clockRatio hn hC hB]
  have hB1 : 1 ≤ B := hC.trans hB
  rw [optimizationLower, clippedDiameter_of_one_le hB1, ← Real.sqrt_eq_rpow]
  nlinarith

theorem stageCount_bounds {A K q : ℝ} (hK : 0 < K) (hq : 1 ≤ q) (hA : 400 * K * q ≤ A) :
    2 ≤ stageCount A K q ∧
      A / (400 * K * q) ≤ (stageCount A K q : ℝ) ∧
      K * (1 + 91 * (stageCount A K q : ℝ) * q) ≤ A ∧
      stageIndex A K q + 1 = stageCount A K q := by
  have hq0 : 0 < q := by linarith
  have hden : 0 < 200 * K * q := by positivity
  have hA0 : 0 < A := (by positivity : 0 < 400 * K * q).trans_le hA
  have ha2 : 2 ≤ A / (200 * K * q) := (le_div_iff₀ hden).mpr (by nlinarith)
  have ha0 : 0 ≤ A / (200 * K * q) := by positivity
  have hT2 : 2 ≤ stageCount A K q := (Nat.le_floor_iff ha0).mpr ha2
  have hlo := Nat.lt_floor_add_one (A / (200 * K * q))
  have hup := Nat.floor_le ha0
  change A / (200 * K * q) < (stageCount A K q : ℝ) + 1 at hlo
  change (stageCount A K q : ℝ) ≤ A / (200 * K * q) at hup
  have hprod := (le_div_iff₀ hden).mp hup
  have hKq : 400 * K ≤ 400 * K * q := by nlinarith [mul_le_mul_of_nonneg_left hq (by positivity : 0 ≤ 400 * K)]
  refine ⟨hT2, ?_, ?_, ?_⟩
  · have he : A / (400 * K * q) = (A / (200 * K * q)) / 2 := by ring
    rw [he]
    nlinarith
  · nlinarith
  · exact Nat.sub_add_cancel (by omega : 1 ≤ stageCount A K q)

theorem calibrated_budget_bound {n B C A K : ℝ} (hn : 65536 ≤ n) (hC : 1 ≤ C) (hB : C ≤ B)
    (hK : 0 < K) (hA : 400 * K * clockRatio n B C ≤ A) :
    A * optimizationLower n B / (400 * 4096 * K * C) ≤
      n * (stageCount A K (clockRatio n B C) : ℝ) / 4096 := by
  have hq := (clockRatio_bounds hn hC hB).1
  have hq0 : 0 < clockRatio n B C := by linarith
  have hA0 : 0 ≤ A := by nlinarith [mul_pos (by positivity : 0 < 400 * K) hq0]
  have hC0 : 0 < C := by linarith
  have hf := optimization_scale_bound hn hC hB
  have hF : optimizationLower n B / C ≤ n / clockRatio n B C :=
    (div_le_iff₀ hC0).mpr (by simpa only [mul_comm] using hf)
  have hT := (stageCount_bounds hK (by linarith) hA).2.1
  calc
    A * optimizationLower n B / (400 * 4096 * K * C) =
        (A * (optimizationLower n B / C)) / (400 * 4096 * K) := by ring
    _ ≤ (A * (n / clockRatio n B C)) / (400 * 4096 * K) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hF hA0) (by positivity)
    _ = n * (A / (400 * K * clockRatio n B C)) / 4096 := by ring
    _ ≤ n * (stageCount A K (clockRatio n B C) : ℝ) / 4096 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hT (by linarith : 0 ≤ n)) (by norm_num)

theorem small_gap_covered {n B C A K : ℝ} (hn : 65536 ≤ n) (hC : 1 ≤ C) (hB : C ≤ B)
    (hK : 0 < K) (hA0 : 0 ≤ A) (hA : A < 400 * K * clockRatio n B C) :
    A * optimizationLower n B ≤ (400 * K * C) * n := by
  have hf := optimization_scale_bound hn hC hB
  have hq0 : 0 < clockRatio n B C := by linarith [(clockRatio_bounds hn hC hB).1]
  have h1 := mul_le_mul_of_nonneg_left hf hA0
  have hn0 : 0 ≤ n := by linarith
  have hfactor : 0 ≤ C * (n / clockRatio n B C) := by positivity
  have h2 := mul_le_mul_of_nonneg_right hA.le hfactor
  have he : (400 * K * clockRatio n B C) * (C * (n / clockRatio n B C)) = (400 * K * C) * n := by
    field_simp
  exact h1.trans (he ▸ h2)

theorem optimization_small_diameter {n B C : ℝ} (hn : 0 ≤ n) (hC : 1 ≤ C) (hB : B ≤ C) :
    optimizationLower n B ≤ C * Real.sqrt n := by
  have hb : clippedDiameter B ≤ C := max_le hC hB
  have hh := mul_le_mul_of_nonneg_left hb (Real.sqrt_nonneg n)
  rw [optimizationLower, ← Real.sqrt_eq_rpow]
  exact (min_le_left _ _).trans (by nlinarith)

theorem optimization_small_n {n B : ℝ} (hn : 1 ≤ n) (hnhi : n ≤ 65536) :
    optimizationLower n B ≤ 16 * Real.sqrt n := by
  have hn0 : 0 < n := by linarith
  have hs : Real.sqrt n ≤ 256 := by nlinarith [Real.sq_sqrt hn0.le, Real.sqrt_nonneg n]
  have hq : quarterRoot n ≤ 16 := by
    nlinarith [quarterRoot_sq hn0.le, Real.sqrt_nonneg (Real.sqrt n)]
  have hh := mul_le_mul_of_nonneg_left hq (Real.sqrt_nonneg n)
  rw [half_mul_quarter hn0] at hh
  exact (min_le_right _ _).trans (by nlinarith)

end NCConcave16991.ConeCalibration
