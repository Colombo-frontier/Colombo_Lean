import MatchingBounds1005.Model
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-! Concrete integer caps for the accelerated upper-bound algorithm. -/
noncomputable section

namespace MatchingBounds1005.CUPG

def phaseCap (r ε : ℝ) : ℕ := ⌈(2 / r) * Real.log (800 / ε ^ 2)⌉₊
def epochCap (r : ℝ) : ℕ := ⌈256 / r ^ 4⌉₊ + 1

theorem log_budget {ε : ℝ} (hε : 0 < ε) (hεone : ε ≤ 1) :
    1 / 2 ≤ Real.log (2 / ε) ∧ Real.log (800 / ε ^ 2) ≤ 12 * Real.log (2 / ε) := by
  have htwo : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh ⊢
    linarith
  have heps : Real.log ε ≤ 0 := Real.log_nonpos hε.le hεone
  have h800 : Real.log 800 ≤ 10 * Real.log 2 := by
    have hh : Real.log (800 : ℝ) ≤ Real.log ((2 : ℝ) ^ 10) :=
      Real.log_le_log (by norm_num) (by norm_num)
    simpa only [Real.log_pow, Nat.cast_ofNat] using hh
  rw [Real.log_div (by norm_num) hε.ne',
    Real.log_div (by norm_num) (pow_ne_zero 2 hε.ne'), Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  constructor <;> linarith

theorem phaseCap_monitor {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) :
    8 * Real.exp (-(r / 2) * phaseCap r ε) ≤ (ε / 10) ^ 2 := by
  have hc := Nat.le_ceil ((2 / r) * Real.log (800 / ε ^ 2))
  have hm := mul_le_mul_of_nonneg_left hc (show 0 ≤ r / 2 by positivity)
  have hid : (r / 2) * ((2 / r) * Real.log (800 / ε ^ 2)) = Real.log (800 / ε ^ 2) := by
    field_simp
    ring
  rw [hid] at hm
  have he := Real.exp_le_exp.mpr (show -(r / 2) * (phaseCap r ε : ℝ) ≤
      -Real.log (800 / ε ^ 2) by change -(r / 2) * (⌈_⌉₊ : ℝ) ≤ _; linarith)
  rw [Real.exp_neg, Real.exp_log (by positivity : 0 < 800 / ε ^ 2)] at he
  have hh := mul_le_mul_of_nonneg_left he (by norm_num : (0 : ℝ) ≤ 8)
  convert hh using 1 <;> field_simp <;> ring

theorem phaseCap_bound {r ε : ℝ} (hr : 0 < r) (hrone : r ≤ 1)
    (hε : 0 < ε) (hεone : ε ≤ 1) :
    (phaseCap r ε : ℝ) ≤ (26 / r) * Real.log (2 / ε) := by
  obtain ⟨hlog, hbudget⟩ := log_budget hε hεone
  have hpos : 0 ≤ Real.log (800 / ε ^ 2) := by
    apply Real.log_nonneg
    apply (le_div_iff₀ (sq_pos_of_pos hε)).mpr
    nlinarith
  have hc := (Nat.ceil_lt_add_one (mul_nonneg (by positivity : 0 ≤ 2 / r) hpos)).le
  have hm := mul_le_mul_of_nonneg_left hbudget (show 0 ≤ 2 / r by positivity)
  have hlow : 1 ≤ (2 / r) * Real.log (2 / ε) := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hr).2
    linarith
  change (⌈(2 / r) * Real.log (800 / ε ^ 2)⌉₊ : ℝ) ≤ _
  calc
    _ ≤ (2 / r) * Real.log (800 / ε ^ 2) + 1 := hc
    _ ≤ (2 / r) * (12 * Real.log (2 / ε)) + (2 / r) * Real.log (2 / ε) := add_le_add hm hlow
    _ = (26 / r) * Real.log (2 / ε) := by ring

theorem epochCap_decrease {r : ℝ} (hr : 0 < r) :
    1 < (epochCap r : ℝ) * (r ^ 4 / 256) := by
  have hc := Nat.le_ceil (256 / r ^ 4)
  have hm := mul_le_mul_of_nonneg_right hc (show 0 ≤ r ^ 4 / 256 by positivity)
  have he : (256 / r ^ 4) * (r ^ 4 / 256) = 1 := by field_simp
  rw [he] at hm
  simp only [epochCap, Nat.cast_add, Nat.cast_one]
  nlinarith [show 0 < r ^ 4 / 256 by positivity]

theorem epochCap_bound {r : ℝ} (hr : 0 < r) (hrone : r ≤ 1) :
    (epochCap r : ℝ) ≤ 258 / r ^ 4 := by
  have hc := (Nat.ceil_lt_add_one (show 0 ≤ 256 / r ^ 4 by positivity)).le
  have hr4 : r ^ 4 ≤ 1 := pow_le_one₀ hr.le hrone
  have ht : 2 ≤ 2 / r ^ 4 := (le_div_iff₀ (pow_pos hr 4)).2 (by nlinarith)
  simp only [epochCap, Nat.cast_add, Nat.cast_one]
  calc
    _ ≤ 256 / r ^ 4 + 2 := by linarith
    _ ≤ 256 / r ^ 4 + 2 / r ^ 4 := by linarith
    _ = 258 / r ^ 4 := by ring

theorem totalCap_bound {r ε : ℝ} (hr : 0 < r) (hrone : r ≤ 1)
    (hε : 0 < ε) (hεone : ε ≤ 1) :
    ((epochCap r * (9 * phaseCap r ε + 3) : ℕ) : ℝ) ≤
      (61920 / r ^ 5) * Real.log (2 / ε) := by
  have hN := phaseCap_bound hr hrone hε hεone
  have hK := epochCap_bound hr hrone
  have hlog := (log_budget hε hεone).1
  have hlow : 3 ≤ (6 / r) * Real.log (2 / ε) := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hr).2
    linarith
  have hphase : 9 * (phaseCap r ε : ℝ) + 3 ≤ (240 / r) * Real.log (2 / ε) := by
    calc
      _ ≤ 9 * ((26 / r) * Real.log (2 / ε)) + (6 / r) * Real.log (2 / ε) := by linarith
      _ = _ := by ring
  have hm := mul_le_mul hK hphase (by positivity)
    (show 0 ≤ 258 / r ^ 4 by positivity)
  push_cast
  convert hm using 1 <;> field_simp <;> ring

end MatchingBounds1005.CUPG
