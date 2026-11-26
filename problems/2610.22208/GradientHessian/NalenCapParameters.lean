import GradientHessian.NalenConvergence
import Mathlib.Algebra.Order.Floor.Ring

/-! Integer choices for a prescribed rich-query cap. Cubing an integer
averaging length makes both the snapshot and averaging counts exact. -/

noncomputable section
namespace GradientHessian.Nalen

def capAveraging (T : ℝ) (h : ℕ) : ℕ := ⌈16*Real.sqrt (T/(h : ℝ))⌉₊
def capRefresh (T : ℝ) (h : ℕ) : ℕ := (capAveraging T h)^3
def capHorizon (T : ℝ) (h : ℕ) : ℕ := h*capRefresh T h
def capBlocks (T : ℝ) (h : ℕ) : ℕ := h*(capAveraging T h)^2

theorem cap_block_horizon (T : ℝ) (h : ℕ) :
    capBlocks T h*capAveraging T h=capHorizon T h := by
  unfold capBlocks capHorizon capRefresh
  ring

theorem cap_parameters {T : ℝ} {h : ℕ} (hT : 1 ≤ T) (hh : 1 ≤ h) (hhT : (h : ℝ) ≤ T) :
    1 ≤ capAveraging T h ∧ 1 ≤ capRefresh T h ∧ 1 ≤ capBlocks T h ∧
      256*T ≤ (capBlocks T h : ℝ) ∧
      (capHorizon T h : ℝ) ≤ 4913*T*Real.sqrt (T/(h : ℝ)) ∧
      (3*capHorizon T h+1 : ℕ) ≤ (14740*T*Real.sqrt (T/(h : ℝ)) : ℝ) := by
  have hhR : (0 : ℝ) < h := by exact_mod_cast (show 0 < h by omega)
  have hTpos : 0 < T := by linarith
  let r := Real.sqrt (T/(h : ℝ))
  have hr : 1 ≤ r := by
    have hratio : (1 : ℝ) ≤ T/(h : ℝ) := (le_div_iff₀ hhR).2 (by simpa using hhT)
    simpa [r] using Real.sqrt_le_sqrt hratio
  have hrpos : 0 < r := by linarith
  have hsq : r^2=T/(h : ℝ) := Real.sq_sqrt (div_nonneg hTpos.le hhR.le)
  have hscale : (h : ℝ)*r^2=T := by rw [hsq]; field_simp
  have hq : 1 ≤ capAveraging T h := Nat.one_le_ceil_iff.mpr (by change 0 < 16*r; positivity)
  have hm : 1 ≤ capRefresh T h := by unfold capRefresh; exact one_le_pow₀ hq
  have hK : 1 ≤ capBlocks T h := by unfold capBlocks; exact one_le_mul_of_one_le_of_one_le hh (one_le_pow₀ hq)
  have hlo : 16*r ≤ (capAveraging T h : ℝ) := Nat.le_ceil _
  have hhi : (capAveraging T h : ℝ) ≤ 17*r := by
    have hc := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 16*r by positivity)
    change (capAveraging T h : ℝ) < 16*r+1 at hc
    linarith
  have hq2 := (sq_le_sq₀ (show (0 : ℝ) ≤ 16*r by positivity) (Nat.cast_nonneg (capAveraging T h))).2 hlo
  have hq2' := mul_le_mul_of_nonneg_left hq2 hhR.le
  have hKb : 256*T ≤ (capBlocks T h : ℝ) := by
    unfold capBlocks
    push_cast
    nlinarith only [hq2',hscale]
  have hq3 := pow_le_pow_left₀ (Nat.cast_nonneg (capAveraging T h)) hhi 3
  have hq3' := mul_le_mul_of_nonneg_left hq3 hhR.le
  have hscale3 : (h : ℝ)*r^3=T*r := by
    calc
      (h : ℝ)*r^3=((h : ℝ)*r^2)*r := by ring
      _ = T*r := by rw [hscale]
  have hNb : (capHorizon T h : ℝ) ≤ 4913*T*r := by
    unfold capHorizon capRefresh
    push_cast
    calc
      (h : ℝ)*(capAveraging T h : ℝ)^3 ≤ (h : ℝ)*(17*r)^3 := hq3'
      _ = 4913*((h : ℝ)*r^3) := by ring
      _ = 4913*T*r := by rw [hscale3]; ring
  have hTr : 1 ≤ T*r := one_le_mul_of_one_le_of_one_le hT hr
  have hGb : ((3*capHorizon T h+1 : ℕ) : ℝ) ≤ 14740*T*r := by
    push_cast
    nlinarith only [hNb,hTr]
  exact ⟨hq,hm,hK,hKb,hNb,hGb⟩

theorem cap_horizon_div_refresh {T : ℝ} {h : ℕ} (hm : 1 ≤ capRefresh T h) :
    capHorizon T h/capRefresh T h=h := by
  unfold capHorizon
  exact Nat.mul_div_left _ (by omega)

theorem cap_budget_scale {T : ℝ} (hT : 0 < T) (h : ℕ) :
    T*Real.sqrt (T/(h : ℝ))=T^((3 : ℝ)/2)/Real.sqrt (h : ℝ) := by
  rw [Real.sqrt_div hT.le,← mul_div_assoc]
  congr 1
  calc
    T*Real.sqrt T=T^(1 : ℝ)*T^((1 : ℝ)/2) := by rw [Real.rpow_one,Real.sqrt_eq_rpow]
    _ = T^((1 : ℝ)+1/2) := (Real.rpow_add hT _ _).symm
    _ = _ := by congr 1; norm_num

theorem cap_source_query_bound {T : ℝ} {h : ℕ} (hT : 1 ≤ T) (hh : 1 ≤ h) (hhT : (h : ℝ) ≤ T) :
    ((3*capHorizon T h+1 : ℕ) : ℝ) ≤ 14740*T^((3 : ℝ)/2)/Real.sqrt (h : ℝ) := by
  have hc := (cap_parameters hT hh hhT).2.2.2.2.2
  have he : 14740*T*Real.sqrt (T/(h : ℝ))=14740*T^((3 : ℝ)/2)/Real.sqrt (h : ℝ) := by
    rw [mul_assoc,cap_budget_scale (by linarith : 0 < T) h,← mul_div_assoc]
  rwa [he] at hc

end GradientHessian.Nalen
