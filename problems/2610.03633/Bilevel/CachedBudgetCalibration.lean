import Bilevel.CachedAnchorCount
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Ring

/-! Explicit public caps, refresh counts, and confidence repetition budgets
from the revised cached upper algorithm. -/
noncomputable section
namespace Bilevel.CachedBudgetCalibration

def outerCount (Λ Δ ε : ℝ) : ℕ := max 1 (Nat.ceil (32*Λ*Δ/ε^2))

def energyCap (Λ Δ ε : ℝ) : ℝ := 16*Λ*Δ+outerCount Λ Δ ε * ε^2

def radiusCap (Λ Δ ε : ℝ) : ℝ := Real.sqrt (outerCount Λ Δ ε * energyCap Λ Δ ε)/Λ

theorem outerCount_pos (Λ Δ ε : ℝ) : 0 < outerCount Λ Δ ε :=
  lt_of_lt_of_le (by decide) (le_max_left _ _)

theorem outerCount_horizon {Λ Δ ε : ℝ} (hε : 0 < ε) :
    32*Λ*Δ ≤ outerCount Λ Δ ε * ε^2 := by
  have hc := Nat.le_ceil (32*Λ*Δ/ε^2)
  have hm : (Nat.ceil (32*Λ*Δ/ε^2) : ℝ) ≤ outerCount Λ Δ ε :=
    Nat.cast_le.mpr (le_max_right _ _)
  exact (div_le_iff₀ (sq_pos_of_pos hε)).mp (hc.trans hm)

theorem outerCount_upper {Λ Δ ε : ℝ} (hΛ : 0 < Λ) (hΔ : 0 ≤ Δ) (hε : 0 < ε) :
    (outerCount Λ Δ ε : ℝ) ≤ 1+32*Λ*Δ/ε^2 := by
  have hX : 0 ≤ 32*Λ*Δ/ε^2 := by positivity
  have hc := (Nat.ceil_lt_add_one hX).le
  unfold outerCount
  rw [Nat.cast_max, Nat.cast_one]
  exact max_le (by linarith) (by linarith)

theorem radiusCap_bound {Λ Δ ε : ℝ} (hΛ : 0 < Λ) (hΔ : 0 ≤ Δ) (hε : 0 < ε) :
    radiusCap Λ Δ ε ≤ ε/Λ+40*Δ/ε := by
  let X := Λ*Δ/ε^2
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hN := outerCount_upper hΛ hΔ hε
  have hN' : (outerCount Λ Δ ε : ℝ) ≤ 1+32*X := by dsimp [X]; convert hN using 1; ring
  have hE : energyCap Λ Δ ε ≤ ε^2*(1+48*X) := by
    have hxid : ε^2*X = Λ*Δ := by dsimp [X]; field_simp
    have hm := mul_le_mul_of_nonneg_left hN' (sq_nonneg ε)
    unfold energyCap
    nlinarith
  have he0 : 0 ≤ energyCap Λ Δ ε := by unfold energyCap; positivity
  have hm := mul_le_mul hN' hE he0 (by positivity : 0 ≤ 1+32*X)
  have hsq : (outerCount Λ Δ ε : ℝ)*energyCap Λ Δ ε ≤ (ε*(1+40*X))^2 := by
    have hp : 0 ≤ ε^2*X^2 := by positivity
    nlinarith
  have hs : Real.sqrt ((outerCount Λ Δ ε : ℝ)*energyCap Λ Δ ε) ≤ ε*(1+40*X) :=
    (Real.sqrt_le_left (by positivity)).mpr hsq
  unfold radiusCap
  have hd := div_le_div_of_nonneg_right hs hΛ.le
  have he : ε*(1+40*X)/Λ = ε/Λ+40*Δ/ε := by dsimp [X]; field_simp; ring
  rwa [he] at hd

/-- The displacement rule needs only O(1+La*Delta/epsilon²) upper refreshes. -/
theorem anchor_budget {Λ La Δ ε M : ℝ}
    (hΛ : 0 < Λ) (hLa : 0 < La) (hLaΛ : La ≤ Λ) (hΔ : 0 ≤ Δ) (hε : 0 < ε)
    (hM : M ≤ 1+radiusCap Λ Δ ε/(ε/(64*La))) :
    M ≤ 2560*(1+La*Δ/ε^2) := by
  have hr := radiusCap_bound hΛ hΔ hε
  have hb : radiusCap Λ Δ ε/(ε/(64*La)) ≤ (ε/Λ+40*Δ/ε)/(ε/(64*La)) :=
    div_le_div_of_nonneg_right hr (by positivity)
  have he : (ε/Λ+40*Δ/ε)/(ε/(64*La)) = 64*(La/Λ)+2560*La*Δ/ε^2 := by
    field_simp
    ring
  rw [he] at hb
  have hquot : La/Λ ≤ 1 := (div_le_one hΛ).mpr hLaΛ
  rw [show 2560*(1+La*Δ/ε^2) = 2560 + 2560*La*Δ/ε^2 by ring]
  linarith

def confidenceCount (N : ℕ) (δ : ℝ) : ℕ := max 1 (Nat.ceil (8*Real.log (10*N/δ)))

theorem confidenceCount_pos (N : ℕ) (δ : ℝ) : 0 < confidenceCount N δ :=
  lt_of_lt_of_le (by decide) (le_max_left _ _)

theorem confidence_failure_budget {N : ℕ} (hN : 0 < N) {δ : ℝ} (hδ : 0 < δ) :
    Real.exp (-(confidenceCount N δ : ℝ)/8) ≤ δ/(10*N) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hl := Nat.le_ceil (8*Real.log (10*N/δ))
  have hm : (Nat.ceil (8*Real.log (10*N/δ)) : ℝ) ≤ confidenceCount N δ :=
    Nat.cast_le.mpr (le_max_right _ _)
  have he : -(confidenceCount N δ : ℝ)/8 ≤ -Real.log (10*N/δ) := by linarith
  have hh := Real.exp_le_exp.mpr he
  rw [Real.exp_neg, Real.exp_log (by positivity : 0 < 10*(N : ℝ)/δ)] at hh
  simpa [inv_div] using hh

theorem six_operations_budget {N : ℕ} (hN : 0 < N) {δ : ℝ} (hδ : 0 < δ) :
    (6*N : ℝ)*Real.exp (-(confidenceCount N δ : ℝ)/8) ≤ δ := by
  have hh := mul_le_mul_of_nonneg_left (confidence_failure_budget hN hδ)
    (by positivity : 0 ≤ (6*N : ℝ))
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have he : (6*N : ℝ)*(δ/(10*N)) = 3*δ/5 := by field_simp; ring
  rw [he] at hh
  linarith

end Bilevel.CachedBudgetCalibration
