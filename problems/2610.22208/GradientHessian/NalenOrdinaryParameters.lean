import GradientHessian.NalenTuning
import Mathlib.Algebra.Order.Floor.Ring

/-! Integer choices and ordinary-query counts for dimension d. The
snapshot period is exactly d, as in the manuscript. -/

noncomputable section
namespace GradientHessian.Nalen

def ordinaryAveraging (d : ℕ) : ℕ := ⌈(d : ℝ)^((1 : ℝ)/3)⌉₊
def ordinaryBlocks (T : ℝ) : ℕ := ⌈256*T⌉₊
def ordinaryHorizon (T : ℝ) (d : ℕ) : ℕ := ordinaryBlocks T*ordinaryAveraging d
def ordinaryQueryCap (T : ℝ) (d : ℕ) : ℕ :=
  3*ordinaryHorizon T d+1+2*d*((ordinaryHorizon T d+d-1)/d)

theorem ordinary_parameters {T : ℝ} {d : ℕ} (hT : 1 ≤ T) (hd : 1 ≤ d) :
    1 ≤ ordinaryAveraging d ∧ 1 ≤ ordinaryBlocks T ∧ d ≤ (ordinaryAveraging d)^3 ∧
      256*T ≤ (ordinaryBlocks T : ℝ) ∧
      (ordinaryHorizon T d : ℝ) ≤ 514*T*(d : ℝ)^((1 : ℝ)/3) ∧
      (ordinaryQueryCap T d : ℝ) ≤ 4096*((d : ℝ)+T*(d : ℝ)^((1 : ℝ)/3)) := by
  have hTpos : 0 < T := by linarith
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  let r := (d : ℝ)^((1 : ℝ)/3)
  have hr : 1 ≤ r := Real.one_le_rpow hdR (by norm_num)
  have hrpos : 0 < r := by linarith
  have hr3 : r^3=(d : ℝ) := by
    dsimp [r]
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg d)]
    norm_num
  have hq : 1 ≤ ordinaryAveraging d := Nat.one_le_ceil_iff.mpr hrpos
  have hqlo : r ≤ (ordinaryAveraging d : ℝ) := Nat.le_ceil _
  have hqhi : (ordinaryAveraging d : ℝ) ≤ 2*r := by
    have h := Nat.ceil_lt_add_one hrpos.le
    change (ordinaryAveraging d : ℝ) < r+1 at h
    linarith
  have hcube := pow_le_pow_left₀ hrpos.le hqlo 3
  rw [hr3] at hcube
  have hmq : d ≤ (ordinaryAveraging d)^3 := by exact_mod_cast hcube
  have hK : 1 ≤ ordinaryBlocks T := Nat.one_le_ceil_iff.mpr (by change 0 < 256*T; positivity)
  have hKlo : 256*T ≤ (ordinaryBlocks T : ℝ) := Nat.le_ceil _
  have hKhi : (ordinaryBlocks T : ℝ) ≤ 257*T := by
    have h := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 256*T by positivity)
    change (ordinaryBlocks T : ℝ) < 256*T+1 at h
    linarith
  have hN : (ordinaryHorizon T d : ℝ) ≤ 514*T*r := by
    unfold ordinaryHorizon
    push_cast
    calc
      (ordinaryBlocks T : ℝ)*(ordinaryAveraging d : ℝ) ≤ (257*T)*(2*r) :=
        mul_le_mul hKhi hqhi (Nat.cast_nonneg _) (by positivity)
      _ = _ := by ring
  let c := (ordinaryHorizon T d+d-1)/d
  have hcount : d*c ≤ ordinaryHorizon T d+d := by
    have h := Nat.div_mul_le_self (ordinaryHorizon T d+d-1) d
    dsimp [c]
    nlinarith [Nat.sub_le (ordinaryHorizon T d+d) 1]
  have hcountR : (d : ℝ)*(c : ℝ) ≤ (ordinaryHorizon T d : ℝ)+(d : ℝ) := by exact_mod_cast hcount
  have hG : (ordinaryQueryCap T d : ℝ) ≤ 4096*((d : ℝ)+T*r) := by
    change ((3*ordinaryHorizon T d+1+2*d*c : ℕ) : ℝ) ≤ _
    push_cast
    nlinarith [mul_nonneg hTpos.le hrpos.le]
  exact ⟨hq,hK,hmq,hKlo,hN,hG⟩

end GradientHessian.Nalen
