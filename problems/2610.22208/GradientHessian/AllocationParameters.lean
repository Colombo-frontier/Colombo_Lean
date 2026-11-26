import GradientHessian.Allocation
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! The literal logarithmic reliability allocation. The cutoff is the
natural ceiling of log base two; all constants stay independent of depth. -/

noncomputable section
namespace GradientHessian.AllocationParameters
open scoped BigOperators

def logInput (M : ℕ) : ℝ := Real.log (2+(M:ℝ))
def lowDimension (Cp : ℝ) (M : ℕ) : ℕ := max 8 ⌈Cp*logInput M⌉₊
def cutoff (M : ℕ) : ℕ := 2+Nat.clog 2 (2+M)
def lowCoefficient (Cp : ℝ) : ℝ := Cp+9/Real.log 2

theorem log_two_pos : 0<Real.log 2 := Real.log_pos (by norm_num)

theorem logInput_ge_log_two (M : ℕ) : Real.log 2 ≤ logInput M := by
  apply Real.log_le_log (by norm_num)
  change (2:ℝ) ≤ 2+M
  linarith [show (0:ℝ)≤M from Nat.cast_nonneg M]

theorem logInput_pos (M : ℕ) : 0<logInput M := log_two_pos.trans_le (logInput_ge_log_two M)

theorem lowDimension_ge_eight (Cp : ℝ) (M : ℕ) : 8≤lowDimension Cp M := le_max_left _ _

theorem lowDimension_ge_log (Cp : ℝ) (M : ℕ) : Cp*logInput M ≤ (lowDimension Cp M:ℝ) :=
  (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right 8 ⌈Cp*logInput M⌉₊))

theorem lowCoefficient_pos {Cp : ℝ} (hCp : 0≤Cp) : 0<lowCoefficient Cp := by
  have h := div_pos (by norm_num : (0:ℝ)<9) log_two_pos
  unfold lowCoefficient
  linarith

theorem lowDimension_le {Cp : ℝ} (hCp : 0≤Cp) (M : ℕ) :
    (lowDimension Cp M:ℝ) ≤ lowCoefficient Cp*logInput M := by
  have hc := (Nat.ceil_lt_add_one (mul_nonneg hCp (logInput_pos M).le)).le
  have hd : lowDimension Cp M ≤ 8+⌈Cp*logInput M⌉₊ := max_le (by omega) (by omega)
  have hd' : (lowDimension Cp M:ℝ) ≤ 8+(⌈Cp*logInput M⌉₊:ℝ) := by exact_mod_cast hd
  have hlog := (div_le_div_iff_of_pos_right log_two_pos).mpr (logInput_ge_log_two M)
  rw [div_self log_two_pos.ne'] at hlog
  unfold lowCoefficient
  have he : (Cp+9/Real.log 2)*logInput M = Cp*logInput M+9*(logInput M/Real.log 2) := by ring
  rw [he]
  linarith

theorem cutoff_eq_source (M : ℕ) : cutoff M = 2+⌈Real.logb 2 (2+(M:ℝ))⌉₊ := by
  unfold cutoff
  rw [← Real.natCeil_logb_natCast 2 (2+M)]
  push_cast
  rfl

theorem cutoff_ge_two (M : ℕ) : 2≤cutoff M := by unfold cutoff; omega

theorem cutoff_upper (M : ℕ) : (cutoff M:ℝ) ≤ 3+logInput M/Real.log 2 := by
  rw [cutoff_eq_source]
  push_cast
  have hlog : 0≤Real.logb 2 (2+(M:ℝ)) := div_nonneg (logInput_pos M).le log_two_pos.le
  have hc := (Nat.ceil_lt_add_one hlog).le
  simp only [Real.logb] at hc
  change (2:ℝ)+(⌈Real.log (2+(M:ℝ))/Real.log 2⌉₊:ℝ) ≤ _
  unfold logInput
  linarith

theorem cutoff_log_bound (M : ℕ) : (cutoff M:ℝ) ≤ (4/Real.log 2)*logInput M := by
  have hc := cutoff_upper M
  have hlog := (div_le_div_iff_of_pos_right log_two_pos).mpr (logInput_ge_log_two M)
  rw [div_self log_two_pos.ne'] at hlog
  have he : (4/Real.log 2)*logInput M = 4*(logInput M/Real.log 2) := by ring
  rw [he]
  linarith

theorem cutoff_power_lower (M : ℕ) : (2+(M:ℝ)) ≤ 2^(cutoff M-2) := by
  have h := Nat.le_pow_clog (by norm_num : 1<2) (2+M)
  simpa only [cutoff, Nat.add_sub_cancel_left, Nat.cast_add, Nat.cast_ofNat, Nat.cast_pow] using
    (show ((2+M:ℕ):ℝ) ≤ (2^Nat.clog 2 (2+M):ℕ) by exact_mod_cast h)

theorem cutoff_tail_decay (M : ℕ) : (1/16:ℝ)^(cutoff M-2) ≤ 1/(2+(M:ℝ))^4 := by
  have hn := cutoff_power_lower M
  have hp := pow_le_pow_left₀ (by positivity : (0:ℝ)≤2+M) hn 4
  have hi := div_le_div_of_nonneg_left (by norm_num : (0:ℝ)≤1)
    (by positivity : (0:ℝ)<(2+M)^4) hp
  have he : (1/16:ℝ)^(cutoff M-2) = 1/((2:ℝ)^(cutoff M-2))^4 := by
    rw [← pow_mul, Nat.mul_comm _ 4, pow_mul]
    simp only [div_pow, one_pow]
    norm_num
  rw [he]
  exact hi

theorem fixed_tail_bound {K : ℝ} (hK : 0<K) (M count : ℕ) :
    (∑ j ∈ Finset.range count, Reliability.fixedDimensionCost K (cutoff M-2+j)) ≤
      256*(6/K)^7/(2+(M:ℝ))^4 := by
  have h := Reliability.fixed_dimension_tail K hK (cutoff M-2) count
  have ht := mul_le_mul_of_nonneg_left (cutoff_tail_decay M)
    (show 0≤256*(6/K)^7 by positivity)
  exact h.trans (by simpa only [mul_one_div] using ht)

theorem level_dimension_log_bound {Cp : ℝ} (hCp : 0≤Cp) (M L : ℕ) :
    ((∑ q ∈ Finset.Icc 2 L, Allocation.levelDimension (lowDimension Cp M) (cutoff M) q):ℝ) ≤
      (4*lowCoefficient Cp/Real.log 2)*(logInput M)^2 + 8*L := by
  have h := Allocation.level_dimension_sum_bound (lowDimension Cp M) (cutoff M) L (cutoff_ge_two M)
  have hr : ((∑ q ∈ Finset.Icc 2 L,
      Allocation.levelDimension (lowDimension Cp M) (cutoff M) q):ℝ) ≤
      (lowDimension Cp M:ℝ)*(cutoff M-2:ℕ)+8*L := by exact_mod_cast h
  have hc : ((cutoff M-2:ℕ):ℝ) ≤ (4/Real.log 2)*logInput M :=
    (show ((cutoff M-2:ℕ):ℝ) ≤ (cutoff M:ℝ) by exact_mod_cast (Nat.sub_le (cutoff M) 2)).trans
      (cutoff_log_bound M)
  have hp := mul_le_mul (lowDimension_le hCp M) hc (Nat.cast_nonneg _)
    (mul_nonneg (lowCoefficient_pos hCp).le (logInput_pos M).le)
  have he : lowCoefficient Cp*logInput M*((4/Real.log 2)*logInput M) =
      (4*lowCoefficient Cp/Real.log 2)*(logInput M)^2 := by ring
  rw [he] at hp
  linarith

end GradientHessian.AllocationParameters
