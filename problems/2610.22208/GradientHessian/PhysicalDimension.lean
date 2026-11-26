import GradientHessian.AllocationParameters
import GradientHessian.FirstHeightScales

/-! The displayed physical-coordinate count has the source logarithmic
depth bound. This counts one shared block per height, not one per node. -/

noncomputable section
namespace GradientHessian.PhysicalDimension
open AllocationParameters
open scoped BigOperators

theorem logInput_le_sqrt {M : ℕ} (hM : 1≤M) : logInput M ≤ 4*Real.sqrt M := by
  have hm : (1:ℝ)≤M := by exact_mod_cast hM
  have hl := Real.log_le_rpow_div (x := 2+(M:ℝ)) (by positivity) (by norm_num : (0:ℝ)<1/2)
  rw [← Real.sqrt_eq_rpow] at hl
  have hs : Real.sqrt (2+(M:ℝ)) ≤ 2*Real.sqrt M := by
    nlinarith [Real.sq_sqrt (by positivity : (0:ℝ)≤2+M),
      Real.sq_sqrt (Nat.cast_nonneg M), Real.sqrt_nonneg (M:ℝ), Real.sqrt_nonneg (2+(M:ℝ))]
  unfold logInput
  linarith

theorem logInput_sq_le {M : ℕ} (hM : 1≤M) : (logInput M)^2 ≤ 16*M := by
  have h := logInput_le_sqrt hM
  have h2 := mul_self_le_mul_self (logInput_pos M).le h
  nlinarith [Real.sq_sqrt (Nat.cast_nonneg M)]

theorem outer_register_log_bound (M : ℕ) :
    (FirstHeight.depth M+2:ℕ) ≤ (5/Real.log 2)*logInput M := by
  have hm : Nat.clog 2 M ≤ Nat.clog 2 (2+M) := Nat.clog_mono_right 2 (by omega)
  have hcast : ((FirstHeight.depth M+2:ℕ):ℝ) ≤ (cutoff M:ℝ)+1 := by
    exact_mod_cast (show FirstHeight.depth M+2 ≤ cutoff M+1 by
      unfold FirstHeight.depth cutoff
      omega)
  have hc := cutoff_log_bound M
  have hlog := (div_le_div_iff_of_pos_right log_two_pos).mpr (logInput_ge_log_two M)
  rw [div_self log_two_pos.ne'] at hlog
  have he4 : (4/Real.log 2)*logInput M=4*(logInput M/Real.log 2) := by ring
  have he5 : (5/Real.log 2)*logInput M=5*(logInput M/Real.log 2) := by ring
  rw [he4] at hc
  rw [he5]
  linarith

def count (Cp : ℝ) (D M L : ℕ) : ℕ :=
  D + M*(Inner.absoluteDepth+2)*lowDimension Cp M +
    8*(FirstHeight.depth M+2)*lowDimension Cp M +
    8*∑ q ∈ Finset.Icc 2 L, Allocation.levelDimension (lowDimension Cp M) (cutoff M) q

def coefficient (Cp Cnum : ℝ) : ℝ :=
  Cnum+212*lowCoefficient Cp+1152*lowCoefficient Cp/Real.log 2

theorem count_le_sqrt {Cp Cnum : ℝ} (hCp : 0≤Cp) (_hnum : 0≤Cnum)
    {D M : ℕ} (hM : 1≤M) (hD : (D:ℝ)≤Cnum*M*Real.sqrt M) (L : ℕ) :
    (count Cp D M L:ℝ) ≤ coefficient Cp Cnum * M * Real.sqrt M + 64*L := by
  have hp := lowDimension_le hCp M
  have hk := outer_register_log_bound M
  have hs := level_dimension_log_bound hCp M L
  have hl := logInput_le_sqrt hM
  have hl2 := logInput_sq_le hM
  have hcoef := (lowCoefficient_pos hCp).le
  have hms : (M:ℝ) ≤ M*Real.sqrt M := by
    have hr : (1:ℝ)≤Real.sqrt M := Real.one_le_sqrt.mpr (by exact_mod_cast hM)
    nlinarith [show (0:ℝ)≤M from Nat.cast_nonneg M]
  have hin : (M:ℝ)*53*(lowDimension Cp M:ℝ) ≤ 212*lowCoefficient Cp*M*Real.sqrt M := by
    have h1 := mul_le_mul_of_nonneg_left hp (show 0≤(M:ℝ)*53 by positivity)
    have h2 := mul_le_mul_of_nonneg_left hl (show 0≤53*lowCoefficient Cp*M by positivity)
    nlinarith
  have hout : (8:ℝ)*(FirstHeight.depth M+2:ℕ)*(lowDimension Cp M:ℝ) ≤
      (640*lowCoefficient Cp/Real.log 2)*M := by
    have h1 := mul_le_mul hk hp (Nat.cast_nonneg _)
      (mul_nonneg (div_nonneg (by norm_num : (0:ℝ)≤5) log_two_pos.le) (logInput_pos M).le)
    have h2 := mul_le_mul_of_nonneg_left hl2 (show 0≤40*lowCoefficient Cp/Real.log 2 by positivity)
    have he : (5/Real.log 2)*logInput M*(lowCoefficient Cp*logInput M) =
        (5*lowCoefficient Cp/Real.log 2)*(logInput M)^2 := by ring
    rw [he] at h1
    have he2 : 40*lowCoefficient Cp/Real.log 2 = 8*(5*lowCoefficient Cp/Real.log 2) := by ring
    rw [he2] at h2
    simp only [div_eq_mul_inv] at h1 h2 ⊢
    nlinarith
  have hhigh : (8:ℝ)*((∑ q ∈ Finset.Icc 2 L,
      Allocation.levelDimension (lowDimension Cp M) (cutoff M) q):ℝ) ≤
      (512*lowCoefficient Cp/Real.log 2)*M+64*L := by
    have h2 := mul_le_mul_of_nonneg_left hl2 (show 0≤32*lowCoefficient Cp/Real.log 2 by positivity)
    have he : 32*lowCoefficient Cp/Real.log 2 = 8*(4*lowCoefficient Cp/Real.log 2) := by ring
    rw [he] at h2
    simp only [div_eq_mul_inv] at hs h2 ⊢
    nlinarith
  have hmem := mul_le_mul_of_nonneg_left hms (show 0≤1152*lowCoefficient Cp/Real.log 2 by positivity)
  unfold count coefficient
  norm_num only [Inner.absoluteDepth, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sum]
  have he : 1152*lowCoefficient Cp/Real.log 2 =
      640*lowCoefficient Cp/Real.log 2+512*lowCoefficient Cp/Real.log 2 := by ring
  rw [he] at hmem
  push_cast at hout hhigh
  simp only [div_eq_mul_inv] at hout hhigh hmem ⊢
  nlinarith

theorem depth_le_log (L : ℕ) : (L:ℝ) ≤ Real.log (2+(8:ℝ)^L)/Real.log 8 := by
  have h8 : 0<Real.log 8 := Real.log_pos (by norm_num)
  have h := Real.log_le_log (by positivity : (0:ℝ)<8^L) (by linarith : (8:ℝ)^L≤2+8^L)
  rw [Real.log_pow] at h
  exact (le_div_iff₀ h8).mpr h

theorem mul_sqrt_eq_rpow {M : ℝ} (hM : 0<M) : M*Real.sqrt M = M^(3/2:ℝ) := by
  rw [show (3/2:ℝ)=1+1/2 by ring, Real.rpow_add hM, Real.rpow_one, ← Real.sqrt_eq_rpow]

def finalCoefficient (Cp Cnum : ℝ) : ℝ := max (coefficient Cp Cnum) (64/Real.log 8)

theorem finalCoefficient_pos (Cp Cnum : ℝ) : 0<finalCoefficient Cp Cnum :=
  (div_pos (by norm_num) (Real.log_pos (by norm_num))).trans_le (le_max_right _ _)

theorem source_dimension_bound {Cp Cnum : ℝ} (hCp : 0≤Cp) (hnum : 0≤Cnum)
    {D M : ℕ} (hM : 1≤M) (hD : (D:ℝ)≤Cnum*M*Real.sqrt M) (L : ℕ) :
    (count Cp D M L:ℝ) ≤ finalCoefficient Cp Cnum *
      ((M:ℝ)^(3/2:ℝ)+Real.log (2+(8:ℝ)^L)) := by
  have h := count_le_sqrt hCp hnum hM hD L
  have hmp : (0:ℝ)<M := by exact_mod_cast (show 0<M by omega)
  rw [mul_assoc, mul_sqrt_eq_rpow hmp] at h
  have hd := mul_le_mul_of_nonneg_left (depth_le_log L) (by norm_num : (0:ℝ)≤64)
  have hc1 := mul_le_mul_of_nonneg_right
    (show coefficient Cp Cnum≤finalCoefficient Cp Cnum from le_max_left _ _)
    (Real.rpow_nonneg hmp.le (3/2:ℝ))
  have hlog : 0≤Real.log (2+(8:ℝ)^L) := Real.log_nonneg (by have h := pow_nonneg (by norm_num : (0:ℝ)≤8) L; linarith)
  have hc2 := mul_le_mul_of_nonneg_right
    (show 64/Real.log 8≤finalCoefficient Cp Cnum from le_max_right _ _) hlog
  have he : 64*(Real.log (2+(8:ℝ)^L)/Real.log 8) = (64/Real.log 8)*Real.log (2+(8:ℝ)^L) := by ring
  rw [he] at hd
  linarith

def numericalCount (κ : ℕ) (KA : ℝ) (J M : ℕ) : ℕ := κ*⌈KA*(M:ℝ)⌉₊*J

theorem numerical_count_le (κ : ℕ) {KA : ℝ} (hKA : 0≤KA) {J M : ℕ}
    (hM : 1≤M) (hJM : J^2≤M) :
    (numericalCount κ KA J M:ℝ) ≤ ((κ:ℝ)*(KA+1))*M*Real.sqrt M := by
  have hm : (1:ℝ)≤M := by exact_mod_cast hM
  have hceil := (Nat.ceil_lt_add_one (mul_nonneg hKA (Nat.cast_nonneg M))).le
  have hr : (⌈KA*(M:ℝ)⌉₊:ℝ) ≤ (KA+1)*M := by nlinarith
  have hj : (J:ℝ)≤Real.sqrt M := (Real.le_sqrt (Nat.cast_nonneg J) (Nat.cast_nonneg M)).mpr (by exact_mod_cast hJM)
  have hp := mul_le_mul hr hj (Nat.cast_nonneg J) (by positivity : 0≤(KA+1)*M)
  have hk := mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg κ)
  unfold numericalCount
  push_cast
  nlinarith

theorem source_numeric_count (κ : ℕ) {KA : ℝ} (hKA : 0≤KA) (J : ℕ) :
    (numericalCount κ KA J (1+4096*J^2):ℝ) ≤
      ((κ:ℝ)*(KA+1))*(1+4096*(J:ℝ)^2)*Real.sqrt (1+4096*(J:ℝ)^2) := by
  have h := numerical_count_le κ hKA (M := 1+4096*J^2) (by omega)
    (show J^2≤1+4096*J^2 by omega)
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] using h

theorem source_construction_dimension {Cp KA : ℝ} (hCp : 0≤Cp) (hKA : 0≤KA) (κ J L : ℕ) :
    (count Cp (numericalCount κ KA J (1+4096*J^2)) (1+4096*J^2) L:ℝ) ≤
      finalCoefficient Cp ((κ:ℝ)*(KA+1)) *
        ((1+4096*(J:ℝ)^2)^(3/2:ℝ)+Real.log (2+(8:ℝ)^L)) := by
  have h := source_dimension_bound hCp
    (show 0≤(κ:ℝ)*(KA+1) by positivity)
    (M := 1+4096*J^2) (D := numericalCount κ KA J (1+4096*J^2)) (by omega)
    (numerical_count_le κ hKA (by omega) (by omega)) L
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] using h

end GradientHessian.PhysicalDimension
