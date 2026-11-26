import GradientHessian.AllocationTails
import GradientHessian.FirstHeightScales
import Mathlib.Data.Complex.ExponentialBounds

/-! Explicit dimension-independent choices for the five repair-cost
contributions. These are arithmetic bounds; stopped adaptive test lists
and their per-action probability bounds remain separate inputs. -/

noncomputable section
namespace GradientHessian.RepairAllocation
open Allocation AllocationParameters AllocationTails
open scoped BigOperators

def lowAllocation : ℝ := 18432*20
def markAllocation : ℝ := 75497472*40

theorem polynomial_uniform {M : ℕ} (hM : 1≤M) (a q : ℕ) (ha : a≤q) :
    (M:ℝ)^a/(2+(M:ℝ))^q ≤ 1/(3:ℝ)^(q-a) := by
  refine (polynomial_weight_bound M a q ha).trans ?_
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  exact pow_le_pow_left₀ (by norm_num) (by exact_mod_cast (show 3≤2+M by omega)) _

theorem low_radius_decay {K Cp : ℝ} (hK : 384≤K) (hCp : lowAllocation≤Cp) (M : ℕ) :
    (6/K)^(lowDimension Cp M-1) ≤ 3/(2+(M:ℝ))^20 := by
  have hKp : 0<K := by linarith
  have hexp : Real.exp 1≤3 := Real.exp_one_lt_d9.le.trans (by norm_num)
  have hbase : 6/K≤Real.exp (-1) := by
    rw [Real.exp_neg,← one_div]
    apply (div_le_div_iff₀ hKp (Real.exp_pos 1)).mpr
    nlinarith
  have hp := pow_le_pow_left₀ (div_nonneg (by norm_num) hKp.le) hbase (lowDimension Cp M-1)
  have hn : 1≤lowDimension Cp M := (by norm_num : 1≤8).trans (lowDimension_ge_eight Cp M)
  have he : (Real.exp (-1))^(lowDimension Cp M-1) =
      Real.exp 1*Real.exp (-(lowDimension Cp M:ℝ)) := by
    rw [← Real.exp_nat_mul,← Real.exp_add,Nat.cast_sub hn]
    push_cast
    congr 1
    ring
  rw [he] at hp
  have hm := memory_allocation_decay M 20 (by simpa [lowAllocation] using hCp)
  have hmono : Real.exp (-(lowDimension Cp M:ℝ)) ≤
      Real.exp (-(lowDimension Cp M:ℝ)/18432) := by
    apply Real.exp_le_exp.mpr
    have h := Nat.cast_nonneg (lowDimension Cp M) (α := ℝ)
    linarith
  calc
    _ ≤ Real.exp 1*Real.exp (-(lowDimension Cp M:ℝ)) := hp
    _ ≤ 3*Real.exp (-(lowDimension Cp M:ℝ)/18432) :=
      mul_le_mul hexp hmono (Real.exp_pos _).le (by norm_num)
    _ ≤ _ := by simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hm (by norm_num : (0:ℝ)≤3)

theorem mark_allocation_decay {M r : ℕ} (hM : 1≤M)
    (hr : markAllocation*(M:ℝ)≤r) :
    Real.exp (-(r:ℝ)/75497472) ≤ 1/(2+(M:ℝ))^20 := by
  rw [← exp_neg_log_power M 20]
  apply Real.exp_le_exp.mpr
  have hlog := Real.log_le_sub_one_of_pos (show (0:ℝ)<2+M by positivity)
  have hM' : (1:ℝ)≤M := by exact_mod_cast hM
  unfold logInput markAllocation at *
  nlinarith

theorem outer_registers_le {M : ℕ} (hM : 1≤M) :
    ((FirstHeight.depth M+2:ℕ):ℝ) ≤ 8*M := by
  have hk := FirstHeight.register_count_le_radius (FirstHeight.depth M)
  have hr := (FirstHeight.outerRadius_range hM).2
  change Inner.lastRadius (FirstHeight.depth M)<8*(M:ℝ) at hr
  exact_mod_cast hk.trans hr.le

theorem low_contribution {K Cp : ℝ} (hK : 384≤K) (hCp : lowAllocation≤Cp)
    {M ell : ℕ} (hM : 1≤M) (hell : ell≤M) :
    (480:ℝ)*M*ell*(6/K)^(lowDimension Cp M-1) ≤ 1/2048 := by
  have he := low_radius_decay hK hCp M
  have hell' : (ell:ℝ)≤M := by exact_mod_cast hell
  have hprod : (M:ℝ)*ell≤(M:ℝ)^2 := by nlinarith [Nat.cast_nonneg M (α := ℝ)]
  have h := mul_le_mul hprod he (by positivity : (0:ℝ)≤(6/K)^(lowDimension Cp M-1)) (by positivity)
  have hw := polynomial_uniform hM 2 20 (by norm_num)
  calc
    _ ≤ 1440*((M:ℝ)^2/(2+(M:ℝ))^20) := by
      convert mul_le_mul_of_nonneg_left h (by norm_num : (0:ℝ)≤480) using 1 <;> ring
    _ ≤ 1440/(3:ℝ)^18 := by nlinarith [hw]
    _ ≤ _ := by norm_num

theorem high_contribution {K : ℝ} (hK : 384≤K) {M ell : ℕ}
    (hM : 1≤M) (hell : ell≤M) :
    (480:ℝ)*M*ell*(6/K)^7/(2+(M:ℝ))^4 ≤ 1/2048 := by
  have hKp : 0<K := by linarith
  have hb : 0≤6/K := by positivity
  have hk : 6/K≤(1/64:ℝ) := (div_le_iff₀ hKp).mpr (by linarith)
  have hp := pow_le_pow_left₀ hb hk 7
  have hell' : (ell:ℝ)≤M := by exact_mod_cast hell
  have hprod : (M:ℝ)*ell≤(M:ℝ)^2 := by nlinarith [Nat.cast_nonneg M (α := ℝ)]
  have hw := polynomial_uniform hM 2 4 (by norm_num)
  have hmul := mul_le_mul hprod hp (pow_nonneg hb 7) (by positivity)
  have hd := div_le_div_of_nonneg_right hmul (show (0:ℝ)≤(2+M)^4 by positivity)
  calc
    _ ≤ 480*(1/64:ℝ)^7*((M:ℝ)^2/(2+(M:ℝ))^4) := by
      convert mul_le_mul_of_nonneg_left hd (by norm_num : (0:ℝ)≤480) using 1 <;> ring
    _ ≤ 480*(1/64:ℝ)^7/(3:ℝ)^2 := by nlinarith [hw]
    _ ≤ _ := by norm_num

theorem cubic_decay_budget {M ell : ℕ} (hM : 1≤M) (hell : ell≤M)
    {decay : ℝ} (hd : 0≤decay) (he : decay≤1/(2+(M:ℝ))^20)
    {C : ℝ} (hC : 0≤C) (hC' : C≤1024) :
    C*(M:ℝ)^2*ell*decay ≤ 1/2048 := by
  have hell' : (ell:ℝ)≤M := by exact_mod_cast hell
  have hpow : (M:ℝ)^2*ell≤(M:ℝ)^3 := by nlinarith [sq_nonneg (M:ℝ)]
  have hm := mul_le_mul hpow he hd (by positivity)
  have hc := mul_le_mul hC' hm (by positivity : (0:ℝ)≤(M:ℝ)^2*ell*decay) (by norm_num)
  have hw := polynomial_uniform hM 3 20 (by norm_num)
  calc
    _ ≤ 1024*((M:ℝ)^3/(2+(M:ℝ))^20) := by convert hc using 1 <;> ring
    _ ≤ 1024/(3:ℝ)^17 := by nlinarith [hw]
    _ ≤ _ := by norm_num

theorem old_contribution {Cp : ℝ} (hCp : lowAllocation≤Cp)
    {M ell : ℕ} (hM : 1≤M) (hell : ell≤M) :
    (128:ℝ)*(FirstHeight.depth M+2)*M*ell*Real.exp (-(lowDimension Cp M:ℝ)/18432) ≤ 1/2048 := by
  have hk := outer_registers_le hM
  have hm := mul_le_mul_of_nonneg_right hk
    (show (0:ℝ)≤128*M*ell*Real.exp (-(lowDimension Cp M:ℝ)/18432) by positivity)
  have hc := cubic_decay_budget hM hell (Real.exp_pos _).le
    (memory_allocation_decay M 20 (by simpa [lowAllocation] using hCp))
    (C := 1024) (by norm_num) le_rfl
  push_cast at hm
  nlinarith

theorem inner_contribution {Cp : ℝ} (hCp : lowAllocation≤Cp)
    {M ell : ℕ} (hM : 1≤M) (hell : ell≤M) :
    (106:ℝ)*(M:ℝ)^2*ell*Real.exp (-(lowDimension Cp M:ℝ)/18432) ≤ 1/2048 :=
  cubic_decay_budget hM hell (Real.exp_pos _).le
    (memory_allocation_decay M 20 (by simpa [lowAllocation] using hCp)) (by norm_num) (by norm_num)

theorem mark_contribution {M ell r : ℕ} (hM : 1≤M) (hell : ell≤M)
    (hr : markAllocation*(M:ℝ)≤r) :
    (2:ℝ)*(M:ℝ)^2*ell*Real.exp (-(r:ℝ)/75497472) ≤ 1/2048 :=
  cubic_decay_budget hM hell (Real.exp_pos _).le (mark_allocation_decay hM hr)
    (by norm_num) (by norm_num)

theorem five_contributions {a b c d e : ℝ} (ha : a≤1/2048) (hb : b≤1/2048)
    (hc : c≤1/2048) (hd : d≤1/2048) (he : e≤1/2048) : a+b+c+d+e≤1/256 := by linarith

end GradientHessian.RepairAllocation
