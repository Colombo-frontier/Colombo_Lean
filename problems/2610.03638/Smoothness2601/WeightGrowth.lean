import Smoothness2601.OrderTradeoff
import Mathlib.Data.Nat.Factorial.Basic

/-!
# Order-uniform differentiation weight growth

This proves the factorial estimates used in `lem:W` directly from the
exponential series and elementary factorial/power inequalities. No Stirling
estimate or asymptotic bound is assumed.

The parameter `L` denotes the product `barLambda * V` in eq:Ar. Both factors
are at least one in the manuscript, as are `M = barM` and the order `r`.
-/
noncomputable section
namespace Smoothness2601

theorem positive_nat_root_pow {r : ℕ} (hr : 1 ≤ r) {x : ℝ} (hx : 0 ≤ x) :
    (x ^ r) ^ (1 / (r : ℝ)) = x := by
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hr))
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  field_simp

theorem factorial_successor_upper_pow (r : ℕ) :
    ((r + 1).factorial : ℝ) ≤ (2 * (r : ℝ)) ^ r := by
  have hf : (r.factorial : ℝ) ≤ (r : ℝ) ^ r := by exact_mod_cast Nat.factorial_le_pow r
  have hp : (r + 1 : ℝ) ≤ (2 : ℝ) ^ r := by exact_mod_cast Nat.succ_le_of_lt (Nat.lt_two_pow_self (n := r))
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, mul_pow]
  exact mul_le_mul hp hf (by positivity) (by positivity)

theorem factorial_lower_pow (r : ℕ) :
    ((r : ℝ) / Real.exp 1) ^ r ≤ (r.factorial : ℝ) := by
  have hfpos : (0 : ℝ) < r.factorial := by exact_mod_cast Nat.factorial_pos r
  have h := (div_le_iff₀ hfpos).mp (Real.pow_div_factorial_le_exp (r : ℝ) (Nat.cast_nonneg r) r)
  have he : Real.exp (r : ℝ) = Real.exp 1 ^ r := by
    simpa only [mul_one] using Real.exp_nat_mul 1 r
  rw [he] at h
  rw [div_pow]
  exact (div_le_iff₀ (pow_pos (Real.exp_pos _) _)).2 (by nlinarith)

def factorialRoot (r : ℕ) : ℝ := ((r + 1).factorial : ℝ) ^ (1 / (r : ℝ))

theorem factorialRoot_bounds {r : ℕ} (hr : 1 ≤ r) :
    (r : ℝ) / Real.exp 1 ≤ factorialRoot r ∧ factorialRoot r ≤ 2 * r := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hr)
  have hf : (r.factorial : ℝ) ≤ ((r + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_le (Nat.le_succ r)
  constructor
  · have h := Real.rpow_le_rpow (pow_nonneg (div_nonneg hr0.le (Real.exp_pos _).le) r)
      ((factorial_lower_pow r).trans hf) (by positivity : (0 : ℝ) ≤ 1 / r)
    simpa only [positive_nat_root_pow hr (div_nonneg hr0.le (Real.exp_pos _).le)] using h
  · have h := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ (r + 1).factorial)
      (factorial_successor_upper_pow r) (by positivity : (0 : ℝ) ≤ 1 / r)
    simpa only [positive_nat_root_pow hr (by positivity : (0 : ℝ) ≤ 2 * r)] using h

theorem stencil_root_le_two {r n : ℕ} (hr : 1 ≤ r) (hn : n ≤ r + 1) :
    (n : ℝ) ^ (1 / (r : ℝ)) ≤ 2 := by
  have hn2 : (n : ℝ) ≤ (2 : ℝ) ^ r := by
    exact_mod_cast hn.trans (Nat.succ_le_of_lt (Nat.lt_two_pow_self (n := r)))
  have h := Real.rpow_le_rpow (Nat.cast_nonneg n) hn2 (by positivity : (0 : ℝ) ≤ 1 / r)
  simpa only [positive_nat_root_pow hr (by norm_num : (0 : ℝ) ≤ 2)] using h

def factorialGrowthConstant (β : ℝ) : ℝ :=
  max ((2 : ℝ) ^ (β - 1)) ((Real.exp 1)⁻¹ ^ (β - 1))

theorem factorialGrowthConstant_pos (β : ℝ) : 0 < factorialGrowthConstant β :=
  lt_of_lt_of_le (Real.rpow_pos_of_pos (by norm_num) _) (le_max_left _ _)

theorem factorialRoot_power_bound {r : ℕ} (hr : 1 ≤ r) (β : ℝ) :
    factorialRoot r ^ (β - 1) ≤ factorialGrowthConstant β * (r : ℝ) ^ (β - 1) := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hr)
  have hfpos : 0 < factorialRoot r := by unfold factorialRoot; positivity
  by_cases hβ : 1 ≤ β
  · have h := Real.rpow_le_rpow hfpos.le (factorialRoot_bounds hr).2 (sub_nonneg.mpr hβ)
    rw [Real.mul_rpow (by norm_num) hr0.le] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hr0.le _))
  · have h := Real.rpow_le_rpow_of_exponent_nonpos (div_pos hr0 (Real.exp_pos _))
      (factorialRoot_bounds hr).1 (by linarith : β - 1 ≤ 0)
    rw [div_eq_mul_inv, Real.mul_rpow hr0.le (inv_nonneg.mpr (Real.exp_pos _).le)] at h
    calc
      factorialRoot r ^ (β - 1) ≤ (r : ℝ) ^ (β - 1) * (Real.exp 1)⁻¹ ^ (β - 1) := h
      _ ≤ factorialGrowthConstant β * (r : ℝ) ^ (β - 1) := by
        simpa only [factorialGrowthConstant, mul_comm] using
          mul_le_mul_of_nonneg_left (le_max_right ((2 : ℝ) ^ (β - 1))
            ((Real.exp 1)⁻¹ ^ (β - 1))) (Real.rpow_nonneg hr0.le (β - 1))

theorem factorial_power_as_root {r : ℕ} (β : ℝ) :
    ((r + 1).factorial : ℝ) ^ ((β - 1) / (r : ℝ)) = factorialRoot r ^ (β - 1) := by
  unfold factorialRoot
  rw [← Real.rpow_mul (by positivity)]
  congr 1
  ring

def normalizedWeight (r n : ℕ) (M L β a : ℝ) : ℝ :=
  (n : ℝ) ^ (1 + 1 / (r : ℝ)) * M ^ (1 / (r : ℝ)) *
    L ^ (1 + 1 / (r : ℝ)) * ((r + 1).factorial : ℝ) ^ ((β - 1) / (r : ℝ)) *
    a ^ (-1 / (r : ℝ))

def weightGrowthConstant (M L β : ℝ) : ℝ := 4 * M * L ^ 2 * factorialGrowthConstant β

theorem weightGrowthConstant_pos {M L : ℝ} (hM : 1 ≤ M) (hL : 1 ≤ L) (β : ℝ) :
    0 < weightGrowthConstant M L β := by
  unfold weightGrowthConstant
  exact mul_pos (mul_pos (mul_pos (by norm_num) (zero_lt_one.trans_le hM))
    (pow_pos (zero_lt_one.trans_le hL) _)) (factorialGrowthConstant_pos β)

/-- The manuscript's substituted weight expression has an order-independent
bound. The proof works for all real β, hence in particular for β ≥ 0. -/
theorem normalizedWeight_bound {r n : ℕ} (hr : 1 ≤ r) (hrn : r ≤ n) (hn : n ≤ r + 1)
    {M L a : ℝ} (hM : 1 ≤ M) (hL : 1 ≤ L) (ha : 0 < a) (β : ℝ) :
    normalizedWeight r n M L β a ≤
      weightGrowthConstant M L β * (r : ℝ) ^ β * a ^ (-1 / (r : ℝ)) := by
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hr0 := zero_lt_one.trans_le hr1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (hr.trans hrn))
  have hn2 : (n : ℝ) ≤ 2 * r := by
    have hnr : (n : ℝ) ≤ r + 1 := by exact_mod_cast hn
    linarith
  have hinv : (1 : ℝ) / r ≤ 1 := (div_le_one hr0).2 hr1
  have hnPow : (n : ℝ) ^ (1 + 1 / (r : ℝ)) ≤ 4 * r := by
    rw [Real.rpow_add hn0, Real.rpow_one]
    have h := mul_le_mul_of_nonneg_left (stencil_root_le_two hr hn) hn0.le
    nlinarith
  have hMpow : M ^ (1 / (r : ℝ)) ≤ M := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hM hinv
  have hLpow : L ^ (1 + 1 / (r : ℝ)) ≤ L ^ 2 := by
    convert Real.rpow_le_rpow_of_exponent_le hL (show 1 + 1 / (r : ℝ) ≤ 2 by linarith) using 1
    norm_num
  have hF := factorialRoot_power_bound hr β
  rw [← factorial_power_as_root β] at hF
  have hprod := mul_le_mul
    (mul_le_mul
      (mul_le_mul hnPow hMpow (Real.rpow_nonneg (zero_le_one.trans hM) _) (by positivity))
      hLpow (Real.rpow_nonneg (zero_le_one.trans hL) _) (by positivity))
    hF (by positivity) (by positivity)
  have hfinal := mul_le_mul_of_nonneg_right hprod (Real.rpow_nonneg ha.le (-1 / (r : ℝ)))
  have hrpow : (r : ℝ) * (r : ℝ) ^ (β - 1) = (r : ℝ) ^ β := by
    calc
      (r : ℝ) * (r : ℝ) ^ (β - 1) = (r : ℝ) ^ (1 : ℝ) * (r : ℝ) ^ (β - 1) := by rw [Real.rpow_one]
      _ = (r : ℝ) ^ (1 + (β - 1)) := (Real.rpow_add hr0 1 (β - 1)).symm
      _ = (r : ℝ) ^ β := by congr 1; ring
  unfold normalizedWeight
  apply hfinal.trans_eq
  unfold weightGrowthConstant
  calc
    _ = (4 * M * L ^ 2 * factorialGrowthConstant β) *
        ((r : ℝ) * (r : ℝ) ^ (β - 1)) * a ^ (-1 / (r : ℝ)) := by ring
    _ = _ := by rw [hrpow]

def taylorCoefficient (r : ℕ) (M L β : ℝ) : ℝ :=
  M * L ^ (r + 1) * ((r + 1).factorial : ℝ) ^ (β - 1)

def differentiationRadius (r n : ℕ) (M L β a : ℝ) : ℝ :=
  (a / ((n : ℝ) * taylorCoefficient r M L β)) ^ (1 / (r : ℝ))

theorem taylorCoefficient_pos (r : ℕ) {M L : ℝ} (hM : 0 < M) (hL : 0 < L) (β : ℝ) :
    0 < taylorCoefficient r M L β := by unfold taylorCoefficient; positivity

theorem differentiationRadius_pos {r n : ℕ} (hn : 1 ≤ n) {M L a : ℝ}
    (hM : 0 < M) (hL : 0 < L) (ha : 0 < a) (β : ℝ) :
    0 < differentiationRadius r n M L β a := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  unfold differentiationRadius
  exact Real.rpow_pos_of_pos (div_pos ha (mul_pos hn0 (taylorCoefficient_pos r hM hL β))) _

theorem differentiationRadius_bias_exact {r n : ℕ} (hr : 1 ≤ r) (hn : 1 ≤ n)
    {M L a : ℝ} (hM : 0 < M) (hL : 0 < L) (ha : 0 < a) (β : ℝ) :
    (n : ℝ) * taylorCoefficient r M L β * differentiationRadius r n M L β a ^ r = a := by
  have hr0 : r ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hr)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hA := taylorCoefficient_pos r hM hL β
  unfold differentiationRadius
  rw [one_div, Real.rpow_inv_natCast_pow (div_nonneg ha.le (mul_nonneg hn0.le hA.le)) hr0]
  field_simp

theorem coefficient_root_formula {r : ℕ} (hr : 1 ≤ r) {M L : ℝ}
    (hM : 0 < M) (hL : 0 < L) (β : ℝ) :
    taylorCoefficient r M L β ^ (1 / (r : ℝ)) =
      M ^ (1 / (r : ℝ)) * L ^ (1 + 1 / (r : ℝ)) *
        ((r + 1).factorial : ℝ) ^ ((β - 1) / (r : ℝ)) := by
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hr))
  unfold taylorCoefficient
  rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow hM.le (by positivity)]
  have hLpow : (L ^ (r + 1)) ^ (1 / (r : ℝ)) = L ^ (1 + 1 / (r : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL.le]
    congr 1
    push_cast
    field_simp
  have hFpow : (((r + 1).factorial : ℝ) ^ (β - 1)) ^ (1 / (r : ℝ)) =
      ((r + 1).factorial : ℝ) ^ ((β - 1) / (r : ℝ)) := by
    rw [← Real.rpow_mul (by positivity)]
    congr 1
    ring
  rw [hLpow, hFpow]

/-- Exact substitution of the source radius into n/h. -/
theorem radius_weight_formula {r n : ℕ} (hr : 1 ≤ r) (hn : 1 ≤ n)
    {M L a : ℝ} (hM : 0 < M) (hL : 0 < L) (ha : 0 < a) (β : ℝ) :
    (n : ℝ) / differentiationRadius r n M L β a = normalizedWeight r n M L β a := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hA := taylorCoefficient_pos r hM hL β
  have haPow : a ^ (-1 / (r : ℝ)) = (a ^ (1 / (r : ℝ)))⁻¹ := by
    have he : -1 / (r : ℝ) = -(1 / (r : ℝ)) := by ring
    rw [he, Real.rpow_neg ha.le]
  unfold differentiationRadius normalizedWeight
  rw [Real.div_rpow ha.le (mul_nonneg hn0.le hA.le), div_div_eq_mul_div,
    Real.mul_rpow hn0.le hA.le, coefficient_root_formula hr hM hL β,
    Real.rpow_add hn0, Real.rpow_one]
  rw [haPow]
  ring

/-- `lem:W` for the actual radius. The same explicit constant works for every
positive order and every stencil size between r and r+1, in particular the
smallest odd integer n ≥ r. The source restriction a<1 is unnecessary here. -/
theorem differentiation_weight_bound {M L β : ℝ} (hM : 1 ≤ M) (hL : 1 ≤ L) :
    ∃ C : ℝ, 0 < C ∧ ∀ (r n : ℕ), 1 ≤ r → r ≤ n → n ≤ r + 1 →
      ∀ a : ℝ, 0 < a →
        (n : ℝ) / differentiationRadius r n M L β a ≤ C * (r : ℝ) ^ β * a ^ (-1 / (r : ℝ)) := by
  refine ⟨weightGrowthConstant M L β, weightGrowthConstant_pos hM hL β, ?_⟩
  intro r n hr hrn hn a ha
  rw [radius_weight_formula hr (hr.trans hrn) (zero_lt_one.trans_le hM) (zero_lt_one.trans_le hL) ha β]
  exact normalizedWeight_bound hr hrn hn hM hL ha β

end Smoothness2601
