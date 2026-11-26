import GradientHessian.AllocationParameters
import GradientHessian.MemoryHitProbability

/-! Explicit polynomial decay supplied by the logarithmic low-register
allocation. These are actual fixed-point probability bounds; adaptive stopped
test lists and their total repair charges are separate constructions. -/

noncomputable section
namespace GradientHessian.AllocationTails
open AllocationParameters MeasureTheory
open scoped InnerProductSpace

theorem exp_neg_log_power (M q : ℕ) :
    Real.exp (-(q:ℝ)*logInput M) = 1/(2+(M:ℝ))^q := by
  rw [show -(q:ℝ)*logInput M = -((q:ℝ)*logInput M) by ring,
    Real.exp_neg, Real.exp_nat_mul]
  rw [logInput, Real.exp_log (by positivity)]
  simp only [one_div]

theorem memory_allocation_decay {Cp : ℝ} (M q : ℕ) (hCp : 18432*(q:ℝ)≤Cp) :
    Real.exp (-(lowDimension Cp M:ℝ)/18432) ≤ 1/(2+(M:ℝ))^q := by
  rw [← exp_neg_log_power M q]
  apply Real.exp_le_exp.mpr
  have hdim := lowDimension_ge_log Cp M
  have hmul := mul_le_mul_of_nonneg_right hCp (logInput_pos M).le
  linarith

theorem memory_repair_polynomial {Cp : ℝ} (M q : ℕ) (hCp : 18432*(q:ℝ)≤Cp)
    (r : ℝ) (x : EuclideanSpace ℝ (Fin (lowDimension Cp M))) :
    (SphereGaussian.sphereLaw (EuclideanSpace ℝ (Fin (lowDimension Cp M)))).real
      {v | (1/8:ℝ) < |LatchChain.u r v x|} ≤ 2/(2+(M:ℝ))^q := by
  have hp : 0<lowDimension Cp M := lt_of_lt_of_le (by norm_num) (lowDimension_ge_eight Cp M)
  have h := MemoryHitProbability.manuscript_memory_hit hp r x
  have he := mul_le_mul_of_nonneg_left (memory_allocation_decay M q hCp) (by norm_num : (0:ℝ)≤2)
  exact h.trans (by simpa only [mul_one_div] using he)

theorem polynomial_weight_bound (M a q : ℕ) (ha : a≤q) :
    (M:ℝ)^a/(2+(M:ℝ))^q ≤ 1/(2+(M:ℝ))^(q-a) := by
  have hp : 0<2+(M:ℝ) := by positivity
  have hpow : (M:ℝ)^a≤(2+(M:ℝ))^a := pow_le_pow_left₀ (Nat.cast_nonneg M) (by linarith) a
  have he : (2+(M:ℝ))^q=(2+(M:ℝ))^a*(2+(M:ℝ))^(q-a) := by
    rw [← pow_add, Nat.add_sub_of_le ha]
  rw [he]
  calc
    _ ≤ (2+(M:ℝ))^a / ((2+(M:ℝ))^a*(2+(M:ℝ))^(q-a)) :=
      div_le_div_of_nonneg_right hpow (by positivity)
    _ = _ := by field_simp

end GradientHessian.AllocationTails
