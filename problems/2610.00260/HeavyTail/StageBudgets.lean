import HeavyTail.LocalizationBudget
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Rounded localization budgets

This module proves the reindexed finite sum in manuscript `lem:phase-sum`,
including ceilings and the factor four for charged raw calls. The index `m`
counts backwards from the final stage. Thus the preceding radius is
`2^(m+1) R_J`, and the confidence logarithm is `ell + (m+1) log 2`.

The explicit premise `1/2 ≤ a * 2^(-2*(m+1))` is the warm-start estimate
`G²/(μ² R_{j-1}²) ≥ 1/2`, weakened using `a = (G²+L^p τ^(2-p))/(μ² R_J²)`.
It is a local ceiling-absorption premise, not the sum being proved.
-/

namespace HeavyTail
open scoped BigOperators

noncomputable def dyadicFactor (γ : ℝ) (m : ℕ) : ℝ :=
  (2 : ℝ) ^ (-γ * (m + 1 : ℕ))

noncomputable def stageConfidence (ell : ℝ) (m : ℕ) : ℝ :=
  ell + (m + 1 : ℕ) * Real.log 2

noncomputable def geometricConfidenceConstant (γ : ℝ) : ℝ :=
  (2 : ℝ) ^ (-γ) / (1 - (2 : ℝ) ^ (-γ)) +
    (2 : ℝ) ^ (-γ) / (1 - (2 : ℝ) ^ (-γ)) ^ 2 * Real.log 2

noncomputable def stageWeight (a b c rp ell : ℝ) (m : ℕ) : ℝ :=
  a * dyadicFactor 2 m + b * dyadicFactor 1 m * stageConfidence ell m +
    c * dyadicFactor rp m * stageConfidence ell m

noncomputable def acceptedStageBudget (C a b c rp ell : ℝ) (m : ℕ) : ℕ :=
  ⌈C * stageWeight a b c rp ell m⌉₊

noncomputable def stageSumConstant (rp : ℝ) : ℝ :=
  max (1 / 3) (max (geometricConfidenceConstant 1) (geometricConfidenceConstant rp))

theorem dyadicFactor_nonneg (γ : ℝ) (m : ℕ) : 0 ≤ dyadicFactor γ m :=
  Real.rpow_nonneg (by norm_num) _

theorem stageConfidence_nonneg {ell : ℝ} (hell : 0 ≤ ell) (m : ℕ) :
    0 ≤ stageConfidence ell m := by
  unfold stageConfidence
  positivity

theorem geometricConfidenceConstant_nonneg {γ : ℝ} (hγ : 0 < γ) :
    0 ≤ geometricConfidenceConstant γ := by
  have hlt : (2 : ℝ) ^ (-γ) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos hγ)
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  unfold geometricConfidenceConstant
  exact add_nonneg (div_nonneg (Real.rpow_nonneg (by norm_num) _) (sub_nonneg.mpr hlt.le))
    (mul_nonneg (div_nonneg (Real.rpow_nonneg (by norm_num) _) (sq_nonneg _)) hlog)

theorem finite_dyadic_sum_bound {γ : ℝ} (hγ : 0 < γ) (N : ℕ) :
    (∑ m ∈ Finset.range N, dyadicFactor γ m) ≤
      (2 : ℝ) ^ (-γ) / (1 - (2 : ℝ) ^ (-γ)) := by
  have h := finite_geometric_confidence_bound
    (r := (2 : ℝ) ^ (-γ)) (ell := 1) (b := 0)
    (Real.rpow_nonneg (by norm_num) _)
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos hγ))
    (by norm_num) (le_refl 0) N
  simpa only [dyadicFactor, Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2),
    mul_zero, add_zero, mul_one] using h

theorem finite_dyadic_two_sum_bound (N : ℕ) :
    (∑ m ∈ Finset.range N, dyadicFactor 2 m) ≤ (1 / 3 : ℝ) := by
  have h := finite_dyadic_sum_bound (γ := 2) (by norm_num) N
  norm_num [Real.rpow_neg, Real.rpow_two] at h ⊢
  exact h

theorem finite_dyadic_confidence_bound {γ ell : ℝ} (hγ : 0 < γ)
    (hell : 1 ≤ ell) (N : ℕ) :
    (∑ m ∈ Finset.range N, dyadicFactor γ m * stageConfidence ell m) ≤
      geometricConfidenceConstant γ * ell :=
  dyadic_confidence_uniform hγ hell N

theorem stageWeight_nonneg {a b c rp ell : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hell : 0 ≤ ell) (m : ℕ) : 0 ≤ stageWeight a b c rp ell m := by
  unfold stageWeight
  exact add_nonneg
    (add_nonneg (mul_nonneg ha (dyadicFactor_nonneg _ _))
      (mul_nonneg (mul_nonneg hb (dyadicFactor_nonneg _ _)) (stageConfidence_nonneg hell _)))
    (mul_nonneg (mul_nonneg hc (dyadicFactor_nonneg _ _)) (stageConfidence_nonneg hell _))

theorem stageWeight_first_le {a b c rp ell : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hell : 0 ≤ ell) (m : ℕ) : a * dyadicFactor 2 m ≤ stageWeight a b c rp ell m := by
  have h1 := mul_nonneg (mul_nonneg hb (dyadicFactor_nonneg 1 m))
    (stageConfidence_nonneg hell m)
  have h2 := mul_nonneg (mul_nonneg hc (dyadicFactor_nonneg rp m))
    (stageConfidence_nonneg hell m)
  unfold stageWeight
  linarith

theorem finite_stageWeight_bound {a b c rp ell : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hrp : 0 < rp)
    (hell : 1 ≤ ell) (N : ℕ) :
    (∑ m ∈ Finset.range N, stageWeight a b c rp ell m) ≤
      a / 3 + b * geometricConfidenceConstant 1 * ell +
        c * geometricConfidenceConstant rp * ell := by
  have h0 := mul_le_mul_of_nonneg_left (finite_dyadic_two_sum_bound N) ha
  have h1 := mul_le_mul_of_nonneg_left
    (finite_dyadic_confidence_bound (γ := 1) (by norm_num) hell N) hb
  have h2 := mul_le_mul_of_nonneg_left (finite_dyadic_confidence_bound hrp hell N) hc
  simp only [stageWeight, Finset.sum_add_distrib]
  simp_rw [mul_assoc, ← Finset.mul_sum]
  nlinarith

theorem finite_stageWeight_uniform {a b c rp ell : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hrp : 0 < rp)
    (hell : 1 ≤ ell) (N : ℕ) :
    (∑ m ∈ Finset.range N, stageWeight a b c rp ell m) ≤
      stageSumConstant rp * (a + b * ell + c * ell) := by
  have h0 : (1 / 3 : ℝ) ≤ stageSumConstant rp := le_max_left _ _
  have h1 : geometricConfidenceConstant 1 ≤ stageSumConstant rp :=
    (le_max_left _ _).trans (le_max_right _ _)
  have h2 : geometricConfidenceConstant rp ≤ stageSumConstant rp :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hm0 := mul_le_mul_of_nonneg_right h0 ha
  have hm1 := mul_le_mul_of_nonneg_right h1 (mul_nonneg hb (by linarith : 0 ≤ ell))
  have hm2 := mul_le_mul_of_nonneg_right h2 (mul_nonneg hc (by linarith : 0 ≤ ell))
  have h := finite_stageWeight_bound ha hb hc hrp hell N
  nlinarith

theorem ceil_le_three_mul {x : ℝ} (hx : (1 / 2 : ℝ) ≤ x) :
    (⌈x⌉₊ : ℝ) ≤ 3 * x := by
  have h := Nat.ceil_lt_add_one (show 0 ≤ x by linarith)
  linarith

/-- Explicit, uniform-in-`N` raw-call bound, including all ceilings. -/
theorem rounded_raw_stage_budget_bound {C a b c rp ell : ℝ}
    (hC : 1 ≤ C) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hrp : 0 < rp) (hell : 1 ≤ ell) (N : ℕ)
    (hwarm : ∀ m ∈ Finset.range N, (1 / 2 : ℝ) ≤ a * dyadicFactor 2 m) :
    4 * (∑ m ∈ Finset.range N, (acceptedStageBudget C a b c rp ell m : ℝ)) ≤
      12 * C * stageSumConstant rp * (a + b * ell + c * ell) := by
  have hround : ∀ m ∈ Finset.range N,
      (acceptedStageBudget C a b c rp ell m : ℝ) ≤ 3 * C * stageWeight a b c rp ell m := by
    intro m hm
    have hw : (1 / 2 : ℝ) ≤ stageWeight a b c rp ell m :=
      (hwarm m hm).trans (stageWeight_first_le hb hc (by linarith) m)
    have hmult := mul_le_mul_of_nonneg_right hC (show 0 ≤ stageWeight a b c rp ell m by linarith)
    have hx : (1 / 2 : ℝ) ≤ C * stageWeight a b c rp ell m := by nlinarith
    simpa only [acceptedStageBudget, mul_assoc] using ceil_le_three_mul hx
  have hsum := Finset.sum_le_sum hround
  rw [← Finset.mul_sum] at hsum
  have hbound := mul_le_mul_of_nonneg_left
    (finite_stageWeight_uniform ha hb hc hrp hell N) (show 0 ≤ 3 * C by linarith)
  nlinarith

theorem dyadicFactor_eq_inverse_rpow (γ : ℝ) (m : ℕ) :
    dyadicFactor γ m = (((2 : ℝ) ^ (m + 1)) ^ γ)⁻¹ := by
  unfold dyadicFactor
  rw [mul_comm (-γ), Real.rpow_natCast_mul (by norm_num),
    Real.rpow_neg (by positivity)]

theorem scaled_radius_power {s μ R rp : ℝ} (hs : 0 ≤ s) (hμ : 0 < μ)
    (hR : 0 < R) (m : ℕ) :
    (s / (μ * ((2 : ℝ) ^ (m + 1) * R))) ^ rp =
      (s / (μ * R)) ^ rp * dyadicFactor rp m := by
  have heq : s / (μ * ((2 : ℝ) ^ (m + 1) * R)) =
      (s / (μ * R)) / (2 : ℝ) ^ (m + 1) := by ring
  rw [heq, Real.div_rpow (by positivity) (by positivity),
    dyadicFactor_eq_inverse_rpow]
  rfl

theorem scaled_radius_linear (G μ R : ℝ) (m : ℕ) :
    G / (μ * ((2 : ℝ) ^ (m + 1) * R)) =
      (G / (μ * R)) * dyadicFactor 1 m := by
  rw [dyadicFactor_eq_inverse_rpow, Real.rpow_one]
  ring

theorem scaled_radius_quadratic (A μ R : ℝ) (m : ℕ) :
    A / (μ ^ 2 * ((2 : ℝ) ^ (m + 1) * R) ^ 2) =
      (A / (μ ^ 2 * R ^ 2)) * dyadicFactor 2 m := by
  rw [dyadicFactor_eq_inverse_rpow, Real.rpow_two]
  ring

noncomputable def physicalStageWeight (A G s μ R rp ell : ℝ) (m : ℕ) : ℝ :=
  A / (μ ^ 2 * ((2 : ℝ) ^ (m + 1) * R) ^ 2) +
    G * stageConfidence ell m / (μ * ((2 : ℝ) ^ (m + 1) * R)) +
    stageConfidence ell m * (s / (μ * ((2 : ℝ) ^ (m + 1) * R))) ^ rp

theorem physicalStageWeight_eq {A G s μ R rp ell : ℝ}
    (hs : 0 ≤ s) (hμ : 0 < μ) (hR : 0 < R) (m : ℕ) :
    physicalStageWeight A G s μ R rp ell m =
      stageWeight (A / (μ ^ 2 * R ^ 2)) (G / (μ * R))
        ((s / (μ * R)) ^ rp) rp ell m := by
  unfold physicalStageWeight stageWeight
  rw [scaled_radius_quadratic, scaled_radius_power hs hμ hR]
  have hmid : G * stageConfidence ell m / (μ * ((2 : ℝ) ^ (m + 1) * R)) =
      (G / (μ * R)) * dyadicFactor 1 m * stageConfidence ell m := by
    calc
      _ = (G / (μ * ((2 : ℝ) ^ (m + 1) * R))) * stageConfidence ell m := by ring
      _ = _ := by rw [scaled_radius_linear]
  rw [hmid]
  ring

/-- `A = G² + L^p τ^(2-p)` and `R = R_J` give the paper's rounded phase sum. -/
theorem physical_raw_stage_budget_bound {C A G s μ R rp ell : ℝ}
    (hC : 1 ≤ C) (hA : 0 ≤ A) (hG : 0 ≤ G) (hs : 0 ≤ s)
    (hμ : 0 < μ) (hR : 0 < R) (hrp : 0 < rp) (hell : 1 ≤ ell) (N : ℕ)
    (hwarm : ∀ m ∈ Finset.range N,
      (1 / 2 : ℝ) ≤ A / (μ ^ 2 * ((2 : ℝ) ^ (m + 1) * R) ^ 2)) :
    4 * (∑ m ∈ Finset.range N, (⌈C * physicalStageWeight A G s μ R rp ell m⌉₊ : ℝ)) ≤
      12 * C * stageSumConstant rp *
        (A / (μ ^ 2 * R ^ 2) + (G / (μ * R)) * ell +
          ((s / (μ * R)) ^ rp) * ell) := by
  have hwarm' : ∀ m ∈ Finset.range N,
      (1 / 2 : ℝ) ≤ (A / (μ ^ 2 * R ^ 2)) * dyadicFactor 2 m := by
    intro m hm
    rw [← scaled_radius_quadratic]
    exact hwarm m hm
  simpa only [physicalStageWeight_eq hs hμ hR, acceptedStageBudget] using
    rounded_raw_stage_budget_bound hC (by positivity) (by positivity)
      (Real.rpow_nonneg (by positivity) rp) hrp hell N hwarm'

end HeavyTail
