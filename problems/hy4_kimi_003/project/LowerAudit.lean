import Mathlib

/-!
Local formal audit of the lower-bound calculations in task006's fixed paper.
These theorems do not formalize adaptive sphere-fiber conditional laws,
conditional expectation, or the all-algorithm minimax theorem.
The lemmas named `conditional_..._reduction` prove only the stated scalar
consequences of their explicit hypotheses.
-/

namespace Task006LowerAudit

noncomputable section

/-- The Bernoulli parameter is a genuine probability in the hard family. -/
theorem rare_probability_bounds (A : ℝ) (hA : 16 ≤ A) :
    0 < 4096 / A ^ 3 ∧ 4096 / A ^ 3 ≤ 1 := by
  have hApos : 0 < A := by linarith
  have hcube : (4096 : ℝ) ≤ A ^ 3 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 16) hA 3
    norm_num at h
    exact h
  constructor
  · positivity
  · exact (div_le_one (pow_pos hApos 3)).2 hcube

/-- Population slope calibration, not an assumption of the minimax result. -/
theorem rare_mean_calibration (L A : ℝ) (hA : 16 ≤ A) :
    (4096 / A ^ 3) * (L * A ^ 2 / 256) = 16 * L / A := by
  have hA0 : A ≠ 0 := by linarith
  field_simp
  ring

/-- The actual real 3/2-moment equality; the exponent is not natural division. -/
theorem rare_moment_calibration (L A : ℝ) (hL : 0 ≤ L) (hA : 16 ≤ A) :
    (4096 / A ^ 3) * (L * A ^ 2 / 256) ^ (3 / 2 : ℝ) =
      L ^ (3 / 2 : ℝ) := by
  have hA0 : A ≠ 0 := by linarith
  have hAn : 0 ≤ A / 16 := by positivity
  have hscale : L * A ^ 2 / 256 = L * (A / 16) ^ 2 := by ring
  have hpow : ((A / 16) ^ 2) ^ (3 / 2 : ℝ) = (A / 16) ^ 3 := by
    calc
      ((A / 16) ^ 2) ^ (3 / 2 : ℝ)
          = (A / 16) ^ ((2 : ℝ) * (3 / 2 : ℝ)) :=
        (Real.rpow_natCast_mul hAn 2 (3 / 2 : ℝ)).symm
      _ = (A / 16) ^ (3 : ℝ) := by norm_num
      _ = (A / 16) ^ (3 : ℕ) := Real.rpow_natCast _ _
  rw [hscale, Real.mul_rpow hL (sq_nonneg _), hpow]
  field_simp
  ring

/-- The actual Bernoulli law parameter, with its probability bounds proved. -/
def rareParameter (A : ℝ) (hA : 16 ≤ A) : unitInterval :=
  ⟨4096 / A ^ 3, le_of_lt (rare_probability_bounds A hA).1,
    (rare_probability_bounds A hA).2⟩

/-- The hard-family moment is an integral under an actual probability measure,
not an abstract variable whose value is assumed to be the target. -/
theorem bernoulli_slope_moment (L A : ℝ) (hL : 0 ≤ L) (hA : 16 ≤ A) :
    ∫ g : ℝ, g ^ (3 / 2 : ℝ)
      ∂(ProbabilityTheory.bernoulliMeasure (L * A ^ 2 / 256) 0 (rareParameter A hA)) =
        L ^ (3 / 2 : ℝ) := by
  rw [ProbabilityTheory.integral_bernoulliMeasure]
  simpa only [rareParameter, smul_eq_mul, Real.zero_rpow (by norm_num : (3 / 2 : ℝ) ≠ 0),
    mul_zero, add_zero] using rare_moment_calibration L A hL hA

/-- The corresponding population slope, integrated over the same Bernoulli law. -/
theorem bernoulli_slope_mean (L A : ℝ) (hA : 16 ≤ A) :
    ∫ g : ℝ, g
      ∂(ProbabilityTheory.bernoulliMeasure (L * A ^ 2 / 256) 0 (rareParameter A hA)) =
        16 * L / A := by
  rw [ProbabilityTheory.integral_bernoulliMeasure]
  simpa only [rareParameter, smul_eq_mul, mul_zero, add_zero] using
    rare_mean_calibration L A hA

/-- Replacing L/A by eps/R is a consequence of the public accuracy ratio. -/
theorem population_slope_from_accuracy (L R eps A : ℝ)
    (hR : 0 < R) (hA : 0 < A) (hratio : L * R = eps * A) :
    16 * L / A = 16 * eps / R := by
  apply (div_eq_div_iff (ne_of_gt hA) (ne_of_gt hR)).2
  nlinarith [hratio]

section LinearGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The sample function is convex on the whole space, hence on the query ball. -/
theorem hard_linear_convex (a : ℝ) (theta : E) :
    ConvexOn ℝ Set.univ (fun x : E => a * inner ℝ theta x) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy b c hb hc hbc
  simp only [inner_add_right, inner_smul_right, smul_eq_mul]
  nlinarith

/-- A unit hidden direction gives the claimed pathwise Lipschitz modulus. -/
theorem hard_linear_lipschitz (a : ℝ) (ha : 0 ≤ a)
    (theta : E) (htheta : ‖theta‖ = 1) (x y : E) :
    |a * inner ℝ theta x - a * inner ℝ theta y| ≤ a * ‖x - y‖ := by
  rw [← mul_sub, ← inner_sub_right, abs_mul, abs_of_nonneg ha]
  have hinner : |inner ℝ theta (x - y)| ≤ ‖theta‖ * ‖x - y‖ := by
    simpa only [Real.norm_eq_abs] using (norm_inner_le_norm (𝕜 := ℝ) theta (x - y))
  simpa only [htheta, one_mul] using mul_le_mul_of_nonneg_left hinner ha

/-- The hard-family minimizer is feasible and attains the asserted value. -/
theorem hard_linear_minimizer (R m : ℝ) (hR : 0 ≤ R)
    (theta : E) (htheta : ‖theta‖ = 1) :
    ‖(-R) • theta‖ ≤ R ∧
      m * inner ℝ theta ((-R) • theta) = -m * R := by
  constructor
  · simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg hR, htheta]
  · rw [inner_smul_right, real_inner_self_eq_norm_sq, htheta]
    ring

/-- Every legal output has at least the linear-family minimum; exact gap formula. -/
theorem hard_linear_gap (R m : ℝ) (_hR : 0 ≤ R) (hm : 0 ≤ m)
    (theta y : E) (htheta : ‖theta‖ = 1) (hy : ‖y‖ ≤ R) :
    0 ≤ m * inner ℝ theta y - (-m * R) ∧
      m * inner ℝ theta y - (-m * R) = m * (R + inner ℝ theta y) := by
  have hinner : |inner ℝ theta y| ≤ R := by
    have h := norm_inner_le_norm (𝕜 := ℝ) theta y
    have h' : |inner ℝ theta y| ≤ ‖y‖ := by
      simpa only [Real.norm_eq_abs, htheta, one_mul] using h
    exact h'.trans hy
  have hlow := (abs_le.mp hinner).1
  constructor
  · have hbase : 0 ≤ R + inner ℝ theta y := by linarith
    nlinarith [mul_nonneg hm hbase]
  · ring

/-- Deterministic orthogonal-center energy increment in the sphere-fiber argument. -/
theorem orthogonal_measurement_energy (c theta u : E)
    (hu : ‖u‖ = 1) (hcu : inner ℝ c u = 0) :
    ‖c + (inner ℝ theta u) • u‖ ^ 2 - ‖c‖ ^ 2 =
      (inner ℝ theta u) ^ 2 := by
  rw [norm_add_sq_real, inner_smul_right, hcu, norm_smul,
    Real.norm_eq_abs, hu]
  simp only [mul_zero, mul_one, add_zero, sq_abs]
  ring

/-- The geometric inequality used after identifying the posterior mean. -/
theorem posterior_mean_geometric_bound (R m : ℝ) (hm : 0 ≤ m)
    (c y : E) (hy : ‖y‖ ≤ R) :
    m * R * (1 - ‖c‖) ≤ m * (R + inner ℝ c y) := by
  have hinner : |inner ℝ c y| ≤ ‖c‖ * R := by
    have h := norm_inner_le_norm (𝕜 := ℝ) c y
    simpa only [Real.norm_eq_abs] using
      h.trans (mul_le_mul_of_nonneg_left hy (norm_nonneg c))
  have hlow := (abs_le.mp hinner).1
  have hbase : R * (1 - ‖c‖) ≤ R + inner ℝ c y := by nlinarith
  calc
    m * R * (1 - ‖c‖) = m * (R * (1 - ‖c‖)) := by ring
    _ ≤ m * (R + inner ℝ c y) := mul_le_mul_of_nonneg_left hbase hm

end LinearGeometry

/-- The exact integer threshold used for dimensions at least eight. -/
def rankThreshold (d : ℕ) : ℕ := (d + 7) / 8

theorem rank_threshold_bounds (d : ℕ) (hd : 8 ≤ d) :
    1 ≤ rankThreshold d ∧ d ≤ 8 * rankThreshold d ∧
      4 * rankThreshold d ≤ d := by
  unfold rankThreshold
  omega

/-- Pure arithmetic in the harmonic energy bound, not a posterior assertion. -/
theorem harmonic_energy_ratio_bound (d k : ℝ) (hk : 0 ≤ k) (hkd : 4 * k ≤ d) :
    0 < d - k + 1 ∧ k / (d - k + 1) < (1 / 3 : ℝ) := by
  have hden : 0 < d - k + 1 := by linarith
  constructor
  · exact hden
  · apply (div_lt_iff₀ hden).2
    linarith

/-- Scalar reduction only: event mass, conditional norm moment, and risk inequality
are explicit premises; their probabilistic derivations are not claimed here. -/
theorem conditional_large_dimension_risk_reduction (eps risk a u : ℝ)
    (heps : 0 < eps) (ha : (1 / 2 : ℝ) ≤ a)
    (hu : u ^ 2 ≤ (2 / 3 : ℝ))
    (hrisk : 16 * eps * a * (1 - u) ≤ risk) : eps < risk := by
  have hu' : u < (7 / 8 : ℝ) := by
    by_contra h
    have hs := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 8) (le_of_not_gt h) 2
    norm_num at hs
    linarith
  have hprod : (1 / 2 : ℝ) * (1 - u) ≤ a * (1 - u) :=
    mul_le_mul_of_nonneg_right ha (by linarith)
  have hsmall : (1 / 16 : ℝ) < a * (1 - u) := by nlinarith
  calc
    eps = (16 * eps) * (1 / 16 : ℝ) := by ring
    _ < (16 * eps) * (a * (1 - u)) :=
      mul_lt_mul_of_pos_left hsmall (by positivity)
    _ = 16 * eps * a * (1 - u) := by ring
    _ ≤ risk := hrisk

/-- Scalar small-dimension reduction; no probabilistic event bound is postulated
as a conclusion of this theorem. -/
theorem conditional_small_dimension_risk_reduction (eps risk a : ℝ)
    (heps : 0 < eps) (ha : (25 / 32 : ℝ) ≤ a)
    (hrisk : 16 * eps * a ≤ risk) : eps < risk := by
  have hsmall : (1 / 16 : ℝ) < a := by linarith
  calc
    eps = (16 * eps) * (1 / 16 : ℝ) := by ring
    _ < (16 * eps) * a := mul_lt_mul_of_pos_left hsmall (by positivity)
    _ ≤ risk := hrisk

/-- Exact calibration of the contradictory reply threshold; a standalone
algebraic equivalence, with no minimax theorem as a hypothesis. -/
theorem budget_threshold_equivalence (A d N : ℝ) (hA : 0 < A) :
    (4096 / A ^ 3) * N ≤ d / 32 ↔ N ≤ d * A ^ 3 / 131072 := by
  rw [div_mul_eq_mul_div, div_le_iff₀ (pow_pos hA 3),
    le_div_iff₀ (by norm_num : (0 : ℝ) < 131072)]
  constructor <;> intro h <;> nlinarith

#print axioms rare_probability_bounds
#print axioms rare_mean_calibration
#print axioms rare_moment_calibration
#print axioms bernoulli_slope_moment
#print axioms bernoulli_slope_mean
#print axioms population_slope_from_accuracy
#print axioms hard_linear_convex
#print axioms hard_linear_lipschitz
#print axioms hard_linear_minimizer
#print axioms hard_linear_gap
#print axioms orthogonal_measurement_energy
#print axioms posterior_mean_geometric_bound
#print axioms rank_threshold_bounds
#print axioms harmonic_energy_ratio_bound
#print axioms conditional_large_dimension_risk_reduction
#print axioms conditional_small_dimension_risk_reduction
#print axioms budget_threshold_equivalence

end
end Task006LowerAudit
