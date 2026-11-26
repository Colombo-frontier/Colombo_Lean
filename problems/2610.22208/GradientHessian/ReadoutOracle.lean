import GradientHessian.ReadoutFilter
import GradientHessian.PolynomialQueries
import GradientHessian.MatrixSandwichOracle
import LowRank.MatrixNetBound

/-! Exact source readout, including the fixed zero-denominator convention,
implemented as a measurable finite policy with the literal polynomial degree. -/

namespace GradientHessian.ReadoutOracle

open Matrix Polynomial MeasureTheory LowRank
open scoped BigOperators
noncomputable section

def euclideanNorm {d : ℕ} (v : Fin d → ℝ) : ℝ :=
  ‖(WithLp.equiv 2 (Fin d → ℝ)).symm v‖

theorem euclideanNorm_sqrt {d : ℕ} (v : Fin d → ℝ) :
    euclideanNorm v = Real.sqrt (∑ i, (v i) ^ 2) := by
  simp only [euclideanNorm, EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs]
  rfl

theorem euclideanNorm_measurable (d : ℕ) : Measurable (@euclideanNorm d) := by
  change Measurable (fun v : Fin d → ℝ => euclideanNorm v)
  simp_rw [euclideanNorm_sqrt]
  fun_prop

theorem euclideanNorm_nonneg {d : ℕ} (v : Fin d → ℝ) : 0 ≤ euclideanNorm v :=
  norm_nonneg _

theorem euclideanNorm_smul {d : ℕ} (c : ℝ) (v : Fin d → ℝ) :
    euclideanNorm (c • v) = |c| * euclideanNorm v := by
  change ‖c • (WithLp.equiv 2 (Fin d → ℝ)).symm v‖ = _
  rw [norm_smul, Real.norm_eq_abs]
  rfl

def normalize {d : ℕ} (fallback v : Fin d → ℝ) : Fin d → ℝ :=
  if euclideanNorm v = 0 then fallback else (euclideanNorm v)⁻¹ • v

theorem normalize_measurable {d : ℕ} (fallback : Fin d → ℝ) :
    Measurable (normalize fallback) := by
  apply Measurable.ite ((euclideanNorm_measurable d) (measurableSet_singleton 0))
    measurable_const
  apply measurable_pi_lambda
  intro i
  exact (euclideanNorm_measurable d).inv.mul (measurable_pi_apply i)

theorem normalize_norm_one {d : ℕ} (fallback v : Fin d → ℝ)
    (hf : euclideanNorm fallback = 1) : euclideanNorm (normalize fallback v) = 1 := by
  unfold normalize
  split_ifs with h
  · exact hf
  · rw [euclideanNorm_smul, abs_of_nonneg (inv_nonneg.mpr (euclideanNorm_nonneg v)),
      inv_mul_cancel₀ h]

def postprocess {d : ℕ} (P : Matrix (Fin d) (Fin d) ℝ) (fallback : Fin d → ℝ) :
    MeasurableStateMap (Fin d → ℝ) (Fin d → ℝ) :=
  ⟨fun v => normalize fallback ((1 - P) *ᵥ v), by
    apply (normalize_measurable fallback).comp
    apply measurable_pi_lambda
    intro i
    simp only [Matrix.mulVec, dotProduct]
    fun_prop⟩

def readout {d : ℕ} (M : ℝ) (P A : Matrix (Fin d) (Fin d) ℝ)
    (fallback w : Fin d → ℝ) : Fin d → ℝ :=
  normalize fallback ((1 - P) *ᵥ ((aeval A (ReadoutFilter.filterPolynomial M ReadoutFilter.delta)) *ᵥ w))

def readoutPolicy {d : ℕ} (M : ℝ) (P : Matrix (Fin d) (Fin d) ℝ)
    (fallback : Fin d → ℝ) :
    BoundedTwoSidedPolicy d (Fin d → ℝ) (ReadoutFilter.degree M ReadoutFilter.delta) (Fin d → ℝ) :=
  (PolynomialQueries.polynomialPolicy (ReadoutFilter.filterPolynomial M ReadoutFilter.delta)
    (ReadoutFilter.degree M ReadoutFilter.delta)).mapOutput d (postprocess P fallback) _

/-- The source readout is computable with exactly its advertised degree in
A products, for every matrix and input, including outside the source event. -/
theorem readoutPolicy_exact {d : ℕ} (M : ℝ) (P A : Matrix (Fin d) (Fin d) ℝ)
    (fallback w : Fin d → ℝ) :
    runBoundedTwoSided d (ReadoutFilter.degree M ReadoutFilter.delta)
        (readoutPolicy M P fallback) A w = readout M P A fallback w ∧
      ((readoutPolicy M P fallback).toProgram d (ReadoutFilter.degree M ReadoutFilter.delta) w).calls
        (twoSidedOracle A) = ReadoutFilter.degree M ReadoutFilter.delta :=
  PolynomialQueries.polynomialPolicy_postprocess _ _
    (ReadoutFilter.filterPolynomial_natDegree_le M ReadoutFilter.delta)
    (postprocess P fallback) A w

theorem readout_norm_one {d : ℕ} (M : ℝ) (P A : Matrix (Fin d) (Fin d) ℝ)
    (fallback w : Fin d → ℝ) (hf : euclideanNorm fallback = 1) :
    euclideanNorm (readout M P A fallback w) = 1 := normalize_norm_one _ _ hf

theorem readout_in_kernel {d : ℕ} (M : ℝ) (P A : Matrix (Fin d) (Fin d) ℝ)
    (hP : P * P = P) (fallback w : Fin d → ℝ) (hf : P *ᵥ fallback = 0) :
    P *ᵥ readout M P A fallback w = 0 := by
  unfold readout normalize
  split_ifs
  · exact hf
  · rw [Matrix.mulVec_smul]
    have hzero : P * (1 - P) = 0 := by rw [mul_sub, mul_one, hP, sub_self]
    simp only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hzero, Matrix.zero_mul,
      Matrix.zero_mulVec, smul_zero]

/-- The same exact readout uses one W product for each A product. -/
theorem readout_from_W {d : ℕ} (M scale : ℝ)
    (P D W : Matrix (Fin d) (Fin d) ℝ) (hD : Dᵀ = D) (hW : Wᵀ = W)
    (fallback w : Fin d → ℝ) :
    let program := (readoutPolicy M P fallback).toProgram d
      (ReadoutFilter.degree M ReadoutFilter.delta) w
    let simulated := program.simulate (MatrixSandwichOracle.encode D)
      (MatrixSandwichOracle.decode scale D)
    simulated.eval (fun z => W *ᵥ z) =
        readout M P (MatrixSandwichOracle.transformedMatrix scale D W) fallback w ∧
      simulated.calls (fun z => W *ᵥ z) = ReadoutFilter.degree M ReadoutFilter.delta ∧
      simulated.HasBudget (ReadoutFilter.degree M ReadoutFilter.delta) := by
  dsimp only
  have hs := MatrixSandwichOracle.simulate_exact scale D W hD hW
    ((readoutPolicy M P fallback).toProgram d (ReadoutFilter.degree M ReadoutFilter.delta) w)
  have hr := readoutPolicy_exact M P (MatrixSandwichOracle.transformedMatrix scale D W) fallback w
  exact ⟨hs.1.trans hr.1, hs.2.trans hr.2,
    MatrixSandwichOracle.simulate_budget scale D _
      (BoundedTwoSidedPolicy.budget_toProgram _ _ _ _)⟩

end
end GradientHessian.ReadoutOracle
