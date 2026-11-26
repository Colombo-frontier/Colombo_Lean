import Geode.ProjectedStep
import Geode.IterationOracle
import Geode.OracleModel
import Geode.UpperRecurrence

/-!
# The actual projected-subgradient upper algorithm

This file proves the manuscript's full upper bound for the concrete hyperbolic
metric, actual first-order oracle model, and a deterministic history algorithm.
All geometric one-step estimates are proved in imported modules.
-/

namespace Geode.Lorentz

open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def upperQueryBudget (R ε : ℝ) : ℕ :=
  ⌈Geode.curvatureFactor (3 * R) / ε ^ 2⌉₊

noncomputable def upperStepSize (R L ε : ℝ) : ℝ :=
  R / (L * Real.sqrt (Geode.curvatureFactor (3 * R) * (upperQueryBudget R ε : ℝ)))

noncomputable def projectedAlgorithm (o : Point E) (R L ε : ℝ) (hR : 0 ≤ R) :
    FirstOrderAlgorithm E :=
  Geode.IterationOracle.algorithm o
    (fun x (reply : FirstOrderReply E) => projectedStep o R hR (upperStepSize R L ε) x reply.2)
    Prod.fst (upperQueryBudget R ε)

theorem upper_parameters {R L ε : ℝ} (hR : 0 < R) (hL : 0 < L) (hε : 0 < ε) :
    0 < upperQueryBudget R ε ∧ 0 < upperStepSize R L ε ∧ upperStepSize R L ε * L ≤ R := by
  have hζ : 1 ≤ Geode.curvatureFactor (3 * R) :=
    Geode.one_le_curvatureFactor (by linarith)
  have hζpos : 0 < Geode.curvatureFactor (3 * R) := by linarith
  have hN : 0 < upperQueryBudget R ε := Nat.ceil_pos.mpr (by positivity)
  have hN1 : (1 : ℝ) ≤ (upperQueryBudget R ε : ℝ) := by
    exact_mod_cast (show 1 ≤ upperQueryBudget R ε from hN)
  have hprod : 1 ≤ Geode.curvatureFactor (3 * R) * (upperQueryBudget R ε : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_right hζ (show (0 : ℝ) ≤ upperQueryBudget R ε by positivity)]
  have hs1 : 1 ≤ Real.sqrt (Geode.curvatureFactor (3 * R) * (upperQueryBudget R ε : ℝ)) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hprod
  have hs : 0 < Real.sqrt (Geode.curvatureFactor (3 * R) * (upperQueryBudget R ε : ℝ)) := by
    linarith
  refine ⟨hN, div_pos hR (mul_pos hL hs), ?_⟩
  unfold upperStepSize
  rw [div_mul_eq_mul_div, div_le_iff₀ (mul_pos hL hs)]
  nlinarith [mul_le_mul_of_nonneg_left hs1 (mul_pos hR hL).le]

/-- The history algorithm has the full budget-and-output guarantee for every
admissible objective and every fixed legal selected-subgradient oracle. -/
theorem projectedAlgorithm_guarantees (o : Point E) {R L ε : ℝ}
    (hR : 0 < R) (hL : 0 < L) (hε : 0 < ε) :
    Guarantees o R L ε (upperQueryBudget R ε) (projectedAlgorithm o R L ε hR.le) := by
  obtain ⟨hN, hα, hαL⟩ := upper_parameters hR hL hε
  have hζ : 0 < Geode.curvatureFactor (3 * R) :=
    lt_of_lt_of_le (by norm_num) (Geode.one_le_curvatureFactor (by linarith))
  intro f hf O hO
  let step : Point E → FirstOrderReply E → Point E :=
    fun x reply => projectedStep o R hR.le (upperStepSize R L ε) x reply.2
  let X : ℕ → Point E := Geode.IterationOracle.iterate o step O
  have hball : ∀ n, dist o (X n) ≤ R := by
    intro n
    cases n with
    | zero => change dist o o ≤ R; simpa using hR.le
    | succ n => exact projectedStep_mem o hR.le _ _ _
  obtain ⟨p₀, hp₀, hmin₀⟩ := hf.minimizer
  have hstart : dist (X 0) p₀ ^ 2 ≤ R ^ 2 := by
    change dist o p₀ ^ 2 ≤ R ^ 2
    exact (sq_le_sq₀ dist_nonneg hR.le).mpr hp₀
  have hrec : ∀ j < upperQueryBudget R ε,
      dist (X (j + 1)) p₀ ^ 2 ≤ dist (X j) p₀ ^ 2 -
        2 * upperStepSize R L ε * (f (X j) - f p₀) +
        Geode.curvatureFactor (3 * R) * upperStepSize R L ε ^ 2 * L ^ 2 := by
    intro j _
    exact projected_subgradient_step o (X j) p₀ hR hL.le hα.le (hball j) hp₀ hαL
      hf.lipschitz (O (X j)).2 (hO (X j)).2
  obtain ⟨i, hi, hgap⟩ := Geode.upper_recurrence_accuracy
    (fun j => dist (X j) p₀ ^ 2) (fun j => f (X j) - f p₀)
    (Geode.curvatureFactor (3 * R)) L R ε (upperQueryBudget R ε)
    hN hζ hL hR hε (Nat.le_ceil _) hstart (sq_nonneg _) hrec
  obtain ⟨j, hj, hrun, hbest⟩ := Geode.IterationOracle.algorithm_spec o step
    (Prod.fst : FirstOrderReply E → ℝ) (upperQueryBudget R ε) hN O
  refine ⟨Geode.IterationOracle.history o step O (upperQueryBudget R ε), X j, hrun, ?_⟩
  intro p hmin
  have hbestf : f (X j) ≤ f (X i) := by
    have h := hbest i hi
    change (O (X j)).1 ≤ (O (X i)).1 at h
    simpa only [(hO (X j)).1, (hO (X i)).1] using h
  have heq : f p = f p₀ := le_antisymm (hmin p₀) (hmin₀ p)
  rw [heq]
  linarith

theorem projected_feasible_budget (o : Point E) {R L ε : ℝ}
    (hR : 0 < R) (hL : 0 < L) (hε : 0 < ε) :
    FeasibleBudget o R L ε (upperQueryBudget R ε) :=
  ⟨projectedAlgorithm o R L ε hR.le, projectedAlgorithm_guarantees o hR hL hε⟩

theorem queryComplexity_upper (o : Point E) {R L ε : ℝ}
    (hR : 0 < R) (hL : 0 < L) (hε : 0 < ε) :
    queryComplexity o R L ε ≤ (upperQueryBudget R ε : ℝ≥0∞) :=
  queryComplexity_le_of_feasible (projected_feasible_budget o hR hL hε)

theorem upperQueryBudget_le_three {R ε : ℝ} (hR : 0 < R) :
    upperQueryBudget R ε ≤ ⌈3 * Geode.curvatureFactor R / ε ^ 2⌉₊ := by
  apply Nat.ceil_le_ceil
  exact div_le_div_of_nonneg_right (Geode.curvatureFactor_three_le hR) (sq_nonneg ε)

theorem queryComplexity_upper_three (o : Point E) {R L ε : ℝ}
    (hR : 0 < R) (hL : 0 < L) (hε : 0 < ε) :
    queryComplexity o R L ε ≤ (⌈3 * Geode.curvatureFactor R / ε ^ 2⌉₊ : ℝ≥0∞) := by
  apply (queryComplexity_upper o hR hL hε).trans
  exact_mod_cast upperQueryBudget_le_three (ε := ε) hR

theorem uniformComplexity_upper {R L ε : ℝ}
    (hR : 0 < R) (hL : 0 < L) (hε : 0 < ε) :
    uniformComplexity R L ε ≤ (upperQueryBudget R ε : ℝ≥0∞) := by
  apply uniformComplexity_le_of_dimensions
  intro d _
  exact queryComplexity_upper (origin : HyperbolicSpace d) hR hL hε

/-- The upper half of the manuscript's matching-complexity theorem, over the
actual dimension-uniform minimax definition. -/
theorem uniformComplexity_upper_three {R L ε : ℝ}
    (hR : 0 < R) (hL : 0 < L) (hε : 0 < ε) :
    uniformComplexity R L ε ≤ (⌈3 * Geode.curvatureFactor R / ε ^ 2⌉₊ : ℝ≥0∞) := by
  apply (uniformComplexity_upper hR hL hε).trans
  exact_mod_cast upperQueryBudget_le_three (ε := ε) hR

end Geode.Lorentz
