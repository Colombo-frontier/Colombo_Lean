import Geode.ScaledObjective
import Geode.OracleConjugacy
import Geode.PartialMain

/-! Exact removal of the Lipschitz constant from the query-complexity
parameter: every value and selected tangent vector is rescaled, and the
complete deterministic execution is transported without changing queries. -/
namespace Geode.Lorentz

open Geode.OracleReplay

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def replyScaleEquiv (a : ℝ) (ha : a ≠ 0) : FirstOrderReply E ≃ FirstOrderReply E where
  toFun r := (a * r.1, a • r.2)
  invFun r := (a⁻¹ * r.1, a⁻¹ • r.2)
  left_inv r := by ext <;> simp [mul_assoc, smul_smul, ha]
  right_inv r := by ext <;> simp [mul_assoc, smul_smul, ha]

@[simp] theorem scaledOracle_scale_inverse (a : ℝ) (ha : a ≠ 0)
    (O : Point E → FirstOrderReply E) : scaledOracle a (scaledOracle a⁻¹ O) = O := by
  funext x
  ext <;> simp [scaledOracle, mul_assoc, smul_smul, ha]

@[simp] theorem scaledOracle_inverse_scale (a : ℝ) (ha : a ≠ 0)
    (O : Point E → FirstOrderReply E) : scaledOracle a⁻¹ (scaledOracle a O) = O := by
  funext x
  ext <;> simp [scaledOracle, mul_assoc, smul_smul, ha]

noncomputable def scaledAlgorithm (a : ℝ) (ha : a ≠ 0) (A : FirstOrderAlgorithm E) :
    FirstOrderAlgorithm E :=
  conjugateAlgorithm (Equiv.refl (Point E)) (replyScaleEquiv a ha) A

theorem run_scaledAlgorithm (a : ℝ) (ha : a ≠ 0) (A : FirstOrderAlgorithm E)
    (O : Point E → FirstOrderReply E) (N : ℕ)
    (h : History (Point E) (FirstOrderReply E)) :
    run (scaledAlgorithm a ha A) (fixedResponder (scaledOracle a O)) N
        (historyEquiv (Equiv.refl _) (replyScaleEquiv a ha) h) =
      resultEquiv (Equiv.refl _) (replyScaleEquiv a ha) (run A (fixedResponder O) N h) :=
  run_conjugate (Equiv.refl _) (replyScaleEquiv a ha) A O N h

theorem scaledAlgorithm_finished (a : ℝ) (ha : a ≠ 0) (A : FirstOrderAlgorithm E)
    (O : Point E → FirstOrderReply E) (N : ℕ)
    (h : History (Point E) (FirstOrderReply E)) (output : Point E)
    (hrun : run A (fixedResponder O) N [] = .finished h output) :
    run (scaledAlgorithm a ha A) (fixedResponder (scaledOracle a O)) N [] =
      .finished (historyEquiv (Equiv.refl _) (replyScaleEquiv a ha) h) output :=
  conjugate_finished (Equiv.refl _) (replyScaleEquiv a ha) A O N [] h output hrun

noncomputable def scaledPartialAlgorithm (a : ℝ) (ha : a ≠ 0)
    (A : PartialFirstOrderAlgorithm E) : PartialFirstOrderAlgorithm E :=
  conjugatePartialAlgorithm (Equiv.refl (Point E)) (replyScaleEquiv a ha) A

theorem partialRun_scaledAlgorithm (a : ℝ) (ha : a ≠ 0) (A : PartialFirstOrderAlgorithm E)
    (O : Point E → FirstOrderReply E) (N : ℕ)
    (h : History (Point E) (FirstOrderReply E)) :
    partialRun (scaledPartialAlgorithm a ha A) (fixedResponder (scaledOracle a O)) N
        (historyEquiv (Equiv.refl _) (replyScaleEquiv a ha) h) =
      partialResultEquiv (Equiv.refl _) (replyScaleEquiv a ha)
        (partialRun A (fixedResponder O) N h) :=
  partialRun_conjugate (Equiv.refl _) (replyScaleEquiv a ha) A O N h

theorem Guarantees.scale {o : Point E} {R L ε a : ℝ} {N : ℕ}
    {A : FirstOrderAlgorithm E} (hA : Guarantees o R L ε N A) (ha : 0 < a) :
    Guarantees o R (a * L) ε N (scaledAlgorithm a ha.ne' A) := by
  intro f hf O hO
  have hf₀ : AdmissibleObjective o R L (scaledObjective a⁻¹ f) := by
    simpa only [← mul_assoc, inv_mul_cancel₀ ha.ne', one_mul] using
      hf.const_mul (inv_nonneg.mpr ha.le)
  have hO₀ := hO.const_mul (inv_nonneg.mpr ha.le)
  obtain ⟨h, output, hrun, hgap⟩ := hA (scaledObjective a⁻¹ f) hf₀ (scaledOracle a⁻¹ O) hO₀
  refine ⟨historyEquiv (Equiv.refl _) (replyScaleEquiv a ha.ne') h, output, ?_, ?_⟩
  · simpa only [scaledOracle_scale_inverse a ha.ne' O] using
      scaledAlgorithm_finished a ha.ne' A (scaledOracle a⁻¹ O) N h output hrun
  · intro p hp
    have hp₀ : ∀ y, scaledObjective a⁻¹ f p ≤ scaledObjective a⁻¹ f y :=
      (scaledObjective_minimizer_iff (inv_pos.mpr ha) p).mpr hp
    have hgood := mul_le_mul_of_nonneg_left (hgap p hp₀) ha.le
    calc
      f output - f p = a * (scaledObjective a⁻¹ f output - scaledObjective a⁻¹ f p) := by
        simp only [scaledObjective, mul_sub, ← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul]
      _ ≤ a * (ε * L * R) := hgood
      _ = ε * (a * L) * R := by ring

theorem FeasibleBudget.scale {o : Point E} {R L ε a : ℝ} {N : ℕ}
    (h : FeasibleBudget o R L ε N) (ha : 0 < a) : FeasibleBudget o R (a * L) ε N := by
  obtain ⟨A, hA⟩ := h
  exact ⟨scaledAlgorithm a ha.ne' A, hA.scale ha⟩

theorem feasibleBudget_scale_iff (o : Point E) (R L ε : ℝ) (N : ℕ)
    {a : ℝ} (ha : 0 < a) :
    FeasibleBudget o R (a * L) ε N ↔ FeasibleBudget o R L ε N := by
  constructor
  · intro h
    have hinv := h.scale (inv_pos.mpr ha)
    simpa only [← mul_assoc, inv_mul_cancel₀ ha.ne', one_mul] using hinv
  · intro h
    exact h.scale ha

theorem queryComplexity_scale (o : Point E) (R L ε : ℝ) {a : ℝ} (ha : 0 < a) :
    queryComplexity o R (a * L) ε = queryComplexity o R L ε := by
  simp only [queryComplexity, feasibleBudget_scale_iff o R L ε _ ha]

theorem feasibleBudget_L_normalization (o : Point E) (R ε : ℝ) {L : ℝ}
    (hL : 0 < L) (N : ℕ) : FeasibleBudget o R L ε N ↔ FeasibleBudget o R 1 ε N := by
  simpa only [mul_one] using feasibleBudget_scale_iff o R 1 ε N hL

theorem queryComplexity_L_normalization (o : Point E) (R ε : ℝ) {L : ℝ} (hL : 0 < L) :
    queryComplexity o R L ε = queryComplexity o R 1 ε := by
  simpa only [mul_one] using queryComplexity_scale o R 1 ε hL

theorem uniformComplexity_L_normalization (R ε : ℝ) {L : ℝ} (hL : 0 < L) :
    uniformComplexity R L ε = uniformComplexity R 1 ε := by
  simp only [uniformComplexity, dimensionComplexity, queryComplexity_L_normalization _ _ _ hL]

theorem partialFeasibleBudget_L_normalization (o : Point E) (R ε : ℝ) {L : ℝ}
    (hL : 0 < L) (N : ℕ) :
    PartialFeasibleBudget o R L ε N ↔ PartialFeasibleBudget o R 1 ε N := by
  rw [partialFeasibleBudget_iff, partialFeasibleBudget_iff]
  exact feasibleBudget_L_normalization o R ε hL N

theorem partialQueryComplexity_L_normalization (o : Point E) (R ε : ℝ) {L : ℝ}
    (hL : 0 < L) : partialQueryComplexity o R L ε = partialQueryComplexity o R 1 ε := by
  rw [partialQueryComplexity_eq, partialQueryComplexity_eq]
  exact queryComplexity_L_normalization o R ε hL

theorem partialUniformComplexity_L_normalization (R ε : ℝ) {L : ℝ} (hL : 0 < L) :
    partialUniformComplexity R L ε = partialUniformComplexity R 1 ε := by
  rw [partialUniformComplexity_eq, partialUniformComplexity_eq]
  exact uniformComplexity_L_normalization R ε hL

end Geode.Lorentz
