import FreshGradientMinimax.OuterProgram

/-! Exact original-query accounting for the coarse outer program. The
cold initialization logarithm is paid once; warm solves use only Ew. -/

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory
open scoped BigOperators

def outerRunWork (L σ μ η Ec Ew : ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range n, scscSolverWork (3 * L) L σ μ (η / 2) (outerStageEnvelope Ec Ew j)

theorem outerRunWork_succ (L σ μ η Ec Ew : ℝ) (n : ℕ) :
    outerRunWork L σ μ η Ec Ew (n + 1) = scscSolverWork (3 * L) L σ μ (η / 2) Ec +
      n * scscSolverWork (3 * L) L σ μ (η / 2) Ew := by
  induction n with
  | zero => simp [outerRunWork, outerStageEnvelope]
  | succ n ih =>
    change (∑ j ∈ Finset.range (n + 1 + 1), scscSolverWork (3 * L) L σ μ (η / 2) (outerStageEnvelope Ec Ew j)) = _
    rw [Finset.sum_range_succ]
    change outerRunWork L σ μ η Ec Ew (n + 1) + _ = _
    rw [ih]
    simp only [outerStageEnvelope, Nat.succ_ne_zero, ite_false, Nat.cast_add, Nat.cast_one]
    ring

namespace NCObjective
variable {dx dy : ℕ} {L μ σ : ℝ} (F : NCObjective dx dy L μ)

theorem outerStepProgram_cost (O : FreshOracle F σ) (η E : ℝ) (p : Euclid dx × Joint dx dy) :
    Integrable costValue ((outerStepProgram dx dy L σ μ η E).lawKernel O.kernel p) ∧
    (∫ t, costValue t ∂(outerStepProgram dx dy L σ μ η E).lawKernel O.kernel p) =
      scscSolverWork (3 * L) L σ μ (η / 2) E := by
  rw [outerStepProgram, OracleProgram.precompose_law, Kernel.comap_apply]
  have h := F.proximalSolverProgram_cost O (η / 2) E (recenterProximal p)
  rwa [OracleProgram.originalKernel_eq_law] at h

theorem outerRunProgram_cost (O : FreshOracle F σ) (η Ec Ew : ℝ) (n : ℕ) (p : Euclid dx × Joint dx dy) :
    Integrable costValue ((outerRunProgram dx dy L σ μ η Ec Ew n).lawKernel O.kernel p) ∧
    (∫ t, costValue t ∂(outerRunProgram dx dy L σ μ η Ec Ew n).lawKernel O.kernel p) =
      outerRunWork L σ μ η Ec Ew n := by
  induction n with
  | zero =>
    rw [outerRunProgram, OracleProgram.pure_law]
    exact ⟨taggedKernel_cost_integrable _ _ _, by
      simpa only [outerRunWork, Finset.range_zero, Finset.sum_empty, Nat.cast_zero] using
        taggedKernel_mean_cost (Kernel.deterministic id measurable_id) 0 p⟩
  | succ n ih =>
    rw [outerRunProgram, OracleProgram.chain_law]
    have h := costedCompose_cost _ _ p ih.1
      (fun y => (F.outerStepProgram_cost O η (outerStageEnvelope Ec Ew n) y).1) _
      (fun y => (F.outerStepProgram_cost O η (outerStageEnvelope Ec Ew n) y).2)
    simpa only [ih.2, outerRunWork, Finset.sum_range_succ] using h

theorem outerRunProgram_mean_calls (O : FreshOracle F σ) (η Ec Ew : ℝ) (n : ℕ)
    (ν : Measure (Euclid dx × Joint dx dy)) [IsProbabilityMeasure ν] :
    Integrable costValue ((outerRunProgram dx dy L σ μ η Ec Ew n).originalKernel O.kernel ∘ₘ ν) ∧
    (∫ t, costValue t ∂(outerRunProgram dx dy L σ μ η Ec Ew n).originalKernel O.kernel ∘ₘ ν) =
      outerRunWork L σ μ η Ec Ew n := by
  rw [OracleProgram.originalKernel_eq_law]
  have h (p : Euclid dx × Joint dx dy) := F.outerRunProgram_cost O η Ec Ew n p
  have hi := (kernel_moment_from_envelope _ ν costValue costValue_measurable.stronglyMeasurable
    (fun t => Nat.cast_nonneg t.2) _ (integrable_const _) (fun p => (h p).1) (fun p => (h p).2.le)).1
  refine ⟨hi, ?_⟩
  rw [Measure.comp_eq_comp_const_apply] at hi ⊢
  rw [Kernel.integral_comp hi, Kernel.const_apply]
  simp_rw [(h _).2]
  simp only [integral_const, measureReal_univ_eq_one, one_smul]

theorem outerRunProgram_calls_rate (O : FreshOracle F σ) {η Ec Ew : ℝ}
    (hη : 0 < η) (hc : 0 ≤ Ec) (hw : 0 ≤ Ew) (n : ℕ)
    (ν : Measure (Euclid dx × Joint dx dy)) [IsProbabilityMeasure ν] :
    (∫ t, costValue t ∂(outerRunProgram dx dy L σ μ η Ec Ew (n + 1)).originalKernel O.kernel ∘ₘ ν) ≤
      10 ^ 114 * valueLogFactor (3 * L) σ μ η ^ 8 *
        (Real.sqrt ((3 * L) / μ) *
          (Real.log (2 + ((3 * L) / μ) * Ec / η) + n * Real.log (2 + ((3 * L) / μ) * Ew / η)) +
          (n + 1 : ℕ) * (σ ^ 2 / (μ * η))) := by
  rw [(F.outerRunProgram_mean_calls O η Ec Ew (n + 1) ν).2, outerRunWork_succ]
  have hL := F.L_pos
  have hμL : μ ≤ 3 * L := by have := F.μ_le_L; linarith
  have hc' := scscSolverWork_half_rate (ℓ := 3 * L) (α := L) (σ := σ) F.μ_pos hμL hL (by linarith) hη hc
  have hw' := scscSolverWork_half_rate (ℓ := 3 * L) (α := L) (σ := σ) F.μ_pos hμL hL (by linarith) hη hw
  calc
    _ ≤ _ := add_le_add hc' (mul_le_mul_of_nonneg_left hw' (Nat.cast_nonneg n))
    _ = _ := by push_cast; ring

end NCObjective
end FreshGradientMinimax
