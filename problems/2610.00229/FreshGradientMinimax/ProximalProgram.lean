import FreshGradientMinimax.ProgramResponse
import FreshGradientMinimax.SCSCPrimitive

/-! A proximal SCSC solve implemented using only the original NC--SC
oracle. Centers are continuous input state. The complete output/count
law on a fixed center equals the verified SCSC law; cost bounds already
hold for arbitrary correlated random centers and starting points. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory

def proximalSolverProgram (dx dy : ℕ) (L σ μ η E₀ : ℝ) :
    OracleProgram dx dy (Euclid dx × Joint dx dy) (Euclid dx × Joint dx dy) :=
  (scscSolverProgram dx dy (3 * L) L σ μ η E₀).adaptResponses (proximalResponse L)
    (proximalResponse_continuous L).measurable

namespace NCObjective
variable {dx dy : ℕ} {L μ σ : ℝ} (F : NCObjective dx dy L μ)

theorem proximalSolverProgram_fiber (O : FreshOracle F σ) (η E₀ : ℝ) (c : Euclid dx) :
    ((proximalSolverProgram dx dy L σ μ η E₀).originalKernel O.kernel).comap
      (fun z => (c, z)) measurable_prodMk_left =
      ((scscSolverProgram dx dy (3 * L) L σ μ η E₀).originalKernel (O.proximal c).kernel).map
        (costedMap (fun z => (c, z))) := by
  rw [FreshOracle.proximal_kernel]
  exact OracleProgram.adaptResponses_original _ _ _ _ _

theorem proximalSolverProgram_apply (O : FreshOracle F σ) (η E₀ : ℝ) (c : Euclid dx) (z : Joint dx dy) :
    (proximalSolverProgram dx dy L σ μ η E₀).originalKernel O.kernel (c, z) =
      ((scscSolverProgram dx dy (3 * L) L σ μ η E₀).originalKernel (O.proximal c).kernel z).map
        (costedMap (fun w => (c, w))) := by
  have h := congrArg (fun K : Kernel (Joint dx dy) ((Euclid dx × Joint dx dy) × ℕ) => K z)
    (F.proximalSolverProgram_fiber O η E₀ c)
  dsimp only at h
  rw [Kernel.comap_apply, Kernel.map_apply _ (costedMap_measurable measurable_prodMk_left)] at h
  exact h

theorem proximalSolverProgram_fixed_law (O : FreshOracle F σ) (η E₀ : ℝ) (c : Euclid dx)
    (ν : Measure (Joint dx dy)) :
    (proximalSolverProgram dx dy L σ μ η E₀).originalKernel O.kernel ∘ₘ ν.map (fun z => (c, z)) =
      ((scscSolverProgram dx dy (3 * L) L σ μ η E₀).originalKernel (O.proximal c).kernel ∘ₘ ν).map
        (costedMap (fun z => (c, z))) := by
  rw [← comap_comp_measure _ _ measurable_prodMk_left, F.proximalSolverProgram_fiber,
    ← Measure.map_comp _ _ (costedMap_measurable measurable_prodMk_left)]

theorem proximalSolverProgram_cost (O : FreshOracle F σ) (η E₀ : ℝ) (p : Euclid dx × Joint dx dy) :
    Integrable costValue ((proximalSolverProgram dx dy L σ μ η E₀).originalKernel O.kernel p) ∧
    (∫ t, costValue t ∂(proximalSolverProgram dx dy L σ μ η E₀).originalKernel O.kernel p) =
      scscSolverWork (3 * L) L σ μ η E₀ := by
  have h := (F.proximalObjective p.1).scscSolverProgram_mean_calls (O.proximal p.1) η E₀ (Measure.dirac p.2)
  rw [Measure.dirac_bind ((scscSolverProgram dx dy (3 * L) L σ μ η E₀).originalKernel (O.proximal p.1).kernel).measurable] at h
  rcases p with ⟨c, z⟩
  rw [F.proximalSolverProgram_apply]
  refine ⟨(integrable_map_measure costValue_measurable.aestronglyMeasurable
    (costedMap_measurable measurable_prodMk_left).aemeasurable).mpr h.1, ?_⟩
  rw [integral_map (costedMap_measurable measurable_prodMk_left).aemeasurable costValue_measurable.aestronglyMeasurable]
  exact h.2

theorem proximalSolverProgram_random_cost (O : FreshOracle F σ) (η E₀ : ℝ)
    (ν : Measure (Euclid dx × Joint dx dy)) [IsProbabilityMeasure ν] :
    Integrable costValue ((proximalSolverProgram dx dy L σ μ η E₀).originalKernel O.kernel ∘ₘ ν) ∧
    (∫ t, costValue t ∂(proximalSolverProgram dx dy L σ μ η E₀).originalKernel O.kernel ∘ₘ ν) =
      scscSolverWork (3 * L) L σ μ η E₀ := by
  rw [OracleProgram.originalKernel_eq_law]
  have h (p : Euclid dx × Joint dx dy) := F.proximalSolverProgram_cost O η E₀ p
  simp only [OracleProgram.originalKernel_eq_law] at h
  have hi := (kernel_moment_from_envelope _ ν costValue costValue_measurable.stronglyMeasurable
    (fun t => Nat.cast_nonneg t.2) _ (integrable_const _) (fun p => (h p).1) (fun p => (h p).2.le)).1
  refine ⟨hi, ?_⟩
  rw [Measure.comp_eq_comp_const_apply] at hi ⊢
  rw [Kernel.integral_comp hi, Kernel.const_apply]
  simp_rw [(h _).2]
  simp only [integral_const, measureReal_univ_eq_one, one_smul]

theorem proximalSolverProgram_calls_rate (O : FreshOracle F σ) {η E₀ : ℝ} (hη : 0 < η) (hE : 0 ≤ E₀)
    (ν : Measure (Euclid dx × Joint dx dy)) [IsProbabilityMeasure ν] :
    (∫ t, costValue t ∂(proximalSolverProgram dx dy L σ μ η E₀).originalKernel O.kernel ∘ₘ ν) ≤
      10 ^ 110 * valueLogFactor (3 * L) σ μ η ^ 8 *
        (Real.sqrt ((3 * L) / μ) * Real.log (2 + ((3 * L) / μ) * E₀ / η) + σ ^ 2 / (μ * η)) := by
  rw [(F.proximalSolverProgram_random_cost O η E₀ ν).2]
  have hL := F.L_pos
  have hμL : μ ≤ 3 * L := by have := F.μ_le_L; linarith
  exact scscSolverWork_rate F.μ_pos hμL F.L_pos (by linarith) hη hE

theorem proximalSolverProgram_fixed_accuracy (O : FreshOracle F σ) (c : Euclid dx) {η E₀ : ℝ} (hη : 0 < η)
    (ν : Measure (Joint dx dy)) [IsProbabilityMeasure ν]
    (hi : Integrable (F.proximalObjective c).saddleStartEnergy ν)
    (hb : (∫ z, (F.proximalObjective c).saddleStartEnergy z ∂ν) ≤ E₀) :
    Integrable (fun t : (Euclid dx × Joint dx dy) × ℕ => (F.proximalObjective c).gap t.1.2.1 t.1.2.2)
      ((proximalSolverProgram dx dy L σ μ η E₀).originalKernel O.kernel ∘ₘ ν.map (fun z => (c, z))) ∧
    (∫ t, (F.proximalObjective c).gap t.1.2.1 t.1.2.2
      ∂(proximalSolverProgram dx dy L σ μ η E₀).originalKernel O.kernel ∘ₘ ν.map (fun z => (c, z))) ≤ η := by
  have hL := F.L_pos
  have h := (F.proximalObjective c).scscSolverProgram_original_gap (O.proximal c)
    (by linarith) (by linarith) hη ν hi hb
  have hm : StronglyMeasurable (fun t : (Euclid dx × Joint dx dy) × ℕ => (F.proximalObjective c).gap t.1.2.1 t.1.2.2) :=
    ((F.proximalObjective c).jointGap_continuous.comp continuous_fst.snd).stronglyMeasurable
  rw [F.proximalSolverProgram_fixed_law]
  refine ⟨(integrable_map_measure hm.aestronglyMeasurable
    (costedMap_measurable measurable_prodMk_left).aemeasurable).mpr h.1, ?_⟩
  rw [integral_map (costedMap_measurable measurable_prodMk_left).aemeasurable hm.aestronglyMeasurable]
  exact h.2

end NCObjective
end FreshGradientMinimax
