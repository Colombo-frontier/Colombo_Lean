import FreshGradientMinimax.RecursiveGap
import FreshGradientMinimax.RecursiveCost

/-! The complete SCSC solver from an arbitrary random starting point.
It only uses numerical parameters and original fresh-gradient queries.
Its true saddle gap and its actual expected call count are verified;
the asymptotic logarithmic bound on the finite cost sum is separate. -/

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory
open scoped BigOperators

def scscGradientTolerance (μ η : ℝ) : ℝ := Real.sqrt (μ * η / 100)

def scscSolverProgram (dx dy : ℕ) (ℓ α σ μ η E₀ : ℝ) : OracleProgram dx dy (Joint dx dy) (Joint dx dy) :=
  ((recursiveSolverProgram dx dy ℓ α σ μ (scscGradientTolerance μ η)
    (recursiveLastIndex (5 * ℓ) μ) (3 * (ℓ / μ) * E₀)).precompose
      (fun z => ((0 : Euclid dy), z)) measurable_prodMk_left).map Prod.snd measurable_snd

def scscSolverWork (ℓ α σ μ η E₀ : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (recursiveLastIndex (5 * ℓ) μ + 1),
    recursiveStageWork ℓ α σ μ (scscGradientTolerance μ η) (recursiveLastIndex (5 * ℓ) μ) (3 * (ℓ / μ) * E₀) j

theorem scscSolverProgram_result_law (dx dy : ℕ) (ℓ α σ μ η E₀ : ℝ)
    (K : Kernel (Joint dx dy) (Joint dx dy)) (ν : Measure (Joint dx dy)) :
    (scscSolverProgram dx dy ℓ α σ μ η E₀).resultKernel K ∘ₘ ν =
    (((recursiveSolverProgram dx dy ℓ α σ μ (scscGradientTolerance μ η)
      (recursiveLastIndex (5 * ℓ) μ) (3 * (ℓ / μ) * E₀)).resultKernel K) ∘ₘ
      ν.map (fun z => ((0 : Euclid dy), z))).map Prod.snd := by
  rw [scscSolverProgram, OracleProgram.map_result, OracleProgram.precompose_result,
    ← Measure.map_comp _ _ measurable_snd, comap_comp_measure]

theorem scscSolverProgram_original_law (dx dy : ℕ) (ℓ α σ μ η E₀ : ℝ)
    (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K] (ν : Measure (Joint dx dy)) :
    (scscSolverProgram dx dy ℓ α σ μ η E₀).originalKernel K ∘ₘ ν =
    (((recursiveSolverProgram dx dy ℓ α σ μ (scscGradientTolerance μ η)
      (recursiveLastIndex (5 * ℓ) μ) (3 * (ℓ / μ) * E₀)).originalKernel K) ∘ₘ
      ν.map (fun z => ((0 : Euclid dy), z))).map (costedMap Prod.snd) := by
  rw [OracleProgram.originalKernel_eq_law, OracleProgram.originalKernel_eq_law,
    scscSolverProgram, OracleProgram.map_law, OracleProgram.precompose_law,
    ← Measure.map_comp (f := fun z : (Euclid dy × Joint dx dy) × ℕ => (z.1.2, z.2)) _ _
      (measurable_fst.snd.prodMk measurable_snd), comap_comp_measure]
  rfl

namespace SCObjective
variable {dx dy : ℕ} {ℓ μ α σ : ℝ} (S : SCObjective dx dy ℓ μ α)

theorem scscSolverProgram_gap (O : FreshOracle S.toNCObjective σ)
    (hαℓ : α ≤ ℓ) (hfast : ℓ / 4 ≤ α) {η E₀ : ℝ} (hη : 0 < η)
    (ν : Measure (Joint dx dy)) [IsProbabilityMeasure ν]
    (hi : Integrable S.saddleStartEnergy ν) (hb : (∫ z, S.saddleStartEnergy z ∂ν) ≤ E₀) :
    Integrable (fun z : Joint dx dy => S.gap z.1 z.2)
      ((scscSolverProgram dx dy ℓ α σ μ η E₀).resultKernel O.kernel ∘ₘ ν) ∧
    (∫ z, S.gap z.1 z.2 ∂(scscSolverProgram dx dy ℓ α σ μ η E₀).resultKernel O.kernel ∘ₘ ν) ≤ η := by
  have hδ : 0 < scscGradientTolerance μ η := Real.sqrt_pos.mpr (by have := S.μ_pos; positivity)
  have hμL : μ ≤ 5 * ℓ := by have := S.μ_le_L; have := S.L_pos; linarith
  have hscale := (recursiveLastIndex_mass S.μ_pos hμL).1
  let ν₀ := ν.map (fun z => ((0 : Euclid dy), z))
  letI : IsProbabilityMeasure ν₀ := isProbabilityMeasure_map measurable_prodMk_left.aemeasurable
  have hzero : ∀ᵐ z ∂ν₀, z.1 = 0 := by
    apply (ae_map_iff measurable_prodMk_left.aemeasurable
      (measurableSet_eq_fun measurable_fst measurable_const)).mpr
    exact Filter.Eventually.of_forall (fun _ => rfl)
  obtain ⟨hei, heb⟩ := S.recursive_cold_energy_mean hfast ν hi hb
  obtain ⟨hgi, hgb⟩ := S.recursiveSolverProgram_gap O hαℓ hfast hδ _ _ hscale ν₀ hei heb hzero
  rw [scscSolverProgram_result_law]
  refine ⟨(integrable_map_measure S.jointGap_continuous.stronglyMeasurable.aestronglyMeasurable
    measurable_snd.aemeasurable).mpr hgi, ?_⟩
  rw [integral_map measurable_snd.aemeasurable S.jointGap_continuous.stronglyMeasurable.aestronglyMeasurable]
  apply hgb.trans
  apply (div_le_iff₀ S.μ_pos).mpr
  rw [scscGradientTolerance, Real.sq_sqrt (by have := S.μ_pos; positivity)]
  nlinarith [mul_pos S.μ_pos hη]

theorem scscSolverProgram_original_gap (O : FreshOracle S.toNCObjective σ)
    (hαℓ : α ≤ ℓ) (hfast : ℓ / 4 ≤ α) {η E₀ : ℝ} (hη : 0 < η)
    (ν : Measure (Joint dx dy)) [IsProbabilityMeasure ν]
    (hi : Integrable S.saddleStartEnergy ν) (hb : (∫ z, S.saddleStartEnergy z ∂ν) ≤ E₀) :
    Integrable (fun t : Joint dx dy × ℕ => S.gap t.1.1 t.1.2)
      ((scscSolverProgram dx dy ℓ α σ μ η E₀).originalKernel O.kernel ∘ₘ ν) ∧
    (∫ t, S.gap t.1.1 t.1.2 ∂(scscSolverProgram dx dy ℓ α σ μ η E₀).originalKernel O.kernel ∘ₘ ν) ≤ η := by
  have h := S.scscSolverProgram_gap O hαℓ hfast hη ν hi hb
  rw [← OracleProgram.original_result_law] at h
  refine ⟨(integrable_map_measure S.jointGap_continuous.stronglyMeasurable.aestronglyMeasurable
    measurable_fst.aemeasurable).mp h.1, ?_⟩
  rw [integral_map measurable_fst.aemeasurable S.jointGap_continuous.stronglyMeasurable.aestronglyMeasurable] at h
  exact h.2

theorem scscSolverProgram_mean_calls (O : FreshOracle S.toNCObjective σ) (η E₀ : ℝ)
    (ν : Measure (Joint dx dy)) [IsProbabilityMeasure ν] :
    Integrable costValue ((scscSolverProgram dx dy ℓ α σ μ η E₀).originalKernel O.kernel ∘ₘ ν) ∧
    (∫ t, costValue t ∂(scscSolverProgram dx dy ℓ α σ μ η E₀).originalKernel O.kernel ∘ₘ ν) = scscSolverWork ℓ α σ μ η E₀ := by
  let ν₀ := ν.map (fun z => ((0 : Euclid dy), z))
  letI : IsProbabilityMeasure ν₀ := isProbabilityMeasure_map measurable_prodMk_left.aemeasurable
  have h := S.recursiveSolverProgram_mean_calls O (scscGradientTolerance μ η)
    (recursiveLastIndex (5 * ℓ) μ) (3 * (ℓ / μ) * E₀) ν₀
  rw [scscSolverProgram_original_law]
  refine ⟨(integrable_map_measure costValue_measurable.aestronglyMeasurable
    (costedMap_measurable measurable_snd).aemeasurable).mpr h.1, ?_⟩
  rw [integral_map (costedMap_measurable measurable_snd).aemeasurable costValue_measurable.aestronglyMeasurable]
  exact h.2

end SCObjective
end FreshGradientMinimax
