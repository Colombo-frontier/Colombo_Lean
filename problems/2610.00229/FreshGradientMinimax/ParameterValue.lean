import FreshGradientMinimax.ParameterEpoch
import FreshGradientMinimax.ValueProgram

/-! The complete value solver with a continuously varying known
regularizer. The single program is jointly measurable in its parameter
and initial state; its true call count has the same uniform mean bound. -/

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory
variable {dx dy : ℕ} {Θ : Type} [MeasurableSpace Θ]

def parameterValueRunProgram (dx dy : ℕ) (ℓ α σ m H e E₀ : ℝ)
    (r : Θ × Euclid dy → Euclid dy) (hr : Measurable r) :
    ℕ → OracleProgram dx dy (Θ × Joint dx dy) (Θ × Joint dx dy)
  | 0 => OracleProgram.pure id measurable_id
  | n + 1 => (parameterValueRunProgram dx dy ℓ α σ m H e E₀ r hr n).chain
      (parameterFullEpochProgram dx dy ℓ α σ m H e (valueEnvelope E₀ e n) r hr)

def parameterValueSolverProgram (dx dy : ℕ) (ℓ α σ m H e E₀ : ℝ)
    (r : Θ × Euclid dy → Euclid dy) (hr : Measurable r) :
    OracleProgram dx dy (Θ × Joint dx dy) (Θ × Joint dx dy) :=
  parameterValueRunProgram dx dy ℓ α σ m H e E₀ r hr (finalEpochIndex E₀ e + 1)

namespace SCObjective
variable {ℓ μ α σ : ℝ} (S : SCObjective dx dy ℓ μ α)

theorem parameterValueRunProgram_fiber (O : FreshOracle S.toNCObjective σ) (m H e E₀ : ℝ)
    (r : Θ × Euclid dy → Euclid dy) (hr : Measurable r) (θ : Θ) (n : ℕ) :
    ((parameterValueRunProgram dx dy ℓ α σ m H e E₀ r hr n).lawKernel O.kernel).comap
        (fun x => (θ, x)) measurable_prodMk_left =
      (S.costedValueRunKernel O m H e E₀ (fun v => r (θ, v)) (hr.comp measurable_prodMk_left) n).map
        (costedMap (fun x => (θ, x))) := by
  induction n with
  | zero =>
    rw [parameterValueRunProgram, OracleProgram.pure_law]
    apply Kernel.ext
    intro x
    change (taggedKernel Kernel.id 0) (θ, x) =
      ((taggedKernel (Kernel.id : Kernel (Joint dx dy) _) 0).map (costedMap (fun y => (θ, y)))) x
    rw [Kernel.map_apply _ (costedMap_measurable measurable_prodMk_left)]
    simp only [taggedKernel]
    rw [Kernel.map_apply (f := fun y : Θ × Joint dx dy => (y, (0 : ℕ))) _ (measurable_id.prodMk measurable_const),
      Kernel.map_apply (f := fun y : Joint dx dy => (y, (0 : ℕ))) _ (measurable_id.prodMk measurable_const)]
    simp only [Kernel.id_apply]
    rw [Measure.map_dirac (show Measurable (fun y : Θ × Joint dx dy => (y, (0 : ℕ))) from
      measurable_id.prodMk measurable_const),
      Measure.map_dirac (show Measurable (fun y : Joint dx dy => (y, (0 : ℕ))) from
      measurable_id.prodMk measurable_const),
      Measure.map_dirac (costedMap_measurable (measurable_prodMk_left (x := θ)))]
    rfl
  | succ n ih =>
    rw [parameterValueRunProgram, OracleProgram.chain_law, costedValueRunKernel]
    exact costedCompose_transport _ _ _ _ _ measurable_prodMk_left _ measurable_prodMk_left
      _ measurable_prodMk_left ih (S.parameterFullEpochProgram_fiber O m H e _ r hr θ)

theorem parameterValueSolverProgram_fiber (O : FreshOracle S.toNCObjective σ) (m H e E₀ : ℝ)
    (r : Θ × Euclid dy → Euclid dy) (hr : Measurable r) (θ : Θ) :
    ((parameterValueSolverProgram dx dy ℓ α σ m H e E₀ r hr).lawKernel O.kernel).comap
        (fun x => (θ, x)) measurable_prodMk_left =
      (S.costedValueSolverKernel O m H e E₀ (fun v => r (θ, v)) (hr.comp measurable_prodMk_left)).map
        (costedMap (fun x => (θ, x))) :=
  S.parameterValueRunProgram_fiber O m H e E₀ r hr θ _

theorem parameterValueSolverProgram_original (O : FreshOracle S.toNCObjective σ) (m H e E₀ : ℝ)
    (r : Θ × Euclid dy → Euclid dy) (hr : Measurable r) (θ : Θ) (z : Joint dx dy) :
    (parameterValueSolverProgram dx dy ℓ α σ m H e E₀ r hr).originalKernel O.kernel (θ, z) =
      (S.costedValueSolverKernel O m H e E₀ (fun v => r (θ, v)) (hr.comp measurable_prodMk_left) z).map
        (costedMap (fun x => (θ, x))) := by
  have h := congrArg (fun L : Kernel (Joint dx dy) ((Θ × Joint dx dy) × ℕ) => L z)
    (S.parameterValueSolverProgram_fiber O m H e E₀ r hr θ)
  dsimp only at h
  rw [Kernel.comap_apply, Kernel.map_apply _ (costedMap_measurable measurable_prodMk_left)] at h
  rw [OracleProgram.originalKernel_eq_law]
  exact h

theorem parameterValueSolverProgram_cost (O : FreshOracle S.toNCObjective σ) (m H e E₀ : ℝ)
    (r : Θ × Euclid dy → Euclid dy) (hr : Measurable r) (z : Θ × Joint dx dy) :
    Integrable costValue ((parameterValueSolverProgram dx dy ℓ α σ m H e E₀ r hr).originalKernel O.kernel z) ∧
    (∫ t, costValue t ∂(parameterValueSolverProgram dx dy ℓ α σ m H e E₀ r hr).originalKernel O.kernel z) =
      valueSolverWork ℓ α σ m H e E₀ := by
  rw [S.parameterValueSolverProgram_original O m H e E₀ r hr z.1 z.2]
  have h := S.costedValueSolverKernel_cost O m H e E₀ (fun v => r (z.1, v)) (hr.comp measurable_prodMk_left) z.2
  constructor
  · exact (integrable_map_measure (g := costValue) costValue_measurable.aestronglyMeasurable
      (costedMap_measurable (measurable_prodMk_left (x := z.1))).aemeasurable).mpr h.1
  · rw [integral_map (φ := costedMap (fun x => (z.1, x)))
      (costedMap_measurable measurable_prodMk_left).aemeasurable costValue_measurable.aestronglyMeasurable]
    exact h.2

theorem parameterValueSolverProgram_random_cost (O : FreshOracle S.toNCObjective σ) (m H e E₀ : ℝ)
    (r : Θ × Euclid dy → Euclid dy) (hr : Measurable r)
    (ν : Measure (Θ × Joint dx dy)) [IsProbabilityMeasure ν] :
    Integrable costValue ((parameterValueSolverProgram dx dy ℓ α σ m H e E₀ r hr).originalKernel O.kernel ∘ₘ ν) ∧
    (∫ t, costValue t ∂(parameterValueSolverProgram dx dy ℓ α σ m H e E₀ r hr).originalKernel O.kernel ∘ₘ ν) =
      valueSolverWork ℓ α σ m H e E₀ := by
  have h (z : Θ × Joint dx dy) := S.parameterValueSolverProgram_cost O m H e E₀ r hr z
  have hi := (kernel_moment_from_envelope
    ((parameterValueSolverProgram dx dy ℓ α σ m H e E₀ r hr).lawKernel O.kernel) ν costValue
    costValue_measurable.stronglyMeasurable (fun t => Nat.cast_nonneg t.2)
    (fun _ => valueSolverWork ℓ α σ m H e E₀) (integrable_const _)
    (fun z => by rw [← OracleProgram.originalKernel_eq_law]; exact (h z).1)
    (fun z => by rw [← OracleProgram.originalKernel_eq_law]; exact (h z).2.le)).1
  rw [← OracleProgram.originalKernel_eq_law] at hi
  refine ⟨hi, ?_⟩
  rw [OracleProgram.originalKernel_eq_law] at hi ⊢
  rw [Measure.comp_eq_comp_const_apply] at hi ⊢
  rw [Kernel.integral_comp hi, Kernel.const_apply]
  simp_rw [← OracleProgram.originalKernel_eq_law, (h _).2]
  simp only [integral_const, measureReal_univ_eq_one, one_smul]

theorem parameterValueSolverProgram_calls_rate (O : FreshOracle S.toNCObjective σ)
    (hfast : ℓ / 4 ≤ α) {m H e E₀ : ℝ} (hm : 0 < m) (hmH : m ≤ H) (hHℓ : H ≤ 20 * ℓ)
    (he : 0 < e) (hE₀ : 0 ≤ E₀) (r : Θ × Euclid dy → Euclid dy) (hr : Measurable r)
    (ν : Measure (Θ × Joint dx dy)) [IsProbabilityMeasure ν] :
    (∫ t, costValue t ∂(parameterValueSolverProgram dx dy ℓ α σ m H e E₀ r hr).originalKernel O.kernel ∘ₘ ν) ≤
      10 ^ 70 * valueLogFactor ℓ σ m e ^ 3 *
        (Real.sqrt (H / m) * Real.log (2 + E₀ / e) + σ ^ 2 / (m * e)) := by
  rw [(S.parameterValueSolverProgram_random_cost O m H e E₀ r hr ν).2]
  exact valueSolverWork_rate S.L_pos S.α_pos hfast hm hmH hHℓ he hE₀

end SCObjective
end FreshGradientMinimax
