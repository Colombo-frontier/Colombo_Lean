import FreshGradientMinimax.EpochParameters
import FreshGradientMinimax.RandomInput

/-! Jointly measurable accelerated phases, retaining the frozen reference.
The resulting law supports random starting data controlled only in mean. -/

set_option autoImplicit false
set_option maxHeartbeats 2200000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory

abbrev EpochState (dx dy : ℕ) := Euclid dx × Joint dy dy

def referenceAccelerationUpdate {dx dy : ℕ} (a m H : ℝ)
    (z : EpochState dx dy × Euclid dy) : EpochState dx dy :=
  (z.1.1, accelerationUpdate a m H (z.1.2, z.2))

theorem referenceAccelerationUpdate_continuous {dx dy : ℕ} (a m H : ℝ) :
    Continuous (referenceAccelerationUpdate (dx := dx) (dy := dy) a m H) :=
  continuous_fst.fst.prodMk ((accelerationUpdate_continuous a m H).comp
    (continuous_fst.snd.prodMk continuous_snd))

namespace SCObjective
variable {dx dy : ℕ} {ℓ μ α σ : ℝ} (S : SCObjective dx dy ℓ μ α)

def jointEpochStepKernel (O : FreshOracle S.toNCObjective σ) (ρ m H e : ℝ)
    (r : Euclid dy → Euclid dy) (hr : Measurable r) (b : ℕ) : Kernel (EpochState dx dy) (EpochState dx dy) :=
  (Kernel.id ×ₖ (S.jointBatchedEstimatorKernel O ρ m e r hr b).comap
    (fun z : EpochState dx dy => (z.1, accelerationQuery (Real.sqrt (m / H)) z.2))
    (measurable_fst.prodMk ((accelerationQuery_continuous _).measurable.comp measurable_snd))).map
    (referenceAccelerationUpdate (Real.sqrt (m / H)) m H)

instance jointEpochStepKernel_markov (O : FreshOracle S.toNCObjective σ) (ρ m H e : ℝ)
    (r : Euclid dy → Euclid dy) (hr : Measurable r) (b : ℕ) :
    IsMarkovKernel (S.jointEpochStepKernel O ρ m H e r hr b) :=
  Kernel.IsMarkovKernel.map _ (referenceAccelerationUpdate_continuous _ _ _).measurable

theorem jointEpochStepKernel_apply (O : FreshOracle S.toNCObjective σ) (ρ m H e : ℝ)
    (r : Euclid dy → Euclid dy) (hr : Measurable r) (b : ℕ) (u : Euclid dx) (s : Joint dy dy) :
    S.jointEpochStepKernel O ρ m H e r hr b (u, s) =
      (S.jointBatchedEstimatorKernel O ρ m e r hr b (u, accelerationQuery (Real.sqrt (m / H)) s)).map
        (fun w => (u, accelerationUpdate (Real.sqrt (m / H)) m H (s, w))) := by
  rw [jointEpochStepKernel, Kernel.map_apply _ (referenceAccelerationUpdate_continuous _ _ _).measurable,
    Kernel.prod_apply, Kernel.id_apply, Kernel.comap_apply, Measure.dirac_prod,
    Measure.map_map (referenceAccelerationUpdate_continuous _ _ _).measurable measurable_prodMk_left]
  rfl

theorem jointEpochStepKernel_fixed (O : FreshOracle S.toNCObjective σ) (ρ m H e : ℝ)
    (r : Euclid dy → Euclid dy) (hr : Measurable r) (b : ℕ) (u : Euclid dx) :
    (S.jointEpochStepKernel O ρ m H e r hr b).comap (fun s => (u, s)) (measurable_const.prodMk measurable_id) =
      (S.epochStepKernel O ρ m H e r hr b u).map (fun s => (u, s)) := by
  apply Kernel.ext
  intro s
  rw [Kernel.comap_apply, S.jointEpochStepKernel_apply,
    Kernel.map_apply (f := fun s : Joint dy dy => (u, s)) _ (measurable_const.prodMk measurable_id),
    epochStepKernel, accelerationStepKernel_apply,
    Measure.map_map (f := fun w => accelerationUpdate (Real.sqrt (m / H)) m H (s, w))
      (g := fun t : Joint dy dy => (u, t)) (measurable_const.prodMk measurable_id)
      ((accelerationUpdate_continuous _ _ _).comp (continuous_const.prodMk continuous_id)).measurable]
  rfl

def jointEpochRunKernel (O : FreshOracle S.toNCObjective σ) (ρ m H e : ℝ)
    (r : Euclid dy → Euclid dy) (hr : Measurable r) (b n : ℕ) : Kernel (EpochState dx dy) (EpochState dx dy) :=
  iterateKernel (S.jointEpochStepKernel O ρ m H e r hr b) n

instance jointEpochRunKernel_markov (O : FreshOracle S.toNCObjective σ) (ρ m H e : ℝ)
    (r : Euclid dy → Euclid dy) (hr : Measurable r) (b n : ℕ) :
    IsMarkovKernel (S.jointEpochRunKernel O ρ m H e r hr b n) := by unfold jointEpochRunKernel; infer_instance

theorem jointEpochRunKernel_fixed (O : FreshOracle S.toNCObjective σ) (ρ m H e : ℝ)
    (r : Euclid dy → Euclid dy) (hr : Measurable r) (b n : ℕ) (u : Euclid dx) :
    (S.jointEpochRunKernel O ρ m H e r hr b n).comap (fun s => (u, s)) (measurable_const.prodMk measurable_id) =
      (S.epochAcceleratedKernel O ρ m H e r hr b u n).map (fun s => (u, s)) :=
  iterateKernel_transport _ _ _ _ (S.jointEpochStepKernel_fixed O ρ m H e r hr b u) n

def epochPhaseStateKernel (O : FreshOracle S.toNCObjective σ) (m H e E : ℝ)
    (r : Euclid dy → Euclid dy) (hr : Measurable r) : Kernel (Joint dx dy) (EpochState dx dy) :=
  (S.jointEpochRunKernel O epochRho m H e r hr (epochBatch m H e σ E) (epochSteps m H)).comap
    (fun z : Joint dx dy => (z.1, (z.2, z.2))) (measurable_fst.prodMk (measurable_snd.prodMk measurable_snd))

instance epochPhaseStateKernel_markov (O : FreshOracle S.toNCObjective σ) (m H e E : ℝ)
    (r : Euclid dy → Euclid dy) (hr : Measurable r) :
    IsMarkovKernel (S.epochPhaseStateKernel O m H e E r hr) := by unfold epochPhaseStateKernel; infer_instance

theorem epochPhaseStateKernel_apply (O : FreshOracle S.toNCObjective σ) (m H e E : ℝ)
    (r : Euclid dy → Euclid dy) (hr : Measurable r) (u : Euclid dx) (x : Euclid dy) :
    S.epochPhaseStateKernel O m H e E r hr (u, x) =
      (S.epochAcceleratedKernel O epochRho m H e r hr (epochBatch m H e σ E) u (epochSteps m H) (x, x)).map
        (fun s => (u, s)) := by
  have h := congrArg (fun K : Kernel (Joint dy dy) (EpochState dx dy) => K (x, x))
    (S.jointEpochRunKernel_fixed O epochRho m H e r hr (epochBatch m H e σ E) (epochSteps m H) u)
  simpa only [epochPhaseStateKernel, Kernel.comap_apply,
    Kernel.map_apply (f := fun s : Joint dy dy => (u, s)) _ (measurable_const.prodMk measurable_id)] using h

theorem epochPhaseStateKernel_contract (O : FreshOracle S.toNCObjective σ)
    (hαℓ : α ≤ ℓ) (hfast : ℓ / 4 ≤ α) {m H e E : ℝ}
    (hm : 0 < m) (hmH : m ≤ H) (he : 0 < e) (heE : e ≤ E)
    (r : Euclid dy → Euclid dy) (hr : Measurable r) {Q : Euclid dy → ℝ}
    (model : SmoothStrongModel Q (fun v => gradient S.effectiveValue v + r v) m H)
    (v : Euclid dy) (hmin : ∀ t, Q v ≤ Q t) (z : Joint dx dy) :
    Integrable (fun t : EpochState dx dy => statePotential Q m v t.2) (S.epochPhaseStateKernel O m H e E r hr z) ∧
    (∫ t, statePotential Q m v t.2 ∂S.epochPhaseStateKernel O m H e E r hr z) ≤
      (Q z.2 - Q v + m * ‖z.1 - S.sliceMin v‖ ^ 2) / (1000000 * 17) + E / (1000000 * 17) := by
  rcases z with ⟨u, x⟩
  rw [S.epochPhaseStateKernel_apply]
  have hPot := ((statePotential_continuous model.continuous m v).comp
    (continuous_snd : Continuous (Prod.snd : EpochState dx dy → Joint dy dy))).stronglyMeasurable
  constructor
  · apply (integrable_map_measure (g := fun t : EpochState dx dy => statePotential Q m v t.2)
      hPot.aestronglyMeasurable (measurable_const.prodMk measurable_id).aemeasurable).mpr
    exact (S.epochAcceleratedKernel_contract O hαℓ hfast epochRho_pos epochRho_small hm hmH he
      r hr model v hmin (epochBatch_pos m H e σ E) u (epochSteps m H) (x, x)).1
  · rw [integral_map (f := fun t : EpochState dx dy => statePotential Q m v t.2)
      (φ := fun s : Joint dy dy => (u, s)) (measurable_const.prodMk measurable_id).aemeasurable hPot.aestronglyMeasurable]
    exact S.epochAcceleratedKernel_selected_bound O hαℓ hfast hm hmH he heE r hr model v hmin u x

/-- Equation (50) with only an expected starting energy; no radius bound. -/
theorem epochPhaseStateKernel_random_accuracy (O : FreshOracle S.toNCObjective σ)
    (hαℓ : α ≤ ℓ) (hfast : ℓ / 4 ≤ α) {m H e E : ℝ}
    (hm : 0 < m) (hmH : m ≤ H) (he : 0 < e) (heE : e ≤ E)
    (r : Euclid dy → Euclid dy) (hr : Measurable r) {Q : Euclid dy → ℝ}
    (model : SmoothStrongModel Q (fun v => gradient S.effectiveValue v + r v) m H)
    (v : Euclid dy) (hmin : ∀ t, Q v ≤ Q t) (ν : Measure (Joint dx dy)) [IsProbabilityMeasure ν]
    (hInit : Integrable (fun z : Joint dx dy => Q z.2 - Q v + m * ‖z.1 - S.sliceMin v‖ ^ 2) ν)
    (hEnergy : (∫ z, Q z.2 - Q v + m * ‖z.1 - S.sliceMin v‖ ^ 2 ∂ν) ≤ E) :
    Integrable (fun t : EpochState dx dy => statePotential Q m v t.2)
      (S.epochPhaseStateKernel O m H e E r hr ∘ₘ ν) ∧
    (∫ t, statePotential Q m v t.2 ∂S.epochPhaseStateKernel O m H e E r hr ∘ₘ ν) ≤ E / (100000 * 17) := by
  have hW := (hInit.div_const (1000000 * 17)).add (integrable_const (E / (1000000 * 17)))
  obtain ⟨hi, hb⟩ := kernel_moment_from_envelope (S.epochPhaseStateKernel O m H e E r hr) ν
    (fun t : EpochState dx dy => statePotential Q m v t.2)
    (((statePotential_continuous model.continuous m v).comp continuous_snd).stronglyMeasurable)
    (fun t => SmoothStrongModel.potential_nonneg hm.le v hmin t.2.1 t.2.2) _ hW
    (fun z => (S.epochPhaseStateKernel_contract O hαℓ hfast hm hmH he heE r hr model v hmin z).1)
    (fun z => (S.epochPhaseStateKernel_contract O hαℓ hfast hm hmH he heE r hr model v hmin z).2)
  refine ⟨hi, ?_⟩
  simp only [Pi.add_apply] at hb
  rw [integral_add (hInit.div_const (1000000 * 17)) (integrable_const (E / (1000000 * 17))), integral_div,
    integral_const, measureReal_univ_eq_one, one_smul] at hb
  have hE := he.trans_le heE
  linarith

end SCObjective
end FreshGradientMinimax
