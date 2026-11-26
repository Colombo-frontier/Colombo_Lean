import FreshGradientMinimax.FullEpoch
import FreshGradientMinimax.EpochSchedule

/-! The actual finite sequence of complete epochs, with unconditional value
and fast-variable accuracy. ValueProgram connects cost to original calls;
ParameterAccuracy handles random known regularizers with a fixed base
objective. Random base objectives remain a separate obligation. -/

set_option autoImplicit false
set_option maxHeartbeats 2200000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory
namespace SCObjective
variable {dx dy : ℕ} {ℓ μ α σ : ℝ} (S : SCObjective dx dy ℓ μ α)

def valueRunKernel (O : FreshOracle S.toNCObjective σ) (m H e E₀ : ℝ)
    (r : Euclid dy → Euclid dy) (hr : Measurable r) : ℕ → Kernel (Joint dx dy) (Joint dx dy)
  | 0 => Kernel.id
  | n + 1 => S.fullEpochKernel O m H e (valueEnvelope E₀ e n) r hr ∘ₖ valueRunKernel O m H e E₀ r hr n

instance valueRunKernel_markov (O : FreshOracle S.toNCObjective σ) (m H e E₀ : ℝ)
    (r : Euclid dy → Euclid dy) (hr : Measurable r) (n : ℕ) :
    IsMarkovKernel (S.valueRunKernel O m H e E₀ r hr n) := by
  induction n with
  | zero => dsimp [valueRunKernel]; infer_instance
  | succ n ih =>
    letI := ih
    change IsMarkovKernel (S.fullEpochKernel O m H e (valueEnvelope E₀ e n) r hr ∘ₖ _)
    infer_instance

def valueSolverKernel (O : FreshOracle S.toNCObjective σ) (m H e E₀ : ℝ)
    (r : Euclid dy → Euclid dy) (hr : Measurable r) : Kernel (Joint dx dy) (Joint dx dy) :=
  S.valueRunKernel O m H e E₀ r hr (finalEpochIndex E₀ e + 1)

instance valueSolverKernel_markov (O : FreshOracle S.toNCObjective σ) (m H e E₀ : ℝ)
    (r : Euclid dy → Euclid dy) (hr : Measurable r) :
    IsMarkovKernel (S.valueSolverKernel O m H e E₀ r hr) := by unfold valueSolverKernel; infer_instance

theorem valueRunKernel_contract (O : FreshOracle S.toNCObjective σ)
    (hαℓ : α ≤ ℓ) (hfast : ℓ / 4 ≤ α) {m H e E₀ : ℝ}
    (hm : 0 < m) (hmH : m ≤ H) (he : 0 < e)
    (r : Euclid dy → Euclid dy) (hr : Measurable r) {Q : Euclid dy → ℝ}
    (model : SmoothStrongModel Q (fun v => gradient S.effectiveValue v + r v) m H)
    (v : Euclid dy) (hmin : ∀ x, Q v ≤ Q x) (ν : Measure (Joint dx dy)) [IsProbabilityMeasure ν]
    (hInit : Integrable (S.solverEnergy Q m v) ν)
    (hEnergy : (∫ z, S.solverEnergy Q m v z ∂ν) ≤ E₀) (n : ℕ) :
    Integrable (S.solverEnergy Q m v) (S.valueRunKernel O m H e E₀ r hr n ∘ₘ ν) ∧
    (∫ z, S.solverEnergy Q m v z ∂S.valueRunKernel O m H e E₀ r hr n ∘ₘ ν) ≤ valueEnvelope E₀ e n := by
  induction n with
  | zero =>
    have heq : S.valueRunKernel O m H e E₀ r hr 0 ∘ₘ ν = ν := by
      change ν.bind Measure.dirac = ν
      exact Measure.bind_dirac
    rw [heq]
    exact ⟨hInit, hEnergy.trans (valueEnvelope_initial E₀ e)⟩
  | succ n ih =>
    rw [valueRunKernel, ← Measure.comp_assoc]
    obtain ⟨hi, hb⟩ := S.fullEpochKernel_random_accuracy O hαℓ hfast hm hmH he
      (valueEnvelope_ge E₀ e n) r hr model v hmin _ ih.1 ih.2
    refine ⟨hi, hb.trans ?_⟩
    have hp : 0 < valueEnvelope E₀ e n := he.trans_le (valueEnvelope_ge E₀ e n)
    exact (by linarith : valueEnvelope E₀ e n / 50000 ≤ valueEnvelope E₀ e n / 2).trans
      (valueEnvelope_half he n)

theorem valueSolverKernel_energy (O : FreshOracle S.toNCObjective σ)
    (hαℓ : α ≤ ℓ) (hfast : ℓ / 4 ≤ α) {m H e E₀ : ℝ}
    (hm : 0 < m) (hmH : m ≤ H) (he : 0 < e)
    (r : Euclid dy → Euclid dy) (hr : Measurable r) {Q : Euclid dy → ℝ}
    (model : SmoothStrongModel Q (fun v => gradient S.effectiveValue v + r v) m H)
    (v : Euclid dy) (hmin : ∀ x, Q v ≤ Q x) (ν : Measure (Joint dx dy)) [IsProbabilityMeasure ν]
    (hInit : Integrable (S.solverEnergy Q m v) ν)
    (hEnergy : (∫ z, S.solverEnergy Q m v z ∂ν) ≤ E₀) :
    Integrable (S.solverEnergy Q m v) (S.valueSolverKernel O m H e E₀ r hr ∘ₘ ν) ∧
    (∫ z, S.solverEnergy Q m v z ∂S.valueSolverKernel O m H e E₀ r hr ∘ₘ ν) ≤ e / 50000 := by
  obtain ⟨hi, hb⟩ := S.valueRunKernel_contract O hαℓ hfast hm hmH he r hr model v hmin ν hInit hEnergy
    (finalEpochIndex E₀ e)
  have h := S.fullEpochKernel_random_accuracy O hαℓ hfast hm hmH he
    (valueEnvelope_ge E₀ e (finalEpochIndex E₀ e)) r hr model v hmin _ hi hb
  rw [Measure.comp_assoc] at h
  simpa only [valueSolverKernel, valueRunKernel, valueEnvelope_final he] using h

theorem valueSolverKernel_accuracy (O : FreshOracle S.toNCObjective σ)
    (hαℓ : α ≤ ℓ) (hfast : ℓ / 4 ≤ α) {m H e E₀ : ℝ}
    (hm : 0 < m) (hmH : m ≤ H) (he : 0 < e)
    (r : Euclid dy → Euclid dy) (hr : Measurable r) {Q : Euclid dy → ℝ}
    (model : SmoothStrongModel Q (fun v => gradient S.effectiveValue v + r v) m H)
    (v : Euclid dy) (hmin : ∀ x, Q v ≤ Q x) (ν : Measure (Joint dx dy)) [IsProbabilityMeasure ν]
    (hInit : Integrable (S.solverEnergy Q m v) ν)
    (hEnergy : (∫ z, S.solverEnergy Q m v z ∂ν) ≤ E₀) :
    Integrable (fun z : Joint dx dy => Q z.2 - Q v) (S.valueSolverKernel O m H e E₀ r hr ∘ₘ ν) ∧
    Integrable (S.fastError m) (S.valueSolverKernel O m H e E₀ r hr ∘ₘ ν) ∧
    (∫ z, Q z.2 - Q v ∂S.valueSolverKernel O m H e E₀ r hr ∘ₘ ν) ≤ e ∧
    (∫ z, S.fastError m z ∂S.valueSolverKernel O m H e E₀ r hr ∘ₘ ν) ≤ e := by
  obtain ⟨hi, hb⟩ := S.valueSolverKernel_energy O hαℓ hfast hm hmH he r hr model v hmin ν hInit hEnergy
  have hgap : Integrable (fun z : Joint dx dy => Q z.2 - Q v) (S.valueSolverKernel O m H e E₀ r hr ∘ₘ ν) := by
    apply hi.mono' ((model.continuous.comp continuous_snd).sub continuous_const).aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro z
    change ‖Q z.2 - Q v‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (hmin z.2))]
    exact S.valueGap_le_solverEnergy hm.le v z
  have hfasti : Integrable (S.fastError m) (S.valueSolverKernel O m H e E₀ r hr ∘ₘ ν) := by
    apply (hi.const_mul 66).mono' (S.fastError_continuous m).aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro z
    rw [Real.norm_eq_abs, abs_of_nonneg (S.fastError_nonneg hm.le z)]
    exact S.fastError_le_solverEnergy model hm hfast v hmin z
  refine ⟨hgap, hfasti, ?_, ?_⟩
  · have h := integral_mono hgap hi (S.valueGap_le_solverEnergy hm.le v)
    linarith
  · have h := integral_mono hfasti (hi.const_mul 66) (S.fastError_le_solverEnergy model hm hfast v hmin)
    rw [integral_const_mul] at h
    linarith

end SCObjective
end FreshGradientMinimax
