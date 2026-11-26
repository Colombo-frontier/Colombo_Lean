import FreshGradientMinimax.ParameterEnergy

/-! Full value and fast-variable accuracy for random known regularizers.
All epochs retain the same parameter, which can be correlated with the
initial iterate. The initialization assumption bounds only a joint mean. -/

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory
namespace SCObjective
variable {dx dy : ℕ} {Θ : Type} [MeasurableSpace Θ]
variable {ℓ μ α σ : ℝ} (S : SCObjective dx dy ℓ μ α)

def parameterValueOutput (O : FreshOracle S.toNCObjective σ) (m H e E₀ : ℝ)
    (r : Θ × Euclid dy → Euclid dy) (hr : Measurable r) (n : ℕ) :
    Kernel (Θ × Joint dx dy) (Θ × Joint dx dy) :=
  ((parameterValueRunProgram dx dy ℓ α σ m H e E₀ r hr n).lawKernel O.kernel).map Prod.fst

instance parameterValueOutput_markov (O : FreshOracle S.toNCObjective σ) (m H e E₀ : ℝ)
    (r : Θ × Euclid dy → Euclid dy) (hr : Measurable r) (n : ℕ) :
    IsMarkovKernel (S.parameterValueOutput O m H e E₀ r hr n) :=
  Kernel.IsMarkovKernel.map _ measurable_fst

theorem parameterValueOutput_zero (O : FreshOracle S.toNCObjective σ) (m H e E₀ : ℝ)
    (r : Θ × Euclid dy → Euclid dy) (hr : Measurable r) :
    S.parameterValueOutput O m H e E₀ r hr 0 = Kernel.id := by
  rw [parameterValueOutput, parameterValueRunProgram, OracleProgram.pure_law, taggedKernel_first]
  rfl

theorem parameterValueOutput_succ (O : FreshOracle S.toNCObjective σ) (m H e E₀ : ℝ)
    (r : Θ × Euclid dy → Euclid dy) (hr : Measurable r) (n : ℕ) :
    S.parameterValueOutput O m H e E₀ r hr (n + 1) =
      S.parameterEpochOutput O m H e (valueEnvelope E₀ e n) r hr ∘ₖ
        S.parameterValueOutput O m H e E₀ r hr n := by
  rw [parameterValueOutput, parameterValueRunProgram, OracleProgram.chain_law, costedCompose_first]
  rfl

theorem parameterValueOutput_contract (O : FreshOracle S.toNCObjective σ)
    (hαℓ : α ≤ ℓ) (hfast : ℓ / 4 ≤ α) {m H e E₀ : ℝ}
    (hm : 0 < m) (hmH : m ≤ H) (he : 0 < e)
    (r : Θ × Euclid dy → Euclid dy) (hr : Measurable r)
    (Q : Θ × Euclid dy → ℝ) (hQ : Measurable Q)
    (model : ∀ θ, SmoothStrongModel (fun y => Q (θ, y)) (fun y => gradient S.effectiveValue y + r (θ, y)) m H)
    (v : Θ → Euclid dy) (hv : Measurable v) (hmin : ∀ θ y, Q (θ, v θ) ≤ Q (θ, y))
    (ν : Measure (Θ × Joint dx dy)) [IsProbabilityMeasure ν]
    (hInit : Integrable (S.parameterEnergy Q m v) ν)
    (hEnergy : (∫ z, S.parameterEnergy Q m v z ∂ν) ≤ E₀) (n : ℕ) :
    Integrable (S.parameterEnergy Q m v) (S.parameterValueOutput O m H e E₀ r hr n ∘ₘ ν) ∧
    (∫ z, S.parameterEnergy Q m v z ∂S.parameterValueOutput O m H e E₀ r hr n ∘ₘ ν) ≤ valueEnvelope E₀ e n := by
  induction n with
  | zero =>
    rw [S.parameterValueOutput_zero]
    have hid : (Kernel.id : Kernel (Θ × Joint dx dy) _) ∘ₘ ν = ν := Measure.bind_dirac
    rw [hid]
    exact ⟨hInit, hEnergy.trans (valueEnvelope_initial E₀ e)⟩
  | succ n ih =>
    rw [S.parameterValueOutput_succ, ← Measure.comp_assoc]
    obtain ⟨hi, hb⟩ := S.parameterEpochOutput_random_accuracy O hαℓ hfast hm hmH he
      (valueEnvelope_ge E₀ e n) r hr Q hQ model v hv hmin _ ih.1 ih.2
    refine ⟨hi, hb.trans ?_⟩
    have hp : 0 < valueEnvelope E₀ e n := he.trans_le (valueEnvelope_ge E₀ e n)
    exact (by linarith : valueEnvelope E₀ e n / 50000 ≤ valueEnvelope E₀ e n / 2).trans
      (valueEnvelope_half he n)

theorem parameterValueOutput_energy (O : FreshOracle S.toNCObjective σ)
    (hαℓ : α ≤ ℓ) (hfast : ℓ / 4 ≤ α) {m H e E₀ : ℝ}
    (hm : 0 < m) (hmH : m ≤ H) (he : 0 < e)
    (r : Θ × Euclid dy → Euclid dy) (hr : Measurable r)
    (Q : Θ × Euclid dy → ℝ) (hQ : Measurable Q)
    (model : ∀ θ, SmoothStrongModel (fun y => Q (θ, y)) (fun y => gradient S.effectiveValue y + r (θ, y)) m H)
    (v : Θ → Euclid dy) (hv : Measurable v) (hmin : ∀ θ y, Q (θ, v θ) ≤ Q (θ, y))
    (ν : Measure (Θ × Joint dx dy)) [IsProbabilityMeasure ν]
    (hInit : Integrable (S.parameterEnergy Q m v) ν)
    (hEnergy : (∫ z, S.parameterEnergy Q m v z ∂ν) ≤ E₀) :
    Integrable (S.parameterEnergy Q m v)
      (S.parameterValueOutput O m H e E₀ r hr (finalEpochIndex E₀ e + 1) ∘ₘ ν) ∧
    (∫ z, S.parameterEnergy Q m v z ∂S.parameterValueOutput O m H e E₀ r hr (finalEpochIndex E₀ e + 1) ∘ₘ ν)
      ≤ e / 50000 := by
  obtain ⟨hi, hb⟩ := S.parameterValueOutput_contract O hαℓ hfast hm hmH he r hr Q hQ model v hv hmin
    ν hInit hEnergy (finalEpochIndex E₀ e)
  have h := S.parameterEpochOutput_random_accuracy O hαℓ hfast hm hmH he
    (valueEnvelope_ge E₀ e (finalEpochIndex E₀ e)) r hr Q hQ model v hv hmin _ hi hb
  rw [Measure.comp_assoc, ← S.parameterValueOutput_succ, valueEnvelope_final he] at h
  exact h

theorem parameterValueOutput_accuracy (O : FreshOracle S.toNCObjective σ)
    (hαℓ : α ≤ ℓ) (hfast : ℓ / 4 ≤ α) {m H e E₀ : ℝ}
    (hm : 0 < m) (hmH : m ≤ H) (he : 0 < e)
    (r : Θ × Euclid dy → Euclid dy) (hr : Measurable r)
    (Q : Θ × Euclid dy → ℝ) (hQ : Measurable Q)
    (model : ∀ θ, SmoothStrongModel (fun y => Q (θ, y)) (fun y => gradient S.effectiveValue y + r (θ, y)) m H)
    (v : Θ → Euclid dy) (hv : Measurable v) (hmin : ∀ θ y, Q (θ, v θ) ≤ Q (θ, y))
    (ν : Measure (Θ × Joint dx dy)) [IsProbabilityMeasure ν]
    (hInit : Integrable (S.parameterEnergy Q m v) ν)
    (hEnergy : (∫ z, S.parameterEnergy Q m v z ∂ν) ≤ E₀) :
    Integrable (parameterGap (dx := dx) Q v)
      (S.parameterValueOutput O m H e E₀ r hr (finalEpochIndex E₀ e + 1) ∘ₘ ν) ∧
    Integrable (fun z : Θ × Joint dx dy => S.fastError m z.2)
      (S.parameterValueOutput O m H e E₀ r hr (finalEpochIndex E₀ e + 1) ∘ₘ ν) ∧
    (∫ z, parameterGap Q v z ∂S.parameterValueOutput O m H e E₀ r hr (finalEpochIndex E₀ e + 1) ∘ₘ ν) ≤ e ∧
    (∫ z, S.fastError m z.2 ∂S.parameterValueOutput O m H e E₀ r hr (finalEpochIndex E₀ e + 1) ∘ₘ ν) ≤ e := by
  obtain ⟨hi, hb⟩ := S.parameterValueOutput_energy O hαℓ hfast hm hmH he r hr Q hQ model v hv hmin ν hInit hEnergy
  have hgap : Integrable (parameterGap (dx := dx) Q v)
      (S.parameterValueOutput O m H e E₀ r hr (finalEpochIndex E₀ e + 1) ∘ₘ ν) := by
    apply hi.mono' (parameterGap_measurable Q hQ v hv).aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro z
    change ‖Q (z.1, z.2.2) - Q (z.1, v z.1)‖ ≤ S.parameterEnergy Q m v z
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (hmin z.1 z.2.2))]
    exact S.valueGap_le_solverEnergy (Q := fun y => Q (z.1, y)) hm.le (v z.1) z.2
  have hfi : Integrable (fun z : Θ × Joint dx dy => S.fastError m z.2)
      (S.parameterValueOutput O m H e E₀ r hr (finalEpochIndex E₀ e + 1) ∘ₘ ν) := by
    apply (hi.const_mul 66).mono' ((S.fastError_continuous m).measurable.comp measurable_snd).aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro z
    change ‖S.fastError m z.2‖ ≤ 66 * S.parameterEnergy Q m v z
    rw [Real.norm_eq_abs, abs_of_nonneg (S.fastError_nonneg hm.le z.2)]
    exact S.fastError_le_solverEnergy (model z.1) hm hfast (v z.1) (hmin z.1) z.2
  refine ⟨hgap, hfi, ?_, ?_⟩
  · have h := integral_mono hgap hi
      (fun z => S.valueGap_le_solverEnergy (Q := fun y => Q (z.1, y)) hm.le (v z.1) z.2)
    linarith
  · have h := integral_mono hfi (hi.const_mul 66)
      (fun z => S.fastError_le_solverEnergy (model z.1) hm hfast (v z.1) (hmin z.1) z.2)
    rw [integral_const_mul] at h
    linarith

theorem parameterValueSolverProgram_output (O : FreshOracle S.toNCObjective σ) (m H e E₀ : ℝ)
    (r : Θ × Euclid dy → Euclid dy) (hr : Measurable r) (ν : Measure (Θ × Joint dx dy)) :
    ((parameterValueSolverProgram dx dy ℓ α σ m H e E₀ r hr).originalKernel O.kernel ∘ₘ ν).map Prod.fst =
      S.parameterValueOutput O m H e E₀ r hr (finalEpochIndex E₀ e + 1) ∘ₘ ν := by
  rw [OracleProgram.originalKernel_eq_law, Measure.map_comp _ _ measurable_fst]
  rfl

theorem parameterValueSolverProgram_accuracy (O : FreshOracle S.toNCObjective σ)
    (hαℓ : α ≤ ℓ) (hfast : ℓ / 4 ≤ α) {m H e E₀ : ℝ}
    (hm : 0 < m) (hmH : m ≤ H) (he : 0 < e)
    (r : Θ × Euclid dy → Euclid dy) (hr : Measurable r)
    (Q : Θ × Euclid dy → ℝ) (hQ : Measurable Q)
    (model : ∀ θ, SmoothStrongModel (fun y => Q (θ, y)) (fun y => gradient S.effectiveValue y + r (θ, y)) m H)
    (v : Θ → Euclid dy) (hv : Measurable v) (hmin : ∀ θ y, Q (θ, v θ) ≤ Q (θ, y))
    (ν : Measure (Θ × Joint dx dy)) [IsProbabilityMeasure ν]
    (hInit : Integrable (S.parameterEnergy Q m v) ν)
    (hEnergy : (∫ z, S.parameterEnergy Q m v z ∂ν) ≤ E₀) :
    Integrable (fun t : (Θ × Joint dx dy) × ℕ => parameterGap Q v t.1)
      ((parameterValueSolverProgram dx dy ℓ α σ m H e E₀ r hr).originalKernel O.kernel ∘ₘ ν) ∧
    Integrable (fun t : (Θ × Joint dx dy) × ℕ => S.fastError m t.1.2)
      ((parameterValueSolverProgram dx dy ℓ α σ m H e E₀ r hr).originalKernel O.kernel ∘ₘ ν) ∧
    (∫ t, parameterGap Q v t.1 ∂(parameterValueSolverProgram dx dy ℓ α σ m H e E₀ r hr).originalKernel O.kernel ∘ₘ ν) ≤ e ∧
    (∫ t, S.fastError m t.1.2 ∂(parameterValueSolverProgram dx dy ℓ α σ m H e E₀ r hr).originalKernel O.kernel ∘ₘ ν) ≤ e := by
  obtain ⟨hg, hf, hgb, hfb⟩ := S.parameterValueOutput_accuracy O hαℓ hfast hm hmH he r hr Q hQ model v hv hmin
    ν hInit hEnergy
  rw [← S.parameterValueSolverProgram_output O m H e E₀ r hr ν] at hg hf hgb hfb
  have hgm := (parameterGap_measurable (dx := dx) Q hQ v hv).stronglyMeasurable
  have hfm : StronglyMeasurable (fun z : Θ × Joint dx dy => S.fastError m z.2) :=
    ((S.fastError_continuous m).measurable.comp measurable_snd).stronglyMeasurable
  refine ⟨(integrable_map_measure (g := parameterGap (dx := dx) Q v)
      hgm.aestronglyMeasurable measurable_fst.aemeasurable).mp hg,
    (integrable_map_measure (g := fun z : Θ × Joint dx dy => S.fastError m z.2)
      hfm.aestronglyMeasurable measurable_fst.aemeasurable).mp hf, ?_, ?_⟩
  · rw [integral_map measurable_fst.aemeasurable hgm.aestronglyMeasurable] at hgb
    exact hgb
  · rw [integral_map measurable_fst.aemeasurable hfm.aestronglyMeasurable] at hfb
    exact hfb

end SCObjective
end FreshGradientMinimax
