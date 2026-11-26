import RandomizedFO2003.SampledCascade
import RandomizedFO2003.ChosenCascade
import RandomizedFO2003.OracleMeasurability

namespace RandomizedFO2003.Spherical

open MeasureTheory

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Also valid in the zero-dimensional space: radial normalization always
lands in the closed unit ball. -/
theorem ae_norm_le_one : ∀ᵐ x ∂sphereLaw E, ‖x‖ ≤ 1 := by
  apply (ae_map_iff (measurable_radial E).aemeasurable
    (measurableSet_le measurable_norm measurable_const)).mpr
  apply Filter.Eventually.of_forall
  intro x
  by_cases hx : x = 0
  · simp [hx, radial]
  · exact (radial_norm E hx).le

end RandomizedFO2003.Spherical

namespace RandomizedFO2003.FiniteSpectralDesign

open MeasureTheory SpectralCoordinates Cascade Rotations Spherical
open scoped BigOperators

variable {m : ℕ} {γ L : ℝ} (S : FiniteSpectralDesign m γ L (1 / (16 * γ)))

theorem cascadeParameterLaw_unitBall (K : Fin S.size → ℕ) (N : ℕ) :
    ∀ᵐ p ∂S.cascadeParameterLaw K N, ∀ i, ‖p.1 i‖ ≤ 1 := by
  have hp : ∀ᵐ u ∂Measure.pi (fun _ : Fin (N + 1) => sphereLaw (BlockSpace K)),
      ∀ i, ‖u i‖ ≤ 1 := by
    apply Filter.eventually_all.mpr
    intro i
    exact (Measure.tendsto_eval_ae_ae
      (μ := fun _ : Fin (N + 1) => sphereLaw (BlockSpace K)) (i := i)).eventually
        (ae_norm_le_one (BlockSpace K))
  have hm : MeasurableSet {p : Sample K N | ∀ i, ‖p.1 i‖ ≤ 1} := by
    simp only [Set.setOf_forall]
    apply MeasurableSet.iInter
    intro i
    exact measurableSet_le (((measurable_pi_apply i).comp measurable_fst).norm) measurable_const
  apply (Measure.ae_prod_iff_ae_ae hm).mpr
  exact hp.mono (fun _ hu => Filter.Eventually.of_forall (fun _ => hu))

variable {Seed : Type} [MeasurableSpace Seed]

theorem measurable_sampledCascadeTranscript (K : Fin S.size → ℕ) (N : ℕ) (h : ℝ)
    (A : Model.Algorithm ((N + 1) * ∑ j, K j) Seed) (T : ℕ) :
    Measurable (fun p : Sample K N × Seed =>
      Model.transcript A (S.sampledCascadeFunction K N h p.1) p.2 T) :=
  Model.measurable_transcript_family A _ (S.measurable_sampledCascadeOracle K N h) T

theorem measurable_sampledCascadeOutput (K : Fin S.size → ℕ) (N : ℕ) (h : ℝ)
    (A : Model.Algorithm ((N + 1) * ∑ j, K j) Seed) (T : ℕ) :
    Measurable (fun p : Sample K N × Seed =>
      A.output T p.2 (Model.transcript A (S.sampledCascadeFunction K N h p.1) p.2 T)) :=
  Model.measurable_output_family A _ (S.measurable_sampledCascadeOracle K N h) T

theorem measurableSet_sampledCascadeSuccess (K : Fin S.size → ℕ) (N : ℕ) (h : ℝ)
    (A : Model.Algorithm ((N + 1) * ∑ j, K j) Seed) (ε : ℝ) (T : ℕ) :
    MeasurableSet (Model.familySuccess A (S.sampledCascadeFunction K N h) ε T) :=
  Model.measurableSet_familySuccess A _ (S.measurable_sampledCascadeOracle K N h) ε T

end RandomizedFO2003.FiniteSpectralDesign

namespace RandomizedFO2003.FiniteSpectralDesign

open MeasureTheory SpectralCoordinates Cascade Rotations

variable {ε Δ L₁ L₂ : ℝ}
variable (S : FiniteSpectralDesign (degreeCount ε L₁ L₂) (lowerCurvature ε L₂)
  (upperCurvature L₁) (1 / (16 * lowerCurvature ε L₂)))

/-- The actual, algorithm-independent parameter law gives functions in the
target class almost surely. No conditioning on a spectral or oracle event
changes the independent sphere/Haar law. -/
theorem sampledCascade_inFunctionClass_ae (hε : 0 < ε) (hL₁ : 0 < L₁) (hL₂ : 0 < L₂)
    (hregime : ε ≤ parameterConstant * L₁ ^ 2 / L₂)
    (hmass : massThreshold ≤ Δ * L₂ ^ (1 / 2 : ℝ) * ε ^ (-(3 / 2 : ℝ)))
    (K : Fin S.size → ℕ) :
    ∀ᵐ p ∂S.cascadeParameterLaw K (stageIndex ε Δ L₂),
      Model.InFunctionClass (S.sampledCascadeFunction K (stageIndex ε Δ L₂) (rhsScale ε) p) Δ L₁ L₂ := by
  filter_upwards [S.cascadeParameterLaw_unitBall K (stageIndex ε Δ L₂)] with p hp
  exact S.chosen_cascade_inFunctionClass hε hL₁ hL₂ hregime hmass K _ p.1 hp

end RandomizedFO2003.FiniteSpectralDesign
