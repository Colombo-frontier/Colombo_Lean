import RandomizedFO2003.CascadeFamily
import RandomizedFO2003.CascadeCoordinatesStationarity
import RandomizedFO2003.CascadeWeightProbability
import RandomizedFO2003.MarkedReadoutEvent
import RandomizedFO2003.FrameMeasurability

namespace RandomizedFO2003.Rotations

open MeasureTheory SpectralCoordinates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem measurable_continuousConjugation (A : E →L[ℝ] E) :
    Measurable (fun U : Rotation E => continuousConjugation (isometry E U) A) := by
  have heq : (fun U : Rotation E => continuousConjugation (isometry E U) A) =
      (fun U : Rotation E => (U : E →L[ℝ] E).comp (A.comp ((U⁻¹ : Rotation E) : E →L[ℝ] E))) := by
    funext U
    apply ContinuousLinearMap.ext
    intro x
    simp only [continuousConjugation_apply, ← isometry_inv, isometry_apply,
      ContinuousLinearMap.comp_apply]
  rw [heq]
  exact measurable_operator_comp measurable_subtype_coe
    (measurable_operator_comp measurable_const (measurable_subtype_coe.comp measurable_inv))

end RandomizedFO2003.Rotations

namespace RandomizedFO2003.Cascade

open SpectralCoordinates Rotations

/-- A Borel structure for the nested block product. Keeping the inner
spectral block explicit avoids overriding the standard-coordinate space's
existing measurable structure. -/
instance spectralBlockProductMeasurableSpace {J : ℕ} (K : Fin J → ℕ) (N : ℕ) :
    MeasurableSpace (BlockProduct N (BlockSpace K)) := borel _

instance spectralBlockProductBorelSpace {J : ℕ} (K : Fin J → ℕ) (N : ℕ) :
    BorelSpace (BlockProduct N (BlockSpace K)) := ⟨rfl⟩

/-- The same sample space used by `cascadeParameterLaw`: no algorithm or
query appears in either its coordinates or its measurable structure. -/
abbrev Sample {J : ℕ} (K : Fin J → ℕ) (N : ℕ) :=
  (Fin (N + 1) → BlockSpace K) × (Fin (N + 1) → Rotation (BlockSpace K))

end RandomizedFO2003.Cascade

namespace RandomizedFO2003.FiniteSpectralDesign

open MeasureTheory SpectralCoordinates Cascade Rotations
open scoped BigOperators

variable {m : ℕ} {γ L : ℝ} (S : FiniteSpectralDesign m γ L (1 / (16 * γ)))

noncomputable def cascadeCoefficients (K : Fin S.size → ℕ) (N : ℕ) (h : ℝ)
    (p : Sample K N) : Coefficients N (BlockSpace K) :=
  (fun i => continuousConjugation (isometry _ (p.2 i)) (continuousDiagonal K S.node),
    (fun i => isometry _ (p.2 i) (direction K (p.1 i) S.residual)),
    (fun i => isometry _ (p.2 i) (h • p.1 i)))

theorem measurable_cascadeCoefficients (K : Fin S.size → ℕ) (N : ℕ) (h : ℝ) :
    Measurable (S.cascadeCoefficients K N h) := by
  have hU (i : Fin (N + 1)) : Measurable (fun p : Sample K N => p.2 i) :=
    (measurable_pi_apply i).comp measurable_snd
  have hu (i : Fin (N + 1)) : Measurable (fun p : Sample K N => p.1 i) :=
    (measurable_pi_apply i).comp measurable_fst
  unfold cascadeCoefficients
  apply Measurable.prodMk
  · apply measurable_pi_lambda
    intro i
    exact (measurable_continuousConjugation (continuousDiagonal K S.node)).comp
      (hU i)
  · apply Measurable.prodMk
    · apply measurable_pi_lambda
      intro i
      exact (continuous_action (BlockSpace K)).measurable.comp
        ((hU i).prodMk ((measurable_direction K S.residual).comp (hu i)))
    · apply measurable_pi_lambda
      intro i
      exact (continuous_action (BlockSpace K)).measurable.comp
        ((hU i).prodMk (measurable_const.smul (hu i)))

theorem cascadeCoefficients_data (K : Fin S.size → ℕ) (N : ℕ) (h : ℝ) (p : Sample K N) :
    coefficientsData N (BlockSpace K) (S.cascadeCoefficients K N h p)
      (radiusCoefficient * h / γ) (h / (64 * γ)) (h ^ 2 / γ) forcingOffset saturationThreshold =
      S.cascade K N (fun i => isometry _ (p.2 i)) p.1 h := rfl

noncomputable def sampledCascadeFunction (K : Fin S.size → ℕ) (N : ℕ) (h : ℝ)
    (p : Sample K N) : Model.Space ((N + 1) * ∑ j, K j) → ℝ :=
  S.cascadeFunction K N (fun i => isometry _ (p.2 i)) p.1 h

theorem measurable_sampledCascadeFunction (K : Fin S.size → ℕ) (N : ℕ) (h : ℝ) :
    Measurable (Function.uncurry (S.sampledCascadeFunction K N h)) := by
  letI : BorelSpace (Coefficients N (BlockSpace K)) := Prod.borelSpace
  have hc := (coefficients_energy_continuous (N := N) (E := BlockSpace K)
    (radiusCoefficient * h / γ) (h / (64 * γ)) (h ^ 2 / γ) forcingOffset saturationThreshold).measurable
  have hx : Measurable (fun p : Sample K N × Model.Space ((N + 1) * ∑ j, K j) =>
      (cascadeCoordinates K N).symm p.2) :=
    (cascadeCoordinates K N).symm.continuous.measurable.comp measurable_snd
  have hm := hc.comp (((S.measurable_cascadeCoefficients K N h).comp measurable_fst).prodMk hx)
  simpa only [Function.comp_apply, cascadeCoefficients_data, sampledCascadeFunction,
    cascadeFunction, Function.uncurry] using hm

/-- The true gradient is jointly measurable even when a normalized residual
direction is discontinuous at zero. No good-weight event is assumed. -/
theorem measurable_sampledCascadeGradient (K : Fin S.size → ℕ) (N : ℕ) (h : ℝ) :
    Measurable (fun p : Sample K N × Model.Space ((N + 1) * ∑ j, K j) =>
      gradient (S.sampledCascadeFunction K N h p.1) p.2) := by
  have hx : Measurable (fun p : Sample K N × Model.Space ((N + 1) * ∑ j, K j) =>
      (cascadeCoordinates K N).symm p.2) :=
    (cascadeCoordinates K N).symm.continuous.measurable.comp measurable_snd
  have hg := (coefficients_gradient_measurable (N := N) (E := BlockSpace K)
    (radiusCoefficient * h / γ) (h / (64 * γ)) (h ^ 2 / γ) forcingOffset saturationThreshold).comp
      (((S.measurable_cascadeCoefficients K N h).comp measurable_fst).prodMk hx)
  have hout := (cascadeCoordinates K N).continuous.measurable.comp hg
  simpa only [Function.comp_apply, cascadeCoefficients_data, sampledCascadeFunction,
    cascadeFunction_gradient] using hout

theorem measurable_sampledCascadeOracle (K : Fin S.size → ℕ) (N : ℕ) (h : ℝ) :
    Measurable (fun p : Sample K N × Model.Space ((N + 1) * ∑ j, K j) =>
      Model.oracle (S.sampledCascadeFunction K N h p.1) p.2) :=
  (S.measurable_sampledCascadeFunction K N h).prodMk (S.measurable_sampledCascadeGradient K N h)

end RandomizedFO2003.FiniteSpectralDesign
