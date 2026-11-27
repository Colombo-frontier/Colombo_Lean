import HaarRebalancingAction

/-!
Uniqueness of the rotationally invariant unit-sphere probability law, proved
by compact-group Haar averaging and Tonelli. This is a measure equality
proof, not a uniqueness axiom or a premise naming the desired distribution.
-/

open Set MeasureTheory MeasureTheory.Measure ProbabilityTheory
open scoped ENNReal NNReal RealInnerProductSpace Matrix

namespace Task006.HaarRebalancing
noncomputable section
variable {d : ℕ}

/-- Compact normalized Haar is also right invariant, by Haar uniqueness and
its already proved probability normalization. -/
instance orthogonalHaarProbability_isRightInvariant :
    IsMulRightInvariant (orthogonalHaarProbability d) where
  map_mul_right_eq_self A := by
    letI : SecondCountableTopology (Matrix (Fin d) (Fin d) ℝ) :=
      inferInstanceAs (SecondCountableTopology (Fin d → Fin d → ℝ))
    letI : SecondCountableTopology (OrthogonalGroup d) :=
      inferInstanceAs (SecondCountableTopology (unitary (Matrix (Fin d) (Fin d) ℝ) :
        Set (Matrix (Fin d) (Fin d) ℝ)))
    change Measure.map (fun Q : OrthogonalGroup d => Q * A)
      (orthogonalHaarProbability d) = haarMeasure (orthogonalHaarCompact d)
    symm
    apply (haarMeasure_eq_iff (orthogonalHaarCompact d) _).2
    change (Measure.map (fun Q : OrthogonalGroup d => Q * A)
      (orthogonalHaarProbability d)) Set.univ = 1
    rw [Measure.map_apply (measurable_mul_const A) MeasurableSet.univ]
    simp

/-- Haar averages over the orbit depend only on the radius. -/
theorem orbit_lintegral_eq (f : EuclideanSpace ℝ (Fin d) → ℝ≥0∞)
    (x y : EuclideanSpace ℝ (Fin d)) (hxy : ‖x‖ = ‖y‖) :
    (∫⁻ Q, f (action Q x) ∂orthogonalHaarProbability d) =
      ∫⁻ Q, f (action Q y) ∂orthogonalHaarProbability d := by
  obtain ⟨A, hA⟩ := action_transitive_on_sphere x y hxy
  symm
  calc
    (∫⁻ Q, f (action Q y) ∂orthogonalHaarProbability d) =
        ∫⁻ Q, f (action (Q * A) x) ∂orthogonalHaarProbability d := by
      apply lintegral_congr_ae
      filter_upwards [] with Q
      rw [action_mul, hA]
    _ = ∫⁻ Q, f (action Q x) ∂orthogonalHaarProbability d :=
      lintegral_mul_right_eq_self (fun Q => f (action Q x)) A

/-- A unit-supported invariant probability integrates every measurable
nonnegative function by the same concrete Haar orbit average. -/
theorem invariant_unit_lintegral_eq_haar
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (hunit : ∀ᵐ x ∂μ, ‖x‖ = 1)
    (hrot : ∀ U : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d),
      Measure.map U μ = μ)
    (x₀ : EuclideanSpace ℝ (Fin d)) (hx₀ : ‖x₀‖ = 1)
    (f : EuclideanSpace ℝ (Fin d) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f x ∂μ) = ∫⁻ Q, f (action Q x₀) ∂orthogonalHaarProbability d := by
  have hfixed (Q : OrthogonalGroup d) :
      (∫⁻ x, f (action Q x) ∂μ) = ∫⁻ x, f x ∂μ := by
    rw [← lintegral_map hf (action Q).continuous.measurable, hrot]
  calc
    (∫⁻ x, f x ∂μ) =
        ∫⁻ Q, ∫⁻ x, f (action Q x) ∂μ ∂orthogonalHaarProbability d := by
      simp_rw [hfixed]
      simp
    _ = ∫⁻ x, ∫⁻ Q, f (action Q x) ∂orthogonalHaarProbability d ∂μ := by
      apply lintegral_lintegral_swap
      exact (hf.comp action_joint_continuous.measurable).aemeasurable
    _ = ∫⁻ _x, ∫⁻ Q, f (action Q x₀) ∂orthogonalHaarProbability d ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hunit] with x hx
      exact orbit_lintegral_eq f x x₀ (hx.trans hx₀.symm)
    _ = ∫⁻ Q, f (action Q x₀) ∂orthogonalHaarProbability d := by simp

/-- There is at most one probability on the Euclidean unit sphere invariant
under all ambient real linear isometries. -/
theorem invariant_unit_probability_unique
    (μ ν : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμunit : ∀ᵐ x ∂μ, ‖x‖ = 1) (hνunit : ∀ᵐ x ∂ν, ‖x‖ = 1)
    (hμrot : ∀ U : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d),
      Measure.map U μ = μ)
    (hνrot : ∀ U : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d),
      Measure.map U ν = ν) : μ = ν := by
  obtain ⟨x₀, hx₀⟩ := hμunit.exists
  apply Measure.ext
  intro s hs
  have hμ := invariant_unit_lintegral_eq_haar μ hμunit hμrot x₀ hx₀
    (s.indicator (fun _ => (1 : ℝ≥0∞))) (measurable_const.indicator hs)
  have hν := invariant_unit_lintegral_eq_haar ν hνunit hνrot x₀ hx₀
    (s.indicator (fun _ => (1 : ℝ≥0∞))) (measurable_const.indicator hs)
  simpa only [lintegral_indicator_const hs, one_mul] using hμ.trans hν.symm

/-- Any two random vectors satisfying the concrete uniform-sphere-law
interface have identical distributions. -/
theorem UniformSphereLaw.map_eq {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} {ν : Measure Ω'} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {v : Ω → EuclideanSpace ℝ (Fin d)} {w : Ω' → EuclideanSpace ℝ (Fin d)}
    (hv : UniformSphereLaw v μ) (hw : UniformSphereLaw w ν) :
    Measure.map v μ = Measure.map w ν := by
  letI : IsProbabilityMeasure (Measure.map v μ) := Measure.isProbabilityMeasure_map hv.measurable
  letI : IsProbabilityMeasure (Measure.map w ν) := Measure.isProbabilityMeasure_map hw.measurable
  apply invariant_unit_probability_unique
  · exact (ae_map_iff hv.measurable ((isClosed_eq continuous_norm continuous_const).measurableSet)).2 hv.unit_ae
  · exact (ae_map_iff hw.measurable ((isClosed_eq continuous_norm continuous_const).measurableSet)).2 hw.unit_ae
  · intro U
    rw [AEMeasurable.map_map_of_aemeasurable U.continuous.aemeasurable hv.measurable]
    exact hv.rotationInvariant U
  · intro U
    rw [AEMeasurable.map_map_of_aemeasurable U.continuous.aemeasurable hw.measurable]
    exact hw.rotationInvariant U

end
end Task006.HaarRebalancing
