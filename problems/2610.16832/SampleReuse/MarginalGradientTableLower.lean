import SampleReuse.MarginalGradientTable

open SecondOrder MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace SampleReuse
noncomputable section

variable {Ξ S Handle : Type} {d : ℕ} {R : ℝ} [Fintype Handle]
  [MeasurableSpace Ξ] [MeasurableSpace S] [MeasurableSpace Handle] [MeasurableSingletonClass Handle]

def marginalActualLaw (μ : Measure Ξ) (hR : 2 ≤ R) (θ : Bool) :
    Measure (Ξ × (Handle → SignedCoefficient R)) :=
  μ.prod (finitePiPMF (fun _ : Handle => coefficientPMF R (signValue θ) hR (signValue_sq θ))).toMeasure

instance marginalActualLaw_probability (μ : Measure Ξ) [IsProbabilityMeasure μ] (hR : 2 ≤ R) (θ : Bool) :
    IsProbabilityMeasure (marginalActualLaw (Handle := Handle) μ hR θ) := by
  unfold marginalActualLaw
  infer_instance

theorem marginal_actual_success_probability (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (P : Ξ → OracleAlgorithm (MarginalQuery Handle d) (PersistentReply d) (Point d) S)
    (hP : MeasurableOracleAlgorithmFamily P) (ε : ℝ) (v : Point d) (hR : 2 ≤ R) (θ : Bool) (N : ℕ) :
    (marginalOracleLaw μ P hP ε v hR θ N).real
      {h | ‖gradient (marginalLoss ε v (2*ε*signValue θ)) (marginalHistoryOutput P ε v N h)‖ ≤ ε} =
    (marginalActualLaw μ hR θ).real
      {w | ‖gradient (marginalLoss ε v (2*ε*signValue θ)) (marginalTableObservation P ε v N w).2‖ ≤ ε} := by
  have hs : MeasurableSet {z : ℕ × Point d |
      ‖gradient (marginalLoss ε v (2*ε*signValue θ)) z.2‖ ≤ ε} :=
    measurableSet_le
      (((contDiff_gradient_one (marginalLoss_contDiff ε v _ 2)).continuous.measurable.comp measurable_snd).norm)
      measurable_const
  have he := congrArg (fun ν : Measure (ℕ × Point d) => ν.real
    {z | ‖gradient (marginalLoss ε v (2*ε*signValue θ)) z.2‖ ≤ ε})
    (marginal_table_observation_law μ P hP ε v hR θ N)
  simpa only [measureReal_def,Measure.map_apply (marginalHistoryObservation_measurable P hP ε v N) hs,
    Measure.map_apply (marginalTableObservation_measurable P hP ε v N) hs,
    Set.preimage_setOf_eq,marginalHistoryObservation,marginalActualLaw] using he

theorem marginal_actual_expected_gradients (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (P : Ξ → OracleAlgorithm (MarginalQuery Handle d) (PersistentReply d) (Point d) S)
    (hP : MeasurableOracleAlgorithmFamily P) (ε : ℝ) (v : Point d) (hR : 2 ≤ R) (θ : Bool) (N : ℕ) :
    (∫ h, (marginalHistoryGradientCount (fun ξ => (P ξ).toQueryPolicy) ε v N h : ℝ)
      ∂marginalOracleLaw μ P hP ε v hR θ N) =
    ∫ w, ((marginalTableObservation P ε v N w).1 : ℝ) ∂marginalActualLaw μ hR θ := by
  have hm : Measurable (fun z : ℕ × Point d => (z.1:ℝ)) :=
    (measurable_of_countable (fun n : ℕ => (n:ℝ))).comp measurable_fst
  have he := congrArg (fun ν : Measure (ℕ × Point d) => ∫ z, (z.1:ℝ) ∂ν)
    (marginal_table_observation_law μ P hP ε v hR θ N)
  simpa only [integral_map (marginalHistoryObservation_measurable P hP ε v N).aemeasurable hm.aestronglyMeasurable,
    integral_map (marginalTableObservation_measurable P hP ε v N).aemeasurable hm.aestronglyMeasurable,
    marginalHistoryObservation,marginalActualLaw] using he

/-- The finite-horizon marginal lower bound for the original, independently
preallocated scalar sample tables, with arbitrary private randomization. -/
theorem marginal_actual_gradient_lower (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (P : Ξ → OracleAlgorithm (MarginalQuery Handle d) (PersistentReply d) (Point d) S)
    (hP : MeasurableOracleAlgorithmFamily P) {ε : ℝ} (hε : 0 < ε)
    {v : Point d} (hv : ‖v‖=1) (hR : 2 ≤ R) (N : ℕ)
    (hsuccess : ∀ θ : Bool, (2/3:ℝ) ≤ (marginalActualLaw μ hR θ).real
      {w | ‖gradient (marginalLoss ε v (2*ε*signValue θ)) (marginalTableObservation P ε v N w).2‖ ≤ ε}) :
    ∃ θ : Bool, binaryTestingConstant*R^2 ≤
      ∫ w, ((marginalTableObservation P ε v N w).1 : ℝ) ∂marginalActualLaw μ hR θ := by
  have hs : ∀ θ : Bool, (2/3:ℝ) ≤ (marginalOracleLaw μ P hP ε v hR θ N).real
      {h | ‖gradient (marginalLoss ε v (2*ε*signValue θ)) (marginalHistoryOutput P ε v N h)‖ ≤ ε} := by
    intro θ
    rw [marginal_actual_success_probability]
    exact hsuccess θ
  obtain ⟨θ,hθ⟩ := marginal_gradient_instance_lower μ P hP hε hv hR N hs
  exact ⟨θ,by rwa [marginal_actual_expected_gradients] at hθ⟩

end
end SampleReuse
