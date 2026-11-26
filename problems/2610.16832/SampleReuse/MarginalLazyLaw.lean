import SampleReuse.MarginalHandleNormalization
import SampleReuse.MarginalGradientTruncation
import SampleReuse.PersistentTapeEvents

open SecondOrder MeasureTheory
open scoped Classical
namespace SampleReuse
noncomputable section
variable {Ξ H S : Type} {d : ℕ} {R : ℝ} [MeasurableSpace Ξ]
  [MeasurableSpace S] [MeasurableSpace (List H)]

def marginalLazyLaw (μ : Measure Ξ) (hR : 2 ≤ R) (θ : Bool) :
    Measure (Ξ × (ℕ → SignedCoefficient R)) :=
  μ.prod (iidSampleTapeLaw (coefficientPMF R (signValue θ) hR (signValue_sq θ)))

instance marginalLazyLaw_probability (μ : Measure Ξ) [IsProbabilityMeasure μ] (hR : 2 ≤ R) (θ : Bool) :
    IsProbabilityMeasure (marginalLazyLaw μ hR θ) := by
  unfold marginalLazyLaw
  infer_instance

theorem marginalLazyObservation_measurable
    (P : Ξ → OracleAlgorithm (MarginalQuery H d) (PersistentReply d) (Point d) S) (N : ℕ)
    (hN : MeasurableOracleAlgorithmFamily (fun ξ => normalizeMarginalOracle N (P ξ)))
    (ε : ℝ) (v : Point d) : Measurable (marginalLazyObservation (R := R) P ε v N) := by
  have hp : Measurable (fun w : Ξ × (ℕ → SignedCoefficient R) =>
      (w.1,fun i : Fin (N+1) => w.2 i.val)) := measurable_fst.prodMk
    (measurable_pi_lambda _ (fun i => (measurable_pi_apply i.val).comp measurable_snd))
  have hh := (marginalTableObservation_measurable _ hN ε v N).comp hp
  exact (funext (normalized_marginal_observation P ε v N)) ▸ hh

theorem marginal_lazy_observation_law (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (P : Ξ → OracleAlgorithm (MarginalQuery H d) (PersistentReply d) (Point d) S) (N : ℕ)
    (hN : MeasurableOracleAlgorithmFamily (fun ξ => normalizeMarginalOracle N (P ξ)))
    (ε : ℝ) (v : Point d) (hR : 2 ≤ R) (θ : Bool) :
    (marginalLazyLaw μ hR θ).map (marginalLazyObservation P ε v N) =
      (marginalActualLaw (Handle := Fin (N+1)) μ hR θ).map
        (marginalTableObservation (fun ξ => normalizeMarginalOracle N (P ξ)) ε v N) := by
  let prefixTape := fun w : Ξ × (ℕ → SignedCoefficient R) => (w.1,fun i : Fin (N+1) => w.2 i.val)
  have hp : Measurable prefixTape := measurable_fst.prodMk
    (measurable_pi_lambda _ (fun i => (measurable_pi_apply i.val).comp measurable_snd))
  have he : marginalLazyObservation P ε v N =
      marginalTableObservation (fun ξ => normalizeMarginalOracle N (P ξ)) ε v N ∘ prefixTape := by
    funext w
    exact (normalized_marginal_observation P ε v N w).symm
  rw [he,← Measure.map_map (marginalTableObservation_measurable _ hN ε v N) hp]
  unfold marginalLazyLaw marginalActualLaw
  rw [iidSampleTapeLaw_joint_prefix]

theorem marginal_lazy_success_probability (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (P : Ξ → OracleAlgorithm (MarginalQuery H d) (PersistentReply d) (Point d) S) (N : ℕ)
    (hN : MeasurableOracleAlgorithmFamily (fun ξ => normalizeMarginalOracle N (P ξ)))
    (ε : ℝ) (v : Point d) (hR : 2 ≤ R) (θ : Bool) :
    (marginalLazyLaw μ hR θ).real {w | ‖gradient (marginalLoss ε v (2*ε*signValue θ))
      (marginalLazyObservation P ε v N w).2‖ ≤ ε} =
    (marginalActualLaw (Handle := Fin (N+1)) μ hR θ).real {w |
      ‖gradient (marginalLoss ε v (2*ε*signValue θ))
        (marginalTableObservation (fun ξ => normalizeMarginalOracle N (P ξ)) ε v N w).2‖ ≤ ε} := by
  have hs : MeasurableSet {z : ℕ × Point d |
      ‖gradient (marginalLoss ε v (2*ε*signValue θ)) z.2‖ ≤ ε} := measurableSet_le
    (((contDiff_gradient_one (marginalLoss_contDiff ε v _ 2)).continuous.measurable.comp measurable_snd).norm)
    measurable_const
  have he := congrArg (fun ν : Measure (ℕ × Point d) => ν.real
    {z | ‖gradient (marginalLoss ε v (2*ε*signValue θ)) z.2‖ ≤ ε})
    (marginal_lazy_observation_law μ P N hN ε v hR θ)
  simpa only [measureReal_def,Measure.map_apply (marginalLazyObservation_measurable P N hN ε v) hs,
    Measure.map_apply (marginalTableObservation_measurable _ hN ε v N) hs,Set.preimage_setOf_eq] using he

theorem marginal_lazy_expected_gradients (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (P : Ξ → OracleAlgorithm (MarginalQuery H d) (PersistentReply d) (Point d) S) (N : ℕ)
    (hN : MeasurableOracleAlgorithmFamily (fun ξ => normalizeMarginalOracle N (P ξ)))
    (ε : ℝ) (v : Point d) (hR : 2 ≤ R) (θ : Bool) :
    (∫ w, ((marginalLazyObservation P ε v N w).1 : ℝ) ∂marginalLazyLaw μ hR θ) =
    ∫ w, ((marginalTableObservation (fun ξ => normalizeMarginalOracle N (P ξ)) ε v N w).1 : ℝ)
      ∂marginalActualLaw (Handle := Fin (N+1)) μ hR θ := by
  have hm : Measurable (fun z : ℕ × Point d => (z.1:ℝ)) :=
    (measurable_of_countable (fun n : ℕ => (n:ℝ))).comp measurable_fst
  have he := congrArg (fun ν : Measure (ℕ × Point d) => ∫ z, (z.1:ℝ) ∂ν)
    (marginal_lazy_observation_law μ P N hN ε v hR θ)
  simpa only [integral_map (marginalLazyObservation_measurable P N hN ε v).aemeasurable hm.aestronglyMeasurable,
    integral_map (marginalTableObservation_measurable _ hN ε v N).aemeasurable hm.aestronglyMeasurable] using he

end
end SampleReuse
