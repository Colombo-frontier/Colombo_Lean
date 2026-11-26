import HardFamilyBayes
import UpperProgramRegularization

open MeasureTheory
open scoped RealInnerProductSpace

namespace Task006.HardFamilyBayes

open Task006.Full Task006.Full.OracleAlgorithm Task006.Full.HardFamily
open Task006.HaarRebalancing Task006.AdaptiveSphereTranscript Task006.AdaptiveSphereGlobal
open Task006.AdaptiveSphereState Task006.AdaptiveSphereStopped Task006.AdaptiveSphereJoint
open Task006.AdaptiveSphereStoppedCoupling

set_option maxHeartbeats 1000000
noncomputable section
variable {d N : ℕ} {S : Type*} [MeasurableSpace S]

def goodRankEvent (alg : OracleAlgorithm d N S) (k : ℕ) (hkd : k ≤ d) (j : Fin d) :
    Set (Exogenous S × OrthogonalGroup d) :=
  {w | (jointFrame alg k hkd N j w).1.val < k}

def boundedOutput (alg : OracleAlgorithm d N S) (R : ℝ) (hR : 0 ≤ R)
    (k : ℕ) (hkd : k ≤ d) (j : Fin d) (w : Exogenous S × OrthogonalGroup d) : Space d :=
  ballProj R hR (alg.output w.1.1 (jointHistory alg k hkd N j w))

theorem goodRankEvent_measurable_past (alg : OracleAlgorithm d N S)
    (k : ℕ) (hkd : k ≤ d) (j : Fin d) :
    MeasurableSet[jointPastSigma alg k hkd N j] (goodRankEvent alg k hkd j) := by
  have ho : @Measurable (Exogenous S × OrthogonalGroup d) (Exogenous S × Transcript N)
      (jointPastSigma alg k hkd N j) _ (jointObservation alg k hkd N j) :=
    measurable_iff_comap_le.mpr le_rfl
  have hc := (frameFromTranscript_joint_measurable alg k hkd N).comp ho
  have hframe : @Measurable (Exogenous S × OrthogonalGroup d) (FrameState d)
      (jointPastSigma alg k hkd N j) _ (jointFrame alg k hkd N j) := by
    change @Measurable (Exogenous S × OrthogonalGroup d) (FrameState d)
      (jointPastSigma alg k hkd N j) _ (fun w =>
        frameFromTranscript alg id w.1.2 w.1.1 k hkd N (jointHistory alg k hkd N j w))
    simpa only [Function.comp_def,jointObservation] using hc
  have hv : Measurable (fun r : Fin (d+1) => r.val) := measurable_of_countable _
  have hr := hv.comp (measurable_fst.comp hframe)
  exact hr measurableSet_Iio

theorem boundedOutput_stronglyMeasurable_past (alg : OracleAlgorithm d N S)
    (R : ℝ) (hR : 0 ≤ R) (k : ℕ) (hkd : k ≤ d) (j : Fin d) :
    StronglyMeasurable[jointPastSigma alg k hkd N j] (boundedOutput alg R hR k hkd j) := by
  have ho : @Measurable (Exogenous S × OrthogonalGroup d) (Exogenous S × Transcript N)
      (jointPastSigma alg k hkd N j) _ (jointObservation alg k hkd N j) :=
    measurable_iff_comap_le.mpr le_rfl
  have hy : Measurable (fun p : Exogenous S × Transcript N =>
      ballProj R hR (alg.output p.1.1 p.2)) := by
    exact (ballProj_lipschitz hR).continuous.measurable.comp
      (alg.output_measurable.comp (measurable_fst.fst.prodMk measurable_snd))
  have hc := hy.comp ho
  have hm : @Measurable (Exogenous S × OrthogonalGroup d) (Space d)
      (jointPastSigma alg k hkd N j) _ (boundedOutput alg R hR k hkd j) := by
    change @Measurable (Exogenous S × OrthogonalGroup d) (Space d)
      (jointPastSigma alg k hkd N j) _ (fun w =>
        ballProj R hR (alg.output w.1.1 (jointHistory alg k hkd N j w)))
    simpa only [Function.comp_def,jointObservation] using hc
  exact hm.stronglyMeasurable

theorem boundedOutput_norm_le (alg : OracleAlgorithm d N S)
    (R : ℝ) (hR : 0 ≤ R) (k : ℕ) (hkd : k ≤ d) (j : Fin d)
    (w : Exogenous S × OrthogonalGroup d) : ‖boundedOutput alg R hR k hkd j w‖ ≤ R := by
  simpa only [boundedOutput,Metric.mem_closedBall,dist_zero_right] using (ballProj_mem R hR
    (alg.output w.1.1 (jointHistory alg k hkd N j w)))

theorem boundedOutput_eq_original_on_event (alg : OracleAlgorithm d N S)
    (R : ℝ) (hR : 0 ≤ R) (k : ℕ) (hkd : k ≤ d) (j : Fin d)
    (hlegal : LegalOriginal alg R) (w : Exogenous S × OrthogonalGroup d)
    (hw : w ∈ goodRankEvent alg k hkd j) :
    boundedOutput alg R hR k hkd j w = originalOutput alg j w := by
  have he := finalTranscript_eq_of_rank_lt alg id w.1.2 w.1.1 k hkd (column w.2 j) hw
  change ballProj R hR (alg.output w.1.1
    ((stoppedObserver alg id w.1.2 w.1.1 k hkd).finalTranscript
      (linearSample id (column w.2 j)) w.1.2 ())) = _
  rw [← he]
  exact ballProj_eq_self hR (originalOutput_norm_le alg j R hlegal w)

theorem originalGap_risk_lower (alg : OracleAlgorithm d N S) (k : ℕ) (hkd : k ≤ d)
    (j : Fin d) (R slope : ℝ) (hR : 0 ≤ R) (hslope : 0 ≤ slope)
    (hlegal : LegalOriginal alg R) (γ : Measure (Exogenous S)) [IsProbabilityMeasure γ] :
    slope*R*((γ.prod (orthogonalHaarProbability d)).real (goodRankEvent alg k hkd j) -
      ∫ w, (goodRankEvent alg k hkd j).indicator (fun w => ‖jointCenter alg k hkd N j w‖) w
        ∂γ.prod (orthogonalHaarProbability d)) ≤
      ∫ w, originalGap alg j R slope w ∂γ.prod (orthogonalHaarProbability d) := by
  classical
  have hm : jointPastSigma alg k hkd N j ≤
      (inferInstance : MeasurableSpace (Exogenous S × OrthogonalGroup d)) :=
    (jointObservation_measurable alg k hkd N j).comap_le
  have he := goodRankEvent_measurable_past alg k hkd j
  have heΩ : MeasurableSet (goodRankEvent alg k hkd j) := hm _ he
  have hy := boundedOutput_stronglyMeasurable_past alg R hR k hkd j
  have hθ : Integrable (fun w : Exogenous S × OrthogonalGroup d => column w.2 j)
      (γ.prod (orthogonalHaarProbability d)) := by
    apply Integrable.of_bound ((measurable_column j).comp measurable_snd).aestronglyMeasurable 1
    exact Filter.Eventually.of_forall (fun w => ((orthonormal_column w.2).norm_eq_one j).le)
  have hC : Integrable (jointCenter alg k hkd N j) (γ.prod (orthogonalHaarProbability d)) := by
    apply Integrable.of_bound ((jointCenter_stronglyMeasurable_past alg k hkd N j).mono hm).aestronglyMeasurable 1
    exact Filter.Eventually.of_forall (jointCenter_norm_le_one alg k hkd N le_rfl j)
  have hinner : Integrable (fun w : Exogenous S × OrthogonalGroup d =>
      inner ℝ ((goodRankEvent alg k hkd j).indicator (boundedOutput alg R hR k hkd j) w)
        (column w.2 j)) (γ.prod (orthogonalHaarProbability d)) := by
    apply Integrable.of_bound
      (((hy.indicator he).mono hm).aestronglyMeasurable.inner hθ.aestronglyMeasurable) R
    apply Filter.Eventually.of_forall
    intro w
    by_cases hw : w ∈ goodRankEvent alg k hkd j
    · rw [Set.indicator_of_mem hw]
      have hb := norm_inner_le_norm (𝕜 := ℝ) (boundedOutput alg R hR k hkd j w) (column w.2 j)
      rw [(orthonormal_column w.2).norm_eq_one j,mul_one] at hb
      exact hb.trans (boundedOutput_norm_le alg R hR k hkd j w)
    · simp only [Set.indicator_of_notMem hw,inner_zero_left,norm_zero]
      exact hR
  apply Task006.LowerRisk.risk_lower_from_conditional_mean hm _ he _ _ _ R slope hR hslope
    hy (boundedOutput_norm_le alg R hR k hkd j) hθ hC hinner
    (joint_conditional_mean alg k hkd N le_rfl j γ)
    (originalGap alg j R slope)
    (originalGap_integrable alg j R slope hR hslope hlegal _)
    (fun w => (originalGap_bounds alg j R slope hR hslope hlegal w).1)
  intro w hw
  dsimp only [originalGap]
  rw [boundedOutput_eq_original_on_event alg R hR k hkd j hlegal w hw]

theorem event_center_cauchy_schwarz (alg : OracleAlgorithm d N S) (k : ℕ) (hkd : k ≤ d)
    (j : Fin d) (γ : Measure (Exogenous S)) [IsProbabilityMeasure γ] :
    (∫ w, (goodRankEvent alg k hkd j).indicator (fun w => ‖jointCenter alg k hkd N j w‖) w
      ∂γ.prod (orthogonalHaarProbability d))^2 ≤
      (γ.prod (orthogonalHaarProbability d)).real (goodRankEvent alg k hkd j) *
        (∫ w, (goodRankEvent alg k hkd j).indicator (fun w => ‖jointCenter alg k hkd N j w‖^2) w
          ∂γ.prod (orthogonalHaarProbability d)) := by
  have hm : jointPastSigma alg k hkd N j ≤
      (inferInstance : MeasurableSpace (Exogenous S × OrthogonalGroup d)) :=
    (jointObservation_measurable alg k hkd N j).comap_le
  have hc := (jointCenter_stronglyMeasurable_past alg k hkd N j).mono hm
  have hsquare : Integrable (fun w : Exogenous S × OrthogonalGroup d => ‖jointCenter alg k hkd N j w‖^2)
      (γ.prod (orthogonalHaarProbability d)) := by
    apply Integrable.of_bound (hc.norm.pow 2).aestronglyMeasurable 1
    apply Filter.Eventually.of_forall
    intro w
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    simp only [Pi.pow_apply]
    have hb := jointCenter_norm_le_one alg k hkd N le_rfl j w
    nlinarith [norm_nonneg (jointCenter alg k hkd N j w)]
  exact Task006.LowerRisk.event_cauchy_schwarz _
    (hm _ (goodRankEvent_measurable_past alg k hkd j)) _ hc.norm.measurable
    (fun w => norm_nonneg _) hsquare

end
end Task006.HardFamilyBayes
