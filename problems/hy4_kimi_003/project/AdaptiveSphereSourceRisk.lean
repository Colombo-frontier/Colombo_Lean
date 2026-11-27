import AdaptiveSphereSourceEvent
import HardFamilyBayesLower
import LowerRiskSharpArithmetic

/-! Literal source event L8--L9, using the original algorithm's K throughout. -/
open MeasureTheory Set
open scoped RealInnerProductSpace
namespace Task006.AdaptiveSphereSourceEvent
open Task006.Full Task006.Full.OracleAlgorithm Task006.Full.HardFamily
open Task006.HaarRebalancing Task006.AdaptiveSphereFrame Task006.AdaptiveSphereState
open Task006.AdaptiveSphereTranscript Task006.AdaptiveSphereStopped Task006.AdaptiveSphereMean
open Task006.AdaptiveSphereGlobal Task006.AdaptiveSphereJoint Task006.PosteriorCenter
open Task006.AdaptiveSphereSpan Task006.RankHandleCount Task006.HardFamilyBayes Task006.StoppedEnergy
set_option maxHeartbeats 1000000
noncomputable section
variable {d N : ℕ} {S : Type*} [MeasurableSpace S]

theorem source_event_subset_goodRankEvent (alg : OracleAlgorithm d N S)
    (R : ℝ) (hlegal : LegalOriginal alg R) (k : ℕ) (hkd : k ≤ d) (j : Fin d)
    (w : Exogenous S × OrthogonalGroup d) (hw : w∈sourceHandleEvent alg j k) :
    w ∈ goodRankEvent alg k hkd j := by
  exact (finalRank_le_twice_originalK alg R hlegal k hkd j w).trans_lt hw

theorem source_originalGap_risk_lower (alg : OracleAlgorithm d N S) (k : ℕ) (hkd : k ≤ d)
    (j : Fin d) (R slope : ℝ) (hR : 0 ≤ R) (hslope : 0 ≤ slope)
    (hlegal : LegalOriginal alg R) (γ : Measure (Exogenous S)) [IsProbabilityMeasure γ] :
    slope*R*((γ.prod (orthogonalHaarProbability d)).real (sourceHandleEvent alg j k) -
      ∫ w, (sourceHandleEvent alg j k).indicator (fun w => ‖jointCenter alg k hkd N j w‖) w
        ∂γ.prod (orthogonalHaarProbability d)) ≤
      ∫ w, originalGap alg j R slope w ∂γ.prod (orthogonalHaarProbability d) := by
  classical
  have hm : jointPastSigma alg k hkd N j ≤
      (inferInstance : MeasurableSpace (Exogenous S × OrthogonalGroup d)) :=
    (jointObservation_measurable alg k hkd N j).comap_le
  have he := sourceHandleEvent_measurable_past alg R hlegal k hkd j
  have heΩ : MeasurableSet (sourceHandleEvent alg j k) := hm _ he
  have hy := boundedOutput_stronglyMeasurable_past alg R hR k hkd j
  have hθ : Integrable (fun w : Exogenous S × OrthogonalGroup d => column w.2 j)
      (γ.prod (orthogonalHaarProbability d)) := by
    apply Integrable.of_bound ((measurable_column j).comp measurable_snd).aestronglyMeasurable 1
    exact Filter.Eventually.of_forall (fun w => ((orthonormal_column w.2).norm_eq_one j).le)
  have hC : Integrable (jointCenter alg k hkd N j) (γ.prod (orthogonalHaarProbability d)) := by
    apply Integrable.of_bound ((jointCenter_stronglyMeasurable_past alg k hkd N j).mono hm).aestronglyMeasurable 1
    exact Filter.Eventually.of_forall (jointCenter_norm_le_one alg k hkd N le_rfl j)
  have hinner : Integrable (fun w : Exogenous S × OrthogonalGroup d =>
      inner ℝ ((sourceHandleEvent alg j k).indicator (boundedOutput alg R hR k hkd j) w)
        (column w.2 j)) (γ.prod (orthogonalHaarProbability d)) := by
    apply Integrable.of_bound
      (((hy.indicator he).mono hm).aestronglyMeasurable.inner hθ.aestronglyMeasurable) R
    apply Filter.Eventually.of_forall
    intro w
    by_cases hw : w ∈ sourceHandleEvent alg j k
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
  rw [boundedOutput_eq_original_on_event alg R hR k hkd j hlegal w (source_event_subset_goodRankEvent alg R hlegal k hkd j w hw)]

theorem source_event_center_cauchy_schwarz (alg : OracleAlgorithm d N S)
    (R : ℝ) (hlegal : LegalOriginal alg R) (k : ℕ) (hkd : k ≤ d) (j : Fin d)
    (γ : Measure (Exogenous S)) [IsProbabilityMeasure γ] :
    (∫ w, (sourceHandleEvent alg j k).indicator (fun w => ‖jointCenter alg k hkd N j w‖) w
      ∂γ.prod (orthogonalHaarProbability d))^2 ≤
      (γ.prod (orthogonalHaarProbability d)).real (sourceHandleEvent alg j k) *
        (∫ w, (sourceHandleEvent alg j k).indicator (fun w => ‖jointCenter alg k hkd N j w‖^2) w
          ∂γ.prod (orthogonalHaarProbability d)) := by
  have hm := (jointObservation_measurable alg k hkd N j).comap_le
  have he := hm _ (sourceHandleEvent_measurable_past alg R hlegal k hkd j)
  have hf := ((jointCenter_stronglyMeasurable_past alg k hkd N j).mono hm).measurable.norm
  exact Task006.LowerRisk.event_cauchy_schwarz _ he _ hf (fun _ => norm_nonneg _)
    (joint_center_energy_integrable alg k hkd N le_rfl j γ)

theorem source_large_dimension_bayes_risk_gt_146 (alg : OracleAlgorithm d N S) (j : Fin d)
    (L R A eps : ℝ) (hL : 0 < L) (hR : 0 ≤ R) (hA : 16 ≤ A) (heps : 0 < eps)
    (hscale : (16*L/A)*R = 16*eps) (hd : 8 ≤ d) (hlegal : LegalOriginal alg R)
    (σ : Measure S) [IsProbabilityMeasure σ]
    (hbudget : (4096/A^3)*(N : ℝ) ≤ (d : ℝ)/32) :
    (146/100:ℝ)*eps < (∫ w, originalGap alg j R (16*L/A) w
      ∂(σ.prod (iidHandleLaw (law L A hA))).prod (orthogonalHaarProbability d)) := by
  classical
  let k := Task006LowerAudit.rankThreshold d
  have hkb := Task006LowerAudit.rank_threshold_bounds d hd
  have hkd : k ≤ d := by dsimp only [k]; omega
  have hk : 0 < k := by dsimp only [k]; omega
  have hdk : d ≤ 8*k := hkb.2.1
  have h4k : 4*(k : ℝ) ≤ (d : ℝ) := by exact_mod_cast hkb.2.2
  have hm : 0 ≤ 16*L/A := by positivity
  have ha := sourceHandleEvent_half_mass alg L A hL hA σ k hk hdk j hbudget
  have hevent : MeasurableSet (sourceHandleEvent alg j k) :=
    (jointObservation_measurable alg k hkd N j).comap_le _
      (sourceHandleEvent_measurable_past alg R hlegal k hkd j)
  have he : (∫ w, (sourceHandleEvent alg j k).indicator
      (fun w => ‖jointCenter alg k hkd N j w‖^2) w
      ∂(σ.prod (iidHandleLaw (law L A hA))).prod (orthogonalHaarProbability d)) ≤ 1/3 := by
    rw [integral_indicator hevent]
    exact (joint_event_center_energy_le_ratio alg k hkd j
      (σ.prod (iidHandleLaw (law L A hA))) _).trans
        (Task006LowerAudit.harmonic_energy_ratio_bound d k (Nat.cast_nonneg _) h4k).2.le
  have hn : 0 ≤ ∫ w, (sourceHandleEvent alg j k).indicator
      (fun w => ‖jointCenter alg k hkd N j w‖) w
      ∂(σ.prod (iidHandleLaw (law L A hA))).prod (orthogonalHaarProbability d) := by
    apply integral_nonneg
    intro w
    exact Set.indicator_nonneg (fun _ _ => norm_nonneg _) w
  have hCS := source_event_center_cauchy_schwarz alg R hlegal k hkd j (σ.prod (iidHandleLaw (law L A hA)))
  have hrisk := source_originalGap_risk_lower alg k hkd j R (16*L/A) hR hm hlegal
    (σ.prod (iidHandleLaw (law L A hA)))
  rw [hscale] at hrisk
  exact Task006.LowerRisk.large_dimension_risk_gt_146 eps _ _ _ _
    heps ha hn he hCS hrisk

/-- On the literal no-informative-handle event, the genuine conditional mean
of the hidden direction is zero, for every arbitrary postprocessing output. -/
theorem zero_handle_conditional_mean (alg : OracleAlgorithm d N S)
    (R : ℝ) (hlegal : LegalOriginal alg R) (h1d : 1≤d) (j : Fin d)
    (γ : Measure (Exogenous S)) [IsProbabilityMeasure γ] :
    ∀ᵐ w ∂γ.prod (orthogonalHaarProbability d), w∈sourceHandleEvent alg j 1 →
      ((γ.prod (orthogonalHaarProbability d))[(fun w => column w.2 j) | jointPastSigma alg 1 h1d N j]) w = 0 := by
  filter_upwards [joint_conditional_mean alg 1 h1d N le_rfl j γ] with w hw
  intro hE
  rw [hw]
  exact center_zero_on_zero_rank_event alg h1d j w
    (source_event_subset_goodRankEvent alg R hlegal 1 h1d j w hE)

#print axioms source_originalGap_risk_lower
#print axioms source_large_dimension_bayes_risk_gt_146
#print axioms zero_handle_conditional_mean
end
end Task006.AdaptiveSphereSourceEvent
