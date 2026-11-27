import AdaptiveSphereInvariance
import AdaptiveSphereCoordinateRotations
import PosteriorCenter
import PosteriorCenterEnergy
import AdaptiveSphereConditionalMap

/-! The actual adaptive posterior mean, derived from proved Haar invariance
and an explicit residual negation. It is not a field of an oracle model. -/
set_option maxHeartbeats 1000000

open MeasureTheory Set
open scoped Matrix RealInnerProductSpace

namespace Task006.AdaptiveSphereMean
open Task006.Full Task006.Full.OracleAlgorithm
open Task006.HaarRebalancing Task006.AdaptiveSphereBlock
open Task006.AdaptiveSphereFrame Task006.AdaptiveSphereResidualFrame
open Task006.AdaptiveSphereState Task006.AdaptiveSphereAction
open Task006.AdaptiveSphereStopped Task006.AdaptiveSphereInvariance
open Task006.AdaptiveSphereTranscript Task006.AdaptiveSphereMeasurable
open Task006.AdaptiveSphereCoordinateRotations Task006.AdaptiveSphereGeometry
open Task006.PosteriorCenter Task006.AdaptiveSphereActualStep Task006.AdaptiveSphere
noncomputable section
variable {d N : ℕ} {S Ω : Type*} [MeasurableSpace S]

def negativeControl (d : ℕ) : ResidualControls d := fun r => negativeOrthogonal (d-r.val)

abbrev pastSigma (A : OracleAlgorithm d N S) (weight : Ω → ℝ) (tape : ℕ → Ω)
    (seed : S) (t : ℕ) (j : Fin d) : MeasurableSpace (OrthogonalGroup d) :=
  (inferInstance : MeasurableSpace (Transcript N)).comap (history A weight tape seed t j)

def actualCenter (A : OracleAlgorithm d N S) (weight : Ω → ℝ) (tape : ℕ → Ω)
    (seed : S) (k : ℕ) (hkd : k ≤ d) (t : ℕ) (j : Fin d)
    (Q : OrthogonalGroup d) : E d :=
  centerFromTranscript A weight tape seed k hkd t (history A weight tape seed t j Q)

theorem actualCenter_eq_projected (A : OracleAlgorithm d N S) (weight : Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d) (t : ℕ) (ht : t ≤ N)
    (j : Fin d) (Q : OrthogonalGroup d) :
    actualCenter A weight tape seed k hkd t j Q =
      projectedCenter (actualState A weight tape seed k hkd t j Q) (column Q j) := by
  have hpast : ∀ i : Fin N, i.val < t →
      A.finalTranscript (linearSample weight (column Q j)) tape seed i =
        history A weight tape seed t j Q i := by
    intro i hi
    exact runPrefix_coordinate_stable A (linearSample weight (column Q j)) tape seed t N ht i hi
  have hc := centerFromTranscript_past_only A weight tape seed k hkd t _ _ hpast
  have hs := frameFromTranscript_past_only A weight tape seed k hkd t _ _ hpast
  change centerFromTranscript A weight tape seed k hkd t _ = _
  rw [← hc,centerFromTranscript_actual_eq_projected,hs]
  rfl

theorem actualCenter_stronglyMeasurable_past (A : OracleAlgorithm d N S)
    (weight : Ω → ℝ) (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d)
    (t : ℕ) (j : Fin d) :
    StronglyMeasurable[pastSigma A weight tape seed t j]
      (actualCenter A weight tape seed k hkd t j) := by
  change StronglyMeasurable[(inferInstance : MeasurableSpace (Transcript N)).comap
      (history A weight tape seed t j)]
    (fun Q : OrthogonalGroup d => centerFromTranscript A weight tape seed k hkd t
      (history A weight tape seed t j Q))
  have h := (measurable_centerFromTranscript A weight tape seed k hkd t).stronglyMeasurable
      |>.comp_measurable (comap_measurable (history A weight tape seed t j))
  simpa only [Function.comp_def] using h

theorem actualCenter_measurable (A : OracleAlgorithm d N S) (weight : Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d) (t : ℕ) (j : Fin d) :
    Measurable (actualCenter A weight tape seed k hkd t j) := by
  change Measurable (fun Q : OrthogonalGroup d => centerFromTranscript A weight tape seed k hkd t
    (history A weight tape seed t j Q))
  have h := (measurable_centerFromTranscript A weight tape seed k hkd t).comp
    (measurable_history A weight tape seed t j)
  simpa only [Function.comp_def] using h

theorem column_norm (Q : OrthogonalGroup d) (j : Fin d) : ‖column Q j‖ = 1 :=
  (orthonormal_column Q).norm_eq_one j

theorem integrable_column (j : Fin d) :
    Integrable (fun Q : OrthogonalGroup d => column Q j) (orthogonalHaarProbability d) := by
  apply (integrable_const (1:ℝ)).mono' (measurable_column j).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun Q => (column_norm Q j).le)

theorem actualCenter_norm_le_one (A : OracleAlgorithm d N S) (weight : Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d) (t : ℕ) (ht : t ≤ N)
    (j : Fin d) (Q : OrthogonalGroup d) :
    ‖actualCenter A weight tape seed k hkd t j Q‖ ≤ 1 := by
  rw [actualCenter_eq_projected A weight tape seed k hkd t ht j Q]
  exact (projectedCenter_norm_le _ _).trans_eq (column_norm Q j)

theorem actualCenter_integrable (A : OracleAlgorithm d N S) (weight : Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d) (t : ℕ) (ht : t ≤ N)
    (j : Fin d) : Integrable (actualCenter A weight tape seed k hkd t j)
      (orthogonalHaarProbability d) := by
  apply (integrable_const (1:ℝ)).mono'
    (actualCenter_measurable A weight tape seed k hkd t j).aestronglyMeasurable
  exact Filter.Eventually.of_forall (actualCenter_norm_le_one A weight tape seed k hkd t ht j)

theorem rotateNegative_action (state : FrameState d) (θ : E d) :
    action (rotateAtState state (negativeControl d)) θ = (2 : ℝ) • projectedCenter state θ - θ := by
  rw [rotateAtState,action_mul,action_mul,negativeControl,blockNegative_action,map_sub,map_smul,
    action_inverse_cancel]
  rfl

/-- Genuine conditional mean for every prefix of any measurable randomized
adaptive rank-stopped policy. Private seed and sample tape are fixed independent
parameters; arbitrary query directions are allowed. -/
theorem rankStopped_conditional_mean (A : OracleAlgorithm d N S)
    (weight : Ω → ℝ) (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d)
    (j : Fin d) (hstop : RankStopped A weight tape seed k hkd)
    (t : ℕ) (ht : t ≤ N) :
    (orthogonalHaarProbability d)[(fun Q => column Q j) | pastSigma A weight tape seed t j]
      =ᵐ[orthogonalHaarProbability d] actualCenter A weight tape seed k hkd t j := by
  let μ := orthogonalHaarProbability d
  let C := actualCenter A weight tape seed k hkd t j
  let T := orbitTransform A weight tape seed k hkd t j (negativeControl d)
  obtain ⟨hmp,hfix⟩ := rankStopped_residual_invariance A weight tape seed k hkd j hstop t ht
  have hm : (pastSigma A weight tape seed t j) ≤ (inferInstance : MeasurableSpace (OrthogonalGroup d)) := by
    change (inferInstance : MeasurableSpace (Transcript N)).comap
      (history A weight tape seed t j) ≤ _
    exact (measurable_history A weight tape seed t j).comap_le
  have hC : Integrable C μ := actualCenter_integrable A weight tape seed k hkd t ht j
  have hθ : Integrable (fun Q => column Q j) μ := integrable_column j
  have hodd : ∀ Q, (column (T Q) j - C (T Q)) = -(column Q j - C Q) := by
    intro Q
    have hc : C (T Q) = C Q := congrArg
      (centerFromTranscript A weight tape seed k hkd t) (hfix (negativeControl d) Q)
    rw [hc]
    change column (rotateAtState (actualState A weight tape seed k hkd t j Q)
      (negativeControl d) * Q) j - C Q = _
    rw [column_mul_action,rotateNegative_action,
      ← actualCenter_eq_projected A weight tape seed k hkd t ht j Q]
    change (2 : ℝ) • C Q - column Q j - C Q = -(column Q j-C Q)
    module
  have hinv : ∀ s : Set (OrthogonalGroup d), MeasurableSet[(pastSigma A weight tape seed t j)] s → T ⁻¹' s = s := by
    intro s hs
    rcases hs with ⟨a,ha,rfl⟩
    ext Q
    change history A weight tape seed t j
      (orbitTransform A weight tape seed k hkd t j (negativeControl d) Q) ∈ a ↔ _
    rw [hfix]
    rfl
  have hdiff : Integrable (fun Q => column Q j-C Q) μ := by
    exact hθ.sub hC
  have hzero := condExp_zero_of_invariant_odd_map (μ := μ) (pastSigma A weight tape seed t j) hm T (hmp (negativeControl d))
    hinv
    (fun Q => column Q j-C Q) hdiff hodd
  have hsub := condExp_sub hθ hC (pastSigma A weight tape seed t j)
  have hceC : μ[C | (pastSigma A weight tape seed t j)] = C := by
    exact condExp_of_stronglyMeasurable (μ := μ) hm
      (actualCenter_stronglyMeasurable_past A weight tape seed k hkd t j) hC
  filter_upwards [hzero,hsub] with Q hz hs
  rw [hceC] at hs
  have he : (μ[(fun Q => column Q j) | (pastSigma A weight tape seed t j)]) Q - C Q = 0 := hs.symm.trans hz
  exact sub_eq_zero.mp he

#print axioms actualCenter_eq_projected
#print axioms actualCenter_stronglyMeasurable_past
#print axioms actualCenter_norm_le_one
#print axioms rotateNegative_action
#print axioms rankStopped_conditional_mean
end
end Task006.AdaptiveSphereMean
