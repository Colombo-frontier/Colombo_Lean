import AdaptiveSphereSecondMomentBound
import PosteriorResidualEnergy

open MeasureTheory Set
open scoped Matrix RealInnerProductSpace

namespace Task006.AdaptiveSphereIsotropy
open Task006.Full Task006.Full.OracleAlgorithm
open Task006.HaarRebalancing Task006.AdaptiveSphereBlock
open Task006.AdaptiveSphereFrame Task006.AdaptiveSphereResidualFrame
open Task006.AdaptiveSphereState Task006.AdaptiveSphereAction
open Task006.AdaptiveSphereStopped Task006.AdaptiveSphereInvariance
open Task006.AdaptiveSphereTranscript Task006.AdaptiveSphereMeasurable
open Task006.AdaptiveSphereCoordinateRotations Task006.AdaptiveSphereGeometry
open Task006.PosteriorCenter Task006.AdaptiveSphereActualStep Task006.AdaptiveSphere
open Task006.AdaptiveSphereMean Task006.AdaptiveSphereReframe Task006.PosteriorResidualEnergy
noncomputable section
variable {d N : ℕ} {S Ω : Type*} [MeasurableSpace S]

theorem restrictedCoordinate_sum_squares_le_one (A : OracleAlgorithm d N S)
    (weight : Ω → ℝ) (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d)
    (t : ℕ) (j : Fin d) (H : Transcript N → ResidualControls d) (r : Fin (d+1))
    (Q : OrthogonalGroup d) :
    (∑ i : Fin (d-r.val), (restrictedCoordinate A weight tape seed k hkd t j H r i Q)^2) ≤ 1 := by
  by_cases hr : (reframedState A weight tape seed k hkd t j H Q).1 = r
  · simp only [restrictedCoordinate,if_pos hr]
    rw [← EuclideanSpace.real_norm_sq_eq,residualCoordinates_norm_sq,
      (action _).norm_map,column_norm Q j]
    nlinarith [sq_nonneg (‖prefixPart r.val
      (action (reframedState A weight tape seed k hkd t j H Q).2⁻¹ (column Q j))‖)]
  · simp only [restrictedCoordinate,if_neg hr,zero_pow (by norm_num : 2≠0),Finset.sum_const_zero]
    norm_num

/-- Actual per-direction conditional second-moment bound for every measurable
adaptive reframe and every rank with a nonempty residual space. -/
theorem restrictedCoordinate_conditional_square_le (A : OracleAlgorithm d N S)
    (weight : Ω → ℝ) (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d)
    (t : ℕ) (ht : t ≤ N) (j : Fin d) (hstop : RankStopped A weight tape seed k hkd)
    (H : Transcript N → ResidualControls d) (hH : Measurable H)
    (r : Fin (d+1)) (hrd : r.val < d) (i : Fin (d-r.val)) :
    (orthogonalHaarProbability d)[(fun Q =>
      (restrictedCoordinate A weight tape seed k hkd t j H r i Q)^2) |
        pastSigma A weight tape seed t j] ≤ᵐ[orthogonalHaarProbability d]
          (fun _ => 1/((d-r.val : ℕ):ℝ)) := by
  apply conditional_square_le_inverse_dimension (d-r.val) (by omega)
    (pastSigma A weight tape seed t j) (measurable_history A weight tape seed t j).comap_le
    (restrictedCoordinate A weight tape seed k hkd t j H r)
  · exact fun l => restrictedCoordinate_square_integrable A weight tape seed k hkd t j H hH r l
  · exact Filter.Eventually.of_forall
      (restrictedCoordinate_sum_squares_le_one A weight tape seed k hkd t j H r)
  · exact fun l l' => restrictedCoordinate_conditional_squares_equal A weight tape seed k hkd
      t ht j hstop H hH r l l'

/-- Integration on any genuine old-past event. The event may select whether a
new independent query direction is acquired. -/
theorem restrictedCoordinate_event_square_le (A : OracleAlgorithm d N S)
    (weight : Ω → ℝ) (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d)
    (t : ℕ) (ht : t ≤ N) (j : Fin d) (hstop : RankStopped A weight tape seed k hkd)
    (H : Transcript N → ResidualControls d) (hH : Measurable H)
    (r : Fin (d+1)) (hrd : r.val < d) (i : Fin (d-r.val))
    (event : Set (OrthogonalGroup d)) (hevent : MeasurableSet[pastSigma A weight tape seed t j] event) :
    (∫ Q in event, (restrictedCoordinate A weight tape seed k hkd t j H r i Q)^2
      ∂orthogonalHaarProbability d) ≤
    (∫ _Q in event, 1/((d-r.val : ℕ):ℝ) ∂orthogonalHaarProbability d) := by
  have hm := (measurable_history A weight tape seed t j).comap_le
  have hf := restrictedCoordinate_square_integrable A weight tape seed k hkd t j H hH r i
  rw [← setIntegral_condExp hm hf hevent]
  apply setIntegral_mono_ae
    integrable_condExp.integrableOn (integrable_const _).integrableOn
  exact restrictedCoordinate_conditional_square_le A weight tape seed k hkd t ht j hstop H hH r hrd i

#print axioms restrictedCoordinate_sum_squares_le_one
#print axioms restrictedCoordinate_conditional_square_le
#print axioms restrictedCoordinate_event_square_le
end
end Task006.AdaptiveSphereIsotropy
