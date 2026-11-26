import AdaptiveSphereExactMoment

/-! Exact conditional second moments of the real spherical adaptive posterior,
not merely the upper estimate used in the minimax lower bound. -/
open MeasureTheory Set
open scoped Matrix RealInnerProductSpace

namespace Task006.AdaptiveSphereIsotropy
open Task006.Full Task006.Full.OracleAlgorithm
open Task006.HaarRebalancing Task006.AdaptiveSphereBlock
open Task006.AdaptiveSphereFrame Task006.AdaptiveSphereResidualFrame
open Task006.AdaptiveSphereState Task006.AdaptiveSphereAction
open Task006.AdaptiveSphereStopped Task006.AdaptiveSphereInvariance
open Task006.AdaptiveSphereTranscript Task006.AdaptiveSphereMeasurable
open Task006.AdaptiveSphereGeometry Task006.PosteriorCenter Task006.AdaptiveSphereActualStep
open Task006.AdaptiveSphereMean Task006.AdaptiveSphereReframe Task006.AdaptiveSphere
open Task006.PosteriorResidualEnergy
noncomputable section
variable {d N : ℕ} {S Ω : Type*} [MeasurableSpace S]

def residualEnergyAtRank (A : OracleAlgorithm d N S) (weight : Ω → ℝ) (tape : ℕ → Ω)
    (seed : S) (k : ℕ) (hkd : k ≤ d) (t : ℕ) (j : Fin d) (r : Fin (d+1))
    (Q : OrthogonalGroup d) : ℝ :=
  if (actualState A weight tape seed k hkd t j Q).1 = r then
    1-‖actualCenter A weight tape seed k hkd t j Q‖^2 else 0

theorem actualState_measurable_past (A : OracleAlgorithm d N S) (weight : Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d) (t : ℕ) (j : Fin d) :
    Measurable[pastSigma A weight tape seed t j] (actualState A weight tape seed k hkd t j) := by
  change Measurable[(inferInstance : MeasurableSpace (Transcript N)).comap
      (history A weight tape seed t j)]
    (fun Q => frameFromTranscript A weight tape seed k hkd t (history A weight tape seed t j Q))
  exact (measurable_frameFromTranscript A weight tape seed k hkd t).comp (comap_measurable _)

theorem residualEnergyAtRank_stronglyMeasurable_past (A : OracleAlgorithm d N S)
    (weight : Ω → ℝ) (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d)
    (t : ℕ) (j : Fin d) (r : Fin (d+1)) :
    StronglyMeasurable[pastSigma A weight tape seed t j]
      (residualEnergyAtRank A weight tape seed k hkd t j r) := by
  letI : MeasurableSpace (OrthogonalGroup d) := pastSigma A weight tape seed t j
  have hr : Measurable[pastSigma A weight tape seed t j]
      (fun Q => (actualState A weight tape seed k hkd t j Q).1) :=
    measurable_fst.comp (actualState_measurable_past A weight tape seed k hkd t j)
  have hc : Measurable[pastSigma A weight tape seed t j]
      (actualCenter A weight tape seed k hkd t j) :=
    (actualCenter_stronglyMeasurable_past A weight tape seed k hkd t j).measurable
  have hm : Measurable[pastSigma A weight tape seed t j]
      (residualEnergyAtRank A weight tape seed k hkd t j r) := by
    change Measurable[pastSigma A weight tape seed t j] (fun Q =>
      if (actualState A weight tape seed k hkd t j Q).1 = r then
        1-‖actualCenter A weight tape seed k hkd t j Q‖^2 else 0)
    exact Measurable.ite (hr (measurableSet_singleton r))
      (measurable_const.sub (hc.norm.pow_const 2)) measurable_const
  exact hm.stronglyMeasurable

theorem residualEnergyAtRank_integrable (A : OracleAlgorithm d N S) (weight : Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d) (t : ℕ) (ht : t ≤ N)
    (j : Fin d) (r : Fin (d+1)) :
    Integrable (residualEnergyAtRank A weight tape seed k hkd t j r) (orthogonalHaarProbability d) := by
  have hm := (residualEnergyAtRank_stronglyMeasurable_past A weight tape seed k hkd t j r).measurable.mono
    (measurable_history A weight tape seed t j).comap_le le_rfl
  apply Integrable.of_bound hm.aestronglyMeasurable 1
  apply Filter.Eventually.of_forall
  intro Q
  unfold residualEnergyAtRank
  split_ifs
  · rw [Real.norm_eq_abs]
    apply abs_le.mpr
    have hc := actualCenter_norm_le_one A weight tape seed k hkd t ht j Q
    have hn := norm_nonneg (actualCenter A weight tape seed k hkd t j Q)
    constructor <;> nlinarith
  · norm_num

theorem restrictedCoordinate_sum_squares_eq_residualEnergy (A : OracleAlgorithm d N S)
    (weight : Ω → ℝ) (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d)
    (t : ℕ) (ht : t ≤ N) (j : Fin d) (H : Transcript N → ResidualControls d)
    (r : Fin (d+1)) (Q : OrthogonalGroup d) :
    (∑ i : Fin (d-r.val), (restrictedCoordinate A weight tape seed k hkd t j H r i Q)^2) =
      residualEnergyAtRank A weight tape seed k hkd t j r Q := by
  have hc : projectedCenter (reframedState A weight tape seed k hkd t j H Q) (column Q j) =
      actualCenter A weight tape seed k hkd t j Q := by
    rw [reframedState,reframe_projectedCenter,actualCenter_eq_projected A weight tape seed k hkd t ht j Q]
  have hrank : (reframedState A weight tape seed k hkd t j H Q).1 =
      (actualState A weight tape seed k hkd t j Q).1 := rfl
  by_cases hr : (actualState A weight tape seed k hkd t j Q).1 = r
  · have hr' : (reframedState A weight tape seed k hkd t j H Q).1 = r := hrank.trans hr
    simp only [restrictedCoordinate,if_pos hr',residualEnergyAtRank,if_pos hr]
    rw [← EuclideanSpace.real_norm_sq_eq,residualCoordinates_norm_sq,(action _).norm_map,column_norm Q j]
    have hcnorm := congrArg (fun x : E d => ‖x‖^2) hc
    rw [projectedCenter,(action _).norm_map] at hcnorm
    rw [hr'] at hcnorm
    rw [hcnorm]
    norm_num
  · have hr' : (reframedState A weight tape seed k hkd t j H Q).1 ≠ r := by
      rw [hrank]
      exact hr
    simp only [restrictedCoordinate,if_neg hr',residualEnergyAtRank,if_neg hr,zero_pow (by norm_num : 2≠0),
      Finset.sum_const_zero]

/-- The exact manuscript posterior covariance formula, for arbitrary measurable
adaptive queries and any old-past measurable residual reframe. -/
theorem rankStopped_conditional_second_moment (A : OracleAlgorithm d N S)
    (weight : Ω → ℝ) (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d)
    (t : ℕ) (ht : t ≤ N) (j : Fin d) (hstop : RankStopped A weight tape seed k hkd)
    (H : Transcript N → ResidualControls d) (hH : Measurable H)
    (r : Fin (d+1)) (hrd : r.val < d) (i : Fin (d-r.val)) :
    (orthogonalHaarProbability d)[(fun Q =>
      (restrictedCoordinate A weight tape seed k hkd t j H r i Q)^2) |
        pastSigma A weight tape seed t j] =ᵐ[orthogonalHaarProbability d]
    (fun Q => residualEnergyAtRank A weight tape seed k hkd t j r Q/((d-r.val:ℕ):ℝ)) := by
  apply conditional_square_eq_div_of_pair (d-r.val) (by omega)
    (pastSigma A weight tape seed t j) (measurable_history A weight tape seed t j).comap_le
    (restrictedCoordinate A weight tape seed k hkd t j H r)
  · exact fun l => restrictedCoordinate_square_integrable A weight tape seed k hkd t j H hH r l
  · exact residualEnergyAtRank_integrable A weight tape seed k hkd t ht j r
  · exact residualEnergyAtRank_stronglyMeasurable_past A weight tape seed k hkd t j r
  · exact Filter.Eventually.of_forall
      (restrictedCoordinate_sum_squares_eq_residualEnergy A weight tape seed k hkd t ht j H r)
  · exact fun l l' => restrictedCoordinate_conditional_squares_equal A weight tape seed k hkd
      t ht j hstop H hH r l l'

#print axioms residualEnergyAtRank_stronglyMeasurable_past
#print axioms restrictedCoordinate_sum_squares_eq_residualEnergy
#print axioms rankStopped_conditional_second_moment
end
end Task006.AdaptiveSphereIsotropy
