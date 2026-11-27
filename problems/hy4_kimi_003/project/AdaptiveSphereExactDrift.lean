import AdaptiveSphereEnergyDrift
import AdaptiveSpherePosteriorSecondMoment

/-! Exact conditional energy drift (L3), with the event of acquiring a new
independent measurement made explicit in the old transcript. -/
open MeasureTheory Set
open scoped Matrix RealInnerProductSpace

namespace Task006.AdaptiveSphereEnergyDrift
open Task006.Full Task006.Full.OracleAlgorithm
open Task006.HaarRebalancing Task006.AdaptiveSphereBlock
open Task006.AdaptiveSphereFrame Task006.AdaptiveSphereResidualFrame
open Task006.AdaptiveSphereState Task006.AdaptiveSphereAction
open Task006.AdaptiveSphereStopped Task006.AdaptiveSphereTranscript Task006.AdaptiveSphereMeasurable
open Task006.AdaptiveSphereMean Task006.AdaptiveSphereReframe Task006.AdaptiveSphereIsotropy
open Task006.AdaptiveSpherePrepared Task006.AdaptiveSphere
noncomputable section
variable {d N : ℕ} {S Ω : Type*} [MeasurableSpace S]

def activeResidualVariance (A : OracleAlgorithm d N S) (weight : Ω → ℝ) (tape : ℕ → Ω)
    (seed : S) (k : ℕ) (hkd : k ≤ d) (t : Fin N) (j : Fin d) (r : Fin d) :
    OrthogonalGroup d → ℝ :=
  (activeEvent A weight tape seed k hkd t j r).indicator
    (fun Q => (1-centerEnergy A weight tape seed k hkd t.val j Q)/((d:ℝ)-r.val))

theorem active_conditional_energy_exact (A : OracleAlgorithm d N S) (weight : Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d) (t : Fin N) (j : Fin d) (r : Fin d)
    (hstop : RankStopped A weight tape seed k hkd) :
    (orthogonalHaarProbability d)[activeCoordinateSquare A weight tape seed k hkd t j r |
      pastSigma A weight tape seed t.val j] =ᵐ[orthogonalHaarProbability d]
      activeResidualVariance A weight tape seed k hkd t j r := by
  have hxi := restrictedCoordinate_square_integrable A weight tape seed k hkd t.val j
    (queryPreparation A weight tape seed k hkd t) (queryPreparation_measurable A weight tape seed k hkd t)
    r.castSucc (residualPivot r)
  have hind := condExp_indicator (μ := orthogonalHaarProbability d) hxi
    (activeEvent_measurable_past A weight tape seed k hkd t j r)
  have hexact := rankStopped_conditional_second_moment A weight tape seed k hkd t.val (by omega) j hstop
    (queryPreparation A weight tape seed k hkd t) (queryPreparation_measurable A weight tape seed k hkd t)
    r.castSucc r.isLt (residualPivot r)
  filter_upwards [hind,hexact] with Q hi hx
  change ((orthogonalHaarProbability d)[(activeEvent A weight tape seed k hkd t j r).indicator
    (fun Q => (restrictedCoordinate A weight tape seed k hkd t.val j
      (queryPreparation A weight tape seed k hkd t) r.castSucc (residualPivot r) Q)^2) |
      pastSigma A weight tape seed t.val j]) Q = _
  rw [hi]
  by_cases hQ : Q ∈ activeEvent A weight tape seed k hkd t j r
  · have hrank : (actualState A weight tape seed k hkd t.val j Q).1 = r.castSucc := Fin.ext hQ.1
    simp only [Set.indicator_of_mem hQ,activeResidualVariance,hx]
    simp only [residualEnergyAtRank,if_pos hrank,Fin.val_castSucc,Nat.cast_sub (Nat.le_of_lt r.isLt),centerEnergy]
  · simp only [Set.indicator_of_notMem hQ,activeResidualVariance]

/-- Exact L3 as one conditional identity for the actual next query slot. Each
active rank r contributes (1-||C||²)/(d-r), and dependent queries contribute 0. -/
theorem actual_conditional_energy_increment_exact (A : OracleAlgorithm d N S) (weight : Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d) (t : Fin N) (j : Fin d)
    (hstop : RankStopped A weight tape seed k hkd) :
    (orthogonalHaarProbability d)[(fun Q => centerEnergy A weight tape seed k hkd (t.val+1) j Q -
      centerEnergy A weight tape seed k hkd t.val j Q) | pastSigma A weight tape seed t.val j]
      =ᵐ[orthogonalHaarProbability d]
      (fun Q => ∑ r : Fin d, activeResidualVariance A weight tape seed k hkd t j r Q) := by
  have hfun : (fun Q => centerEnergy A weight tape seed k hkd (t.val+1) j Q -
      centerEnergy A weight tape seed k hkd t.val j Q) =
      ∑ r : Fin d, activeCoordinateSquare A weight tape seed k hkd t j r := by
    funext Q
    simp only [Finset.sum_apply]
    exact energy_increment_as_coordinates A weight tape seed k hkd t j Q
  rw [hfun]
  have hsum := condExp_finsetSum (μ := orthogonalHaarProbability d) (s := Finset.univ)
    (f := fun r : Fin d => activeCoordinateSquare A weight tape seed k hkd t j r)
    (fun r _ => activeCoordinateSquare_integrable A weight tape seed k hkd t j r)
    (pastSigma A weight tape seed t.val j)
  have hall : ∀ᵐ Q ∂orthogonalHaarProbability d, ∀ r : Fin d,
      ((orthogonalHaarProbability d)[activeCoordinateSquare A weight tape seed k hkd t j r |
        pastSigma A weight tape seed t.val j]) Q = activeResidualVariance A weight tape seed k hkd t j r Q := by
    rw [ae_all_iff]
    exact fun r => active_conditional_energy_exact A weight tape seed k hkd t j r hstop
  filter_upwards [hsum,hall] with Q hs hh
  rw [hs]
  simp only [Finset.sum_apply]
  exact Finset.sum_congr rfl (fun r _ => hh r)

#print axioms active_conditional_energy_exact
#print axioms actual_conditional_energy_increment_exact
end
end Task006.AdaptiveSphereEnergyDrift
