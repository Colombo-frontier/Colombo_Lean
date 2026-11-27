import AdaptiveSphereEnergyDrift

/-! Complete fixed-exogenous-parameter stopped-energy bound for the canonical
arbitrary measurable adaptive observation policy. No local or terminal posterior
energy inequality is assumed: local bounds come from actual Haar swaps. -/
open MeasureTheory Set
open scoped Matrix RealInnerProductSpace

namespace Task006.AdaptiveSphereStoppedEnergy
open Task006.Full Task006.Full.OracleAlgorithm
open Task006.HaarRebalancing Task006.AdaptiveSphereBlock
open Task006.AdaptiveSphereFrame Task006.AdaptiveSphereResidualFrame
open Task006.AdaptiveSphereState Task006.AdaptiveSphereAction
open Task006.AdaptiveSphereStopped Task006.AdaptiveSphereInvariance
open Task006.AdaptiveSphereTranscript Task006.AdaptiveSphereMeasurable
open Task006.AdaptiveSphereGeometry Task006.PosteriorCenter Task006.AdaptiveSphereActualStep
open Task006.AdaptiveSphereMean Task006.AdaptiveSphereEnergyDrift Task006.StoppedEnergy
noncomputable section
variable {d N : ℕ} {S Ω : Type*} [MeasurableSpace S]

theorem actualRank_measurable (A : OracleAlgorithm d N S) (weight : Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d) (t : ℕ) (j : Fin d) :
    Measurable (actualRank A weight tape seed k hkd t j) := by
  have hv : Measurable (fun r : Fin (d+1) => r.val) := measurable_of_countable _
  exact hv.comp (measurable_fst.comp (measurable_actualState A weight tape seed k hkd t j))

theorem actualRank_le_cap (A : OracleAlgorithm d N S) (weight : Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d) (t : ℕ) (j : Fin d)
    (Q : OrthogonalGroup d) : actualRank A weight tape seed k hkd t j Q ≤ k :=
  frameFromTranscript_rank_cap A weight tape seed k hkd t _

theorem centerEnergy_integrable (A : OracleAlgorithm d N S) (weight : Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d) (t : ℕ) (ht : t ≤ N) (j : Fin d) :
    Integrable (centerEnergy A weight tape seed k hkd t j) (orthogonalHaarProbability d) := by
  have hm : Measurable (centerEnergy A weight tape seed k hkd t j) :=
    (actualCenter_measurable A weight tape seed k hkd t j).norm.pow_const 2
  apply Integrable.of_bound hm.aestronglyMeasurable 1
  apply Filter.Eventually.of_forall
  intro Q
  have hc := actualCenter_norm_le_one A weight tape seed k hkd t ht j Q
  change ‖‖actualCenter A weight tape seed k hkd t j Q‖^2‖ ≤ 1
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  nlinarith [norm_nonneg (actualCenter A weight tape seed k hkd t j Q)]

theorem actualPotential_integrable (A : OracleAlgorithm d N S) (weight : Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d) (t : ℕ) (j : Fin d) :
    Integrable (fun Q => rankPotential d (actualRank A weight tape seed k hkd t j Q))
      (orthogonalHaarProbability d) := by
  have hp : Measurable (rankPotential d) := measurable_of_countable _
  have hm := hp.comp (actualRank_measurable A weight tape seed k hkd t j)
  apply Integrable.of_bound hm.aestronglyMeasurable (rankPotential d k)
  apply Filter.Eventually.of_forall
  intro Q
  have hk := actualRank_le_cap A weight tape seed k hkd t j Q
  have hlo := rankPotential_mono_below_dimension d 0
    (actualRank A weight tape seed k hkd t j Q) (Nat.zero_le _) (hk.trans hkd)
  have hhi := rankPotential_mono_below_dimension d
    (actualRank A weight tape seed k hkd t j Q) k hk hkd
  rw [rankPotential_zero] at hlo
  change ‖rankPotential d (actualRank A weight tape seed k hkd t j Q)‖ ≤ _
  rw [Real.norm_eq_abs,abs_of_nonneg hlo]
  exact hhi

/-- Main actual stopped-energy theorem, for each independent seed and sample
tape. Invariance and isotropy are internally proved for the real adaptive run. -/
theorem rankStopped_expected_center_energy_le (A : OracleAlgorithm d N S)
    (weight : Ω → ℝ) (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d)
    (j : Fin d) (hstop : RankStopped A weight tape seed k hkd) :
    (∫ Q, ‖actualCenter A weight tape seed k hkd N j Q‖^2 ∂orthogonalHaarProbability d) ≤
      rankPotential d k := by
  apply expected_energy_le_rankPotential_of_expected_increments N d k hkd
    (fun t => centerEnergy A weight tape seed k hkd t j)
    (fun t => actualRank A weight tape seed k hkd t j)
  · exact fun t ht => centerEnergy_integrable A weight tape seed k hkd t ht j
  · exact fun t _ => actualPotential_integrable A weight tape seed k hkd t j
  · apply Filter.Eventually.of_forall
    intro Q
    simp [centerEnergy,actualCenter,centerFromTranscript]
  · apply Filter.Eventually.of_forall
    intro Q
    rfl
  · exact Filter.Eventually.of_forall (actualRank_le_cap A weight tape seed k hkd N j)
  · intro t ht
    exact actual_expected_one_step_drift A weight tape seed k hkd ⟨t,ht⟩ j hstop

/-- The constructed observer from ANY original canonical policy satisfies the
energy bound. This is the theorem used by the lower-bound integration. -/
theorem stoppedObserver_expected_center_energy_le (A : OracleAlgorithm d N S)
    (weight : Ω → ℝ) (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d) (j : Fin d) :
    (∫ Q, ‖actualCenter (stoppedObserver A weight tape seed k hkd) weight tape () k hkd N j Q‖^2
      ∂orthogonalHaarProbability d) ≤ rankPotential d k :=
  rankStopped_expected_center_energy_le _ _ _ _ _ _ j
    (stoppedObserver_rankStopped A weight tape seed k hkd)

#print axioms centerEnergy_integrable
#print axioms actualPotential_integrable
#print axioms rankStopped_expected_center_energy_le
#print axioms stoppedObserver_expected_center_energy_le
end
end Task006.AdaptiveSphereStoppedEnergy
