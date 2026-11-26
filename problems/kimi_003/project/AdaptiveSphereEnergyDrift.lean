import AdaptiveSpherePrepared
import AdaptiveSphereConditionalBound
import PosteriorEnergyPartition
import StoppedEnergyExpected

/-! One-step expected energy drift for the ACTUAL stopped transcript, proved
from concrete adaptive swaps on its old-past active-rank events. -/
open MeasureTheory Set
open scoped Matrix RealInnerProductSpace

namespace Task006.AdaptiveSphereEnergyDrift
open Task006.Full Task006.Full.OracleAlgorithm
open Task006.HaarRebalancing Task006.AdaptiveSphereBlock
open Task006.AdaptiveSphereFrame Task006.AdaptiveSphereResidualFrame
open Task006.AdaptiveSphereState Task006.AdaptiveSphereAction
open Task006.AdaptiveSphereStopped Task006.AdaptiveSphereInvariance
open Task006.AdaptiveSphereTranscript Task006.AdaptiveSphereMeasurable
open Task006.AdaptiveSphereCoordinateRotations Task006.AdaptiveSphereGeometry
open Task006.PosteriorCenter Task006.AdaptiveSphereActualStep Task006.AdaptiveSphere
open Task006.AdaptiveSphereMean Task006.AdaptiveSphereReframe Task006.AdaptiveSphereIsotropy
open Task006.AdaptiveSpherePrepared Task006.PosteriorEnergyPartition Task006.StoppedEnergy
noncomputable section
variable {d N : ℕ} {S Ω : Type*} [MeasurableSpace S]

def queryVector (A : OracleAlgorithm d N S) (weight : Ω → ℝ) (tape : ℕ → Ω)
    (seed : S) (t : Fin N) (h : Transcript N) : E d :=
  effectiveVector weight tape (A.action t seed h)

def activeEvent (A : OracleAlgorithm d N S) (weight : Ω → ℝ) (tape : ℕ → Ω)
    (seed : S) (k : ℕ) (hkd : k ≤ d) (t : Fin N) (j : Fin d) (r : Fin d) :
    Set (OrthogonalGroup d) :=
  {Q | activeRank (actualState A weight tape seed k hkd t.val j Q)
    (queryVector A weight tape seed t (history A weight tape seed t.val j Q)) k r}

theorem queryVector_measurable (A : OracleAlgorithm d N S) (weight : Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) (t : Fin N) : Measurable (queryVector A weight tape seed t) := by
  have hin : Measurable (fun h : Transcript N => (seed,h)) := measurable_const.prodMk measurable_id
  exact (measurable_effectiveVector weight tape).comp ((A.action_measurable t).comp hin)

theorem activeEvent_measurable_past (A : OracleAlgorithm d N S) (weight : Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d) (t : Fin N) (j : Fin d) (r : Fin d) :
    MeasurableSet[pastSigma A weight tape seed t.val j] (activeEvent A weight tape seed k hkd t j r) := by
  have hs := measurable_frameFromTranscript A weight tape seed k hkd t.val
  have hval : Measurable (fun x : Fin (d+1) => x.val) := measurable_of_countable _
  have hrank := hval.comp (measurable_fst.comp hs)
  have hq := queryVector_measurable A weight tape seed t
  have hcoords := orthogonal_inverse_action_measurable.comp ((measurable_snd.comp hs).prodMk hq)
  have hres := (continuous_residualCoordinates r.val (Nat.le_of_lt r.isLt)).measurable.comp hcoords
  have hevent : MeasurableSet {h : Transcript N |
      activeRank (frameFromTranscript A weight tape seed k hkd t.val h)
        (queryVector A weight tape seed t h) k r} := by
    unfold activeRank
    exact (hrank (measurableSet_singleton r.val)).inter
      ((MeasurableSet.const (r.val<k)).inter (hres (measurableSet_singleton 0)).compl)
  exact ⟨_,hevent,rfl⟩

theorem prepared_coordinate_eq_next_inner (A : OracleAlgorithm d N S) (weight : Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d) (t : Fin N) (j : Fin d) (r : Fin d)
    (Q : OrthogonalGroup d) (hQ : Q ∈ activeEvent A weight tape seed k hkd t j r) :
    restrictedCoordinate A weight tape seed k hkd t.val j
      (queryPreparation A weight tape seed k hkd t) r.castSucc (residualPivot r) Q =
    inner ℝ (column Q j) (frameVector (actualState A weight tape seed k hkd (t.val+1) j Q).2 r) := by
  have hrank : (reframedState A weight tape seed k hkd t.val j
      (queryPreparation A weight tape seed k hkd t) Q).1 = r.castSucc :=
    Fin.ext hQ.1
  rw [restrictedCoordinate,if_pos hrank,prepared_actual_frame_eq_next]
  have hi : indexSplit d r.val (Nat.le_of_lt r.isLt) (Sum.inr (residualPivot r)) = r := by
    apply Fin.ext
    rw [indexSplit_right_val]
    simp [residualPivot]
  change (action (actualState A weight tape seed k hkd (t.val+1) j Q).2⁻¹ (column Q j))
    (indexSplit d r.val (Nat.le_of_lt r.isLt) (Sum.inr (residualPivot r))) = _
  rw [hi,coordinate_as_inner]

#print axioms queryVector_measurable
#print axioms activeEvent_measurable_past
#print axioms prepared_coordinate_eq_next_inner
end
end Task006.AdaptiveSphereEnergyDrift

namespace Task006.AdaptiveSphereEnergyDrift
open Task006.Full Task006.Full.OracleAlgorithm
open Task006.HaarRebalancing Task006.AdaptiveSphereBlock
open Task006.AdaptiveSphereFrame Task006.AdaptiveSphereResidualFrame
open Task006.AdaptiveSphereState Task006.AdaptiveSphereAction
open Task006.AdaptiveSphereStopped Task006.AdaptiveSphereInvariance
open Task006.AdaptiveSphereTranscript Task006.AdaptiveSphereMeasurable
open Task006.AdaptiveSphereGeometry Task006.PosteriorCenter Task006.AdaptiveSphereActualStep
open Task006.AdaptiveSphereMean Task006.AdaptiveSphereReframe Task006.AdaptiveSphereIsotropy
open Task006.AdaptiveSpherePrepared Task006.PosteriorEnergyPartition Task006.StoppedEnergy
noncomputable section
variable {d N : ℕ} {S Ω : Type*} [MeasurableSpace S]

def centerEnergy (A : OracleAlgorithm d N S) (weight : Ω → ℝ) (tape : ℕ → Ω)
    (seed : S) (k : ℕ) (hkd : k ≤ d) (t : ℕ) (j : Fin d) (Q : OrthogonalGroup d) : ℝ :=
  ‖actualCenter A weight tape seed k hkd t j Q‖^2

def actualRank (A : OracleAlgorithm d N S) (weight : Ω → ℝ) (tape : ℕ → Ω)
    (seed : S) (k : ℕ) (hkd : k ≤ d) (t : ℕ) (j : Fin d) (Q : OrthogonalGroup d) : ℕ :=
  (actualState A weight tape seed k hkd t j Q).1.val

def activeCoordinateSquare (A : OracleAlgorithm d N S) (weight : Ω → ℝ) (tape : ℕ → Ω)
    (seed : S) (k : ℕ) (hkd : k ≤ d) (t : Fin N) (j : Fin d) (r : Fin d) :
    OrthogonalGroup d → ℝ :=
  (activeEvent A weight tape seed k hkd t j r).indicator (fun Q =>
    (restrictedCoordinate A weight tape seed k hkd t.val j
      (queryPreparation A weight tape seed k hkd t) r.castSucc (residualPivot r) Q)^2)

def activePotentialIncrement (A : OracleAlgorithm d N S) (weight : Ω → ℝ) (tape : ℕ → Ω)
    (seed : S) (k : ℕ) (hkd : k ≤ d) (t : Fin N) (j : Fin d) (r : Fin d) :
    OrthogonalGroup d → ℝ :=
  (activeEvent A weight tape seed k hkd t j r).indicator (fun _ => 1/((d:ℝ)-r.val))

theorem energy_increment_as_coordinates (A : OracleAlgorithm d N S) (weight : Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d) (t : Fin N) (j : Fin d)
    (Q : OrthogonalGroup d) :
    centerEnergy A weight tape seed k hkd (t.val+1) j Q -
      centerEnergy A weight tape seed k hkd t.val j Q =
      ∑ r : Fin d, activeCoordinateSquare A weight tape seed k hkd t j r Q := by
  classical
  unfold centerEnergy
  rw [actualCenter_eq_projected A weight tape seed k hkd (t.val+1) (by omega) j Q,
    actualCenter_eq_projected A weight tape seed k hkd t.val (by omega) j Q,
    actualState_succ,energy_increment_partition]
  apply Finset.sum_congr rfl
  intro r hr
  by_cases ha : Q ∈ activeEvent A weight tape seed k hkd t j r
  · have hactive : activeRank (actualState A weight tape seed k hkd t.val j Q)
        (queryVector A weight tape seed t (history A weight tape seed t.val j Q)) k r := ha
    dsimp only [queryVector] at hactive
    rw [if_pos hactive]
    change _ = (activeEvent A weight tape seed k hkd t j r).indicator _ Q
    rw [Set.indicator_of_mem ha,prepared_coordinate_eq_next_inner A weight tape seed k hkd t j r Q ha,
      actualState_succ]
  · have hactive : ¬activeRank (actualState A weight tape seed k hkd t.val j Q)
        (queryVector A weight tape seed t (history A weight tape seed t.val j Q)) k r := ha
    dsimp only [queryVector] at hactive
    rw [if_neg hactive]
    exact (Set.indicator_of_notMem ha _).symm

theorem potential_increment_as_events (A : OracleAlgorithm d N S) (weight : Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d) (t : Fin N) (j : Fin d)
    (Q : OrthogonalGroup d) :
    rankPotential d (actualRank A weight tape seed k hkd (t.val+1) j Q) -
      rankPotential d (actualRank A weight tape seed k hkd t.val j Q) =
      ∑ r : Fin d, activePotentialIncrement A weight tape seed k hkd t j r Q := by
  classical
  unfold actualRank
  rw [actualState_succ,potential_increment_partition]
  apply Finset.sum_congr rfl
  intro r hr
  by_cases ha : Q ∈ activeEvent A weight tape seed k hkd t j r
  · have hactive : activeRank (actualState A weight tape seed k hkd t.val j Q)
        (queryVector A weight tape seed t (history A weight tape seed t.val j Q)) k r := ha
    dsimp only [queryVector] at hactive
    rw [if_pos hactive]
    change _ = (activeEvent A weight tape seed k hkd t j r).indicator
      (fun _ : OrthogonalGroup d => 1/((d:ℝ)-r.val)) Q
    rw [Set.indicator_of_mem ha]
  · have hactive : ¬activeRank (actualState A weight tape seed k hkd t.val j Q)
        (queryVector A weight tape seed t (history A weight tape seed t.val j Q)) k r := ha
    dsimp only [queryVector] at hactive
    rw [if_neg hactive]
    exact (Set.indicator_of_notMem ha _).symm

theorem activeCoordinateSquare_integrable (A : OracleAlgorithm d N S) (weight : Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d) (t : Fin N) (j : Fin d) (r : Fin d) :
    Integrable (activeCoordinateSquare A weight tape seed k hkd t j r) (orthogonalHaarProbability d) := by
  apply (restrictedCoordinate_square_integrable A weight tape seed k hkd t.val j
    (queryPreparation A weight tape seed k hkd t) (queryPreparation_measurable A weight tape seed k hkd t)
    r.castSucc (residualPivot r)).indicator
  exact (measurable_history A weight tape seed t.val j).comap_le _
    (activeEvent_measurable_past A weight tape seed k hkd t j r)

theorem activePotentialIncrement_integrable (A : OracleAlgorithm d N S) (weight : Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d) (t : Fin N) (j : Fin d) (r : Fin d) :
    Integrable (activePotentialIncrement A weight tape seed k hkd t j r) (orthogonalHaarProbability d) := by
  apply (integrable_const _).indicator
  exact (measurable_history A weight tape seed t.val j).comap_le _
    (activeEvent_measurable_past A weight tape seed k hkd t j r)

theorem active_expected_energy_le_potential (A : OracleAlgorithm d N S) (weight : Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d) (t : Fin N) (j : Fin d) (r : Fin d)
    (hstop : RankStopped A weight tape seed k hkd) :
    (∫ Q, activeCoordinateSquare A weight tape seed k hkd t j r Q ∂orthogonalHaarProbability d) ≤
      ∫ Q, activePotentialIncrement A weight tape seed k hkd t j r Q ∂orthogonalHaarProbability d := by
  have he := (measurable_history A weight tape seed t.val j).comap_le _
    (activeEvent_measurable_past A weight tape seed k hkd t j r)
  unfold activeCoordinateSquare activePotentialIncrement
  rw [integral_indicator he,integral_indicator he]
  have h := restrictedCoordinate_event_square_le A weight tape seed k hkd t.val (by omega) j hstop
    (queryPreparation A weight tape seed k hkd t) (queryPreparation_measurable A weight tape seed k hkd t)
    r.castSucc r.isLt (residualPivot r) (activeEvent A weight tape seed k hkd t j r)
    (activeEvent_measurable_past A weight tape seed k hkd t j r)
  simpa only [Fin.val_castSucc,Nat.cast_sub (Nat.le_of_lt r.isLt)] using h

theorem actual_expected_one_step_drift (A : OracleAlgorithm d N S) (weight : Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d) (t : Fin N) (j : Fin d)
    (hstop : RankStopped A weight tape seed k hkd) :
    (∫ Q, centerEnergy A weight tape seed k hkd (t.val+1) j Q -
      centerEnergy A weight tape seed k hkd t.val j Q ∂orthogonalHaarProbability d) ≤
    ∫ Q, rankPotential d (actualRank A weight tape seed k hkd (t.val+1) j Q) -
      rankPotential d (actualRank A weight tape seed k hkd t.val j Q) ∂orthogonalHaarProbability d := by
  simp_rw [energy_increment_as_coordinates,potential_increment_as_events]
  rw [integral_finsetSum _ (fun r _ => activeCoordinateSquare_integrable A weight tape seed k hkd t j r),
    integral_finsetSum _ (fun r _ => activePotentialIncrement_integrable A weight tape seed k hkd t j r)]
  exact Finset.sum_le_sum (fun r _ => active_expected_energy_le_potential A weight tape seed k hkd t j r hstop)

#print axioms energy_increment_as_coordinates
#print axioms potential_increment_as_events
#print axioms active_expected_energy_le_potential
#print axioms actual_expected_one_step_drift
end
end Task006.AdaptiveSphereEnergyDrift
