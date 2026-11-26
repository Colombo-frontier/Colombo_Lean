import AdaptiveSphereIsotropy

/-! Preparing the next query direction is an actual measurable residual
reframe of the OLD posterior. Its rank remains the old rank. -/
open MeasureTheory Set
open scoped Matrix RealInnerProductSpace

namespace Task006.AdaptiveSpherePrepared
open Task006.Full Task006.Full.OracleAlgorithm
open Task006.HaarRebalancing Task006.AdaptiveSphereBlock
open Task006.AdaptiveSphereFrame Task006.AdaptiveSphereResidualFrame
open Task006.AdaptiveSphereState Task006.AdaptiveSphereAction
open Task006.AdaptiveSphereStopped Task006.AdaptiveSphereInvariance
open Task006.AdaptiveSphereTranscript Task006.AdaptiveSphereMeasurable
open Task006.AdaptiveSphereCoordinateRotations Task006.AdaptiveSphereGeometry
open Task006.PosteriorCenter Task006.AdaptiveSphereActualStep Task006.AdaptiveSphere
open Task006.AdaptiveSphereMean Task006.AdaptiveSphereReframe Task006.AdaptiveSphereIsotropy
noncomputable section
variable {d N : ℕ} {S Ω : Type*} [MeasurableSpace S]

def preparationControls (k : ℕ) (hkd : k ≤ d) (B : OrthogonalGroup d)
    (q : E d) : ResidualControls d := fun r =>
  if hr : r.val < k then
    residualHouseholder (⟨r.val,by omega⟩ : Fin d) (action B⁻¹ q)
  else 1

theorem preparationControls_measurable (k : ℕ) (hkd : k ≤ d) :
    Measurable (fun p : OrthogonalGroup d × E d => preparationControls k hkd p.1 p.2) := by
  apply measurable_pi_lambda
  intro r
  by_cases hr : r.val < k
  · have hm := (measurable_residualHouseholder (⟨r.val,by omega⟩ : Fin d)).comp
      orthogonal_inverse_action_measurable
    simpa only [preparationControls,dif_pos hr,Function.comp_def] using hm
  · simpa only [preparationControls,dif_neg hr] using
      (measurable_const : Measurable (fun _ : OrthogonalGroup d × E d => (1 : OrthogonalGroup (d-r.val))))

theorem preparation_frame_eq_next (k : ℕ) (hkd : k ≤ d) (state : FrameState d) (q : E d) :
    (reframe state (preparationControls k hkd state.2 q)).2 =
      (stateStep k hkd state q).2 := by
  by_cases hr : state.1.val < k
  · let pivot : Fin d := ⟨state.1.val,by omega⟩
    by_cases hx : residualCoordinates state.1.val (by omega) (action state.2⁻¹ q) = 0
    · simp only [reframe,preparationControls,dif_pos hr,stateStep,if_pos hx,
        residualHouseholder,blockOrthogonal_one,mul_one]
    · simp only [reframe,preparationControls,dif_pos hr,stateStep,if_neg hx,
        residualUpdate,fullResidualStep]
  · simp only [reframe,preparationControls,dif_neg hr,stateStep,blockOrthogonal_one,mul_one]

def queryPreparation (A : OracleAlgorithm d N S) (weight : Ω → ℝ) (tape : ℕ → Ω)
    (seed : S) (k : ℕ) (hkd : k ≤ d) (t : Fin N) (h : Transcript N) : ResidualControls d :=
  preparationControls k hkd (frameFromTranscript A weight tape seed k hkd t.val h).2
    (effectiveVector weight tape (A.action t seed h))

theorem queryPreparation_measurable (A : OracleAlgorithm d N S) (weight : Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d) (t : Fin N) :
    Measurable (queryPreparation A weight tape seed k hkd t) := by
  have hB := measurable_snd.comp (measurable_frameFromTranscript A weight tape seed k hkd t.val)
  have hin : Measurable (fun h : Transcript N => (seed,h)) := measurable_const.prodMk measurable_id
  have hq := (measurable_effectiveVector weight tape).comp ((A.action_measurable t).comp hin)
  have hr := (preparationControls_measurable k hkd).comp (hB.prodMk hq)
  change Measurable (fun h => preparationControls k hkd
    (frameFromTranscript A weight tape seed k hkd t.val h).2
    (effectiveVector weight tape (A.action t seed h)))
  simpa only [Function.comp_def] using hr

theorem prepared_actual_frame_eq_next (A : OracleAlgorithm d N S) (weight : Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d) (t : Fin N)
    (j : Fin d) (Q : OrthogonalGroup d) :
    (reframedState A weight tape seed k hkd t.val j
      (queryPreparation A weight tape seed k hkd t) Q).2 =
      (actualState A weight tape seed k hkd (t.val+1) j Q).2 := by
  rw [actualState_succ]
  exact preparation_frame_eq_next k hkd _ _

#print axioms preparationControls_measurable
#print axioms preparation_frame_eq_next
#print axioms queryPreparation_measurable
#print axioms prepared_actual_frame_eq_next
end
end Task006.AdaptiveSpherePrepared
