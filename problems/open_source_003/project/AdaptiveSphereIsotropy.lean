import AdaptiveSphereReframe
import AdaptiveSphereMean

/-! Genuine conditional isotropy at every rank, including an arbitrary old-past
measurable residual reframe. This is applied to the prepared next-query frame. -/
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
open Task006.AdaptiveSphereMean Task006.AdaptiveSphereReframe
noncomputable section
variable {d N : ℕ} {S Ω : Type*} [MeasurableSpace S]

theorem measurable_reframedState (A : OracleAlgorithm d N S) (weight : Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d) (t : ℕ) (j : Fin d)
    (H : Transcript N → ResidualControls d) (hH : Measurable H) :
    Measurable (reframedState A weight tape seed k hkd t j H) := by
  have hm := (reframe_joint_measurable (d := d)).comp
    ((measurable_actualState A weight tape seed k hkd t j).prodMk
      (hH.comp (measurable_history A weight tape seed t j)))
  change Measurable (fun Q => reframe (actualState A weight tape seed k hkd t j Q)
    (H (history A weight tape seed t j Q)))
  simpa only [Function.comp_def] using hm

def restrictedCoordinate (A : OracleAlgorithm d N S) (weight : Ω → ℝ) (tape : ℕ → Ω)
    (seed : S) (k : ℕ) (hkd : k ≤ d) (t : ℕ) (j : Fin d)
    (H : Transcript N → ResidualControls d) (r : Fin (d+1)) (i : Fin (d-r.val))
    (Q : OrthogonalGroup d) : ℝ :=
  if (reframedState A weight tape seed k hkd t j H Q).1 = r then
    residualCoordinates r.val (by omega)
      (action (reframedState A weight tape seed k hkd t j H Q).2⁻¹ (column Q j)) i
  else 0

theorem restrictedCoordinate_measurable (A : OracleAlgorithm d N S) (weight : Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d) (t : ℕ) (j : Fin d)
    (H : Transcript N → ResidualControls d) (hH : Measurable H)
    (r : Fin (d+1)) (i : Fin (d-r.val)) :
    Measurable (restrictedCoordinate A weight tape seed k hkd t j H r i) := by
  have hs := measurable_reframedState A weight tape seed k hkd t j H hH
  have hr := measurable_fst.comp hs
  have hB := measurable_snd.comp hs
  have hc := orthogonal_inverse_action_measurable.comp (hB.prodMk (measurable_column j))
  have hres := (continuous_residualCoordinates r.val (by omega)).measurable.comp hc
  have hcoord := (EuclideanSpace.proj i).continuous.measurable.comp hres
  change Measurable (fun Q => if (reframedState A weight tape seed k hkd t j H Q).1 = r then
    residualCoordinates r.val (by omega)
      (action (reframedState A weight tape seed k hkd t j H Q).2⁻¹ (column Q j)) i else 0)
  exact Measurable.ite (hr (measurableSet_singleton r)) hcoord measurable_const

theorem restrictedCoordinate_abs_le_one (A : OracleAlgorithm d N S) (weight : Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d) (t : ℕ) (j : Fin d)
    (H : Transcript N → ResidualControls d) (r : Fin (d+1)) (i : Fin (d-r.val))
    (Q : OrthogonalGroup d) :
    |restrictedCoordinate A weight tape seed k hkd t j H r i Q| ≤ 1 := by
  unfold restrictedCoordinate
  split_ifs
  · have hb := PiLp.norm_apply_le
      (action (reframedState A weight tape seed k hkd t j H Q).2⁻¹ (column Q j))
      (indexSplit d r.val (by omega) (Sum.inr i))
    rw [(action _).norm_map,column_norm Q j] at hb
    exact hb
  · norm_num

theorem restrictedCoordinate_square_integrable (A : OracleAlgorithm d N S) (weight : Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d) (t : ℕ) (j : Fin d)
    (H : Transcript N → ResidualControls d) (hH : Measurable H)
    (r : Fin (d+1)) (i : Fin (d-r.val)) :
    Integrable (fun Q => (restrictedCoordinate A weight tape seed k hkd t j H r i Q)^2)
      (orthogonalHaarProbability d) := by
  apply Integrable.of_bound
    ((restrictedCoordinate_measurable A weight tape seed k hkd t j H hH r i).pow_const 2).aestronglyMeasurable 1
  apply Filter.Eventually.of_forall
  intro Q
  have h := restrictedCoordinate_abs_le_one A weight tape seed k hkd t j H r i Q
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  have hbounds := abs_le.mp h
  nlinarith

theorem rotated_residualCoordinates (r : Fin (d+1)) (B : OrthogonalGroup d)
    (g : ResidualControls d) (θ : E d) :
    residualCoordinates r.val (by omega)
      (action B⁻¹ (action (rotateAtState (r,B) g) θ)) =
      action (g r) (residualCoordinates r.val (by omega) (action B⁻¹ θ)) := by
  rw [rotateAtState,action_mul,action_mul,action_inverse_cancel_left,
    blockOrthogonal_action_residual]

/-- Every rank-restricted residual coordinate has the same conditional second
moment, derived from a concrete measure-preserving adaptive swap. -/
theorem restrictedCoordinate_conditional_squares_equal (A : OracleAlgorithm d N S)
    (weight : Ω → ℝ) (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d)
    (t : ℕ) (ht : t ≤ N) (j : Fin d) (hstop : RankStopped A weight tape seed k hkd)
    (H : Transcript N → ResidualControls d) (hH : Measurable H)
    (r : Fin (d+1)) (i l : Fin (d-r.val)) :
    (orthogonalHaarProbability d)[(fun Q =>
      (restrictedCoordinate A weight tape seed k hkd t j H r i Q)^2) |
        pastSigma A weight tape seed t j] =ᵐ[orthogonalHaarProbability d]
    (orthogonalHaarProbability d)[(fun Q =>
      (restrictedCoordinate A weight tape seed k hkd t j H r l Q)^2) |
        pastSigma A weight tape seed t j] := by
  let g : ResidualControls d := Function.update (fun _ => 1) r (swapOrthogonal i l)
  let T := reframedOrbit A weight tape seed k hkd t j H g
  have hmp := reframedOrbit_measurePreserving A weight tape seed k hkd t ht j hstop H hH g
  have hfix := reframedOrbit_fixes_history A weight tape seed k hkd t ht j hstop H g
  have hstate (Q : OrthogonalGroup d) :
      reframedState A weight tape seed k hkd t j H (T Q) =
        reframedState A weight tape seed k hkd t j H Q := by
    change reframe (frameFromTranscript A weight tape seed k hkd t
      (history A weight tape seed t j (T Q))) (H (history A weight tape seed t j (T Q))) = _
    rw [hfix]
    rfl
  have hcomp (Q : OrthogonalGroup d) :
      restrictedCoordinate A weight tape seed k hkd t j H r i (T Q) =
        restrictedCoordinate A weight tape seed k hkd t j H r l Q := by
    unfold restrictedCoordinate
    rw [hstate]
    by_cases hr : (reframedState A weight tape seed k hkd t j H Q).1 = r
    · rw [if_pos hr,if_pos hr]
      have hstateQ : reframedState A weight tape seed k hkd t j H Q =
          (r,(reframedState A weight tape seed k hkd t j H Q).2) := by
        exact Prod.ext hr rfl
      have hcol : column (T Q) j = action
          (rotateAtState (reframedState A weight tape seed k hkd t j H Q) g) (column Q j) :=
        column_mul_action _ Q j
      rw [hcol,hstateQ]
      rw [rotated_residualCoordinates]
      simp only [g,Function.update_self]
      exact swapOrthogonal_action_first i l _
    · rw [if_neg hr,if_neg hr]
  apply condExp_transport_of_invariant_map (pastSigma A weight tape seed t j)
    (measurable_history A weight tape seed t j).comap_le T hmp
  · intro s hs
    rcases hs with ⟨a,ha,rfl⟩
    ext Q
    change history A weight tape seed t j (T Q) ∈ a ↔ _
    rw [hfix]
    rfl
  · exact restrictedCoordinate_square_integrable A weight tape seed k hkd t j H hH r i
  · exact restrictedCoordinate_square_integrable A weight tape seed k hkd t j H hH r l
  · intro Q
    rw [hcomp]

#print axioms measurable_reframedState
#print axioms restrictedCoordinate_measurable
#print axioms restrictedCoordinate_abs_le_one
#print axioms rotated_residualCoordinates
#print axioms restrictedCoordinate_conditional_squares_equal
end
end Task006.AdaptiveSphereIsotropy
