import AdaptiveSpherePosteriorSecondMoment

/-! Actual regular conditional distributions and their adaptive residual
rotation laws. This file uses Mathlib's genuine condDistrib disintegration;
no claimed conditional-law axiom is introduced. -/
open MeasureTheory Set ProbabilityTheory
open scoped Matrix RealInnerProductSpace

namespace Task006.AdaptiveSphereKernel
noncomputable section

/-- A measure-preserving observable-fixing map induces the corresponding
rotation law of the actual regular conditional distribution. -/
theorem condDistrib_map_eq_of_preserving_observable
    {W H V : Type*} [MeasurableSpace W] [MeasurableSpace H]
    [MeasurableSpace V] [StandardBorelSpace V] [Nonempty V]
    (μ : Measure W) [IsFiniteMeasure μ]
    (obs : W → H) (hobs : Measurable obs) (Y : W → V) (hY : Measurable Y)
    (T : W → W) (hT : MeasurePreserving T μ μ)
    (U : V → V) (hU : Measurable U)
    (hfix : ∀ w, obs (T w) = obs w) (hcomp : ∀ w, Y (T w) = U (Y w)) :
    (condDistrib Y obs μ).map U =ᵐ[μ.map obs] condDistrib Y obs μ := by
  have hobsmap : AEMeasurable obs (μ.map T) := by rw [hT.map_eq]; exact hobs.aemeasurable
  have hYmap : AEMeasurable Y (μ.map T) := by rw [hT.map_eq]; exact hY.aemeasurable
  have hm := condDistrib_map (X := obs) (Y := Y) (ν := μ) hobsmap hYmap hT.measurable.aemeasurable
  have ho : obs ∘ T = obs := funext hfix
  have hy : Y ∘ T = U ∘ Y := funext hcomp
  simp only [hT.map_eq,ho,hy] at hm
  exact (hm.trans (condDistrib_comp obs hY.aemeasurable hU)).symm

open Task006.Full Task006.Full.OracleAlgorithm
open Task006.HaarRebalancing Task006.AdaptiveSphereBlock
open Task006.AdaptiveSphereFrame Task006.AdaptiveSphereResidualFrame
open Task006.AdaptiveSphereState Task006.AdaptiveSphereAction
open Task006.AdaptiveSphereStopped Task006.AdaptiveSphereInvariance
open Task006.AdaptiveSphereTranscript Task006.AdaptiveSphereMeasurable
open Task006.AdaptiveSphereGeometry Task006.PosteriorCenter Task006.AdaptiveSphereActualStep
open Task006.AdaptiveSphereMean Task006.AdaptiveSphereReframe Task006.AdaptiveSphere
open Task006.AdaptiveSphereIsotropy Task006.PosteriorResidualEnergy
variable {d N : ℕ} {S Ω : Type*} [MeasurableSpace S]

def rankResidual (A : OracleAlgorithm d N S) (weight : Ω → ℝ) (tape : ℕ → Ω)
    (seed : S) (k : ℕ) (hkd : k ≤ d) (t : ℕ) (j : Fin d)
    (H : Transcript N → ResidualControls d) (r : Fin (d+1))
    (Q : OrthogonalGroup d) : E (d-r.val) :=
  if (reframedState A weight tape seed k hkd t j H Q).1 = r then
    residualCoordinates r.val (by omega)
      (action (reframedState A weight tape seed k hkd t j H Q).2⁻¹ (column Q j))
  else 0

theorem rankResidual_measurable (A : OracleAlgorithm d N S) (weight : Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d) (t : ℕ) (j : Fin d)
    (H : Transcript N → ResidualControls d) (hH : Measurable H) (r : Fin (d+1)) :
    Measurable (rankResidual A weight tape seed k hkd t j H r) := by
  have hs := measurable_reframedState A weight tape seed k hkd t j H hH
  have hr := measurable_fst.comp hs
  have hB := measurable_snd.comp hs
  have hc := orthogonal_inverse_action_measurable.comp (hB.prodMk (measurable_column j))
  have hres := (continuous_residualCoordinates r.val (by omega)).measurable.comp hc
  change Measurable (fun Q => if (reframedState A weight tape seed k hkd t j H Q).1 = r then
    residualCoordinates r.val (by omega)
      (action (reframedState A weight tape seed k hkd t j H Q).2⁻¹ (column Q j)) else 0)
  exact Measurable.ite (hr (measurableSet_singleton r)) hres measurable_const

/-- The actual conditional residual distribution is invariant under each fixed
orthogonal transformation, a.e. in the observed transcript law. -/
theorem rankResidual_condDistrib_rotation (A : OracleAlgorithm d N S)
    (weight : Ω → ℝ) (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d)
    (t : ℕ) (ht : t ≤ N) (j : Fin d) (hstop : RankStopped A weight tape seed k hkd)
    (H : Transcript N → ResidualControls d) (hH : Measurable H)
    (r : Fin (d+1)) (g : OrthogonalGroup (d-r.val)) :
    (condDistrib (rankResidual A weight tape seed k hkd t j H r)
      (history A weight tape seed t j) (orthogonalHaarProbability d)).map (action g)
      =ᵐ[(orthogonalHaarProbability d).map (history A weight tape seed t j)]
    condDistrib (rankResidual A weight tape seed k hkd t j H r)
      (history A weight tape seed t j) (orthogonalHaarProbability d) := by
  let control : ResidualControls d := Function.update (fun _ => 1) r g
  let T := reframedOrbit A weight tape seed k hkd t j H control
  have hmp := reframedOrbit_measurePreserving A weight tape seed k hkd t ht j hstop H hH control
  have hfix := reframedOrbit_fixes_history A weight tape seed k hkd t ht j hstop H control
  apply condDistrib_map_eq_of_preserving_observable (orthogonalHaarProbability d)
    (history A weight tape seed t j) (measurable_history A weight tape seed t j)
    (rankResidual A weight tape seed k hkd t j H r)
    (rankResidual_measurable A weight tape seed k hkd t j H hH r)
    T hmp (action g) (action g).continuous.measurable hfix
  intro Q
  have hs : reframedState A weight tape seed k hkd t j H (T Q) =
      reframedState A weight tape seed k hkd t j H Q := by
    change reframe (frameFromTranscript A weight tape seed k hkd t
      (history A weight tape seed t j (T Q))) (H (history A weight tape seed t j (T Q))) = _
    rw [hfix]
    rfl
  unfold rankResidual
  rw [hs]
  by_cases hr : (reframedState A weight tape seed k hkd t j H Q).1 = r
  · rw [if_pos hr,if_pos hr]
    have hstateQ : reframedState A weight tape seed k hkd t j H Q =
        (r,(reframedState A weight tape seed k hkd t j H Q).2) := Prod.ext hr rfl
    have hcol : column (T Q) j = action
        (rotateAtState (reframedState A weight tape seed k hkd t j H Q) control) (column Q j) :=
      column_mul_action _ Q j
    rw [hcol,hstateQ,rotated_residualCoordinates]
    simp only [control,Function.update_self]
  · rw [if_neg hr,if_neg hr,map_zero]

#print axioms condDistrib_map_eq_of_preserving_observable
#print axioms rankResidual_condDistrib_rotation
end
end Task006.AdaptiveSphereKernel
