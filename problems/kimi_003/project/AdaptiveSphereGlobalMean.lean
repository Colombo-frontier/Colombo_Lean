import AdaptiveSphereGlobalInvariance
import AdaptiveSphereMean

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace Task006.AdaptiveSphereGlobal

open Task006.Full Task006.Full.OracleAlgorithm Task006.HaarRebalancing
open Task006.AdaptiveSphereState Task006.AdaptiveSphereStopped Task006.AdaptiveSphereAction
open Task006.AdaptiveSphereFrame Task006.AdaptiveSphereTranscript Task006.PosteriorCenter
open Task006.AdaptiveSphereJoint Task006.AdaptiveSphereMean Task006.AdaptiveSphere
open Task006.AdaptiveSphereActualStep

set_option maxHeartbeats 1000000
noncomputable section
variable {d N : ℕ} {S : Type*} [MeasurableSpace S]

def jointObservation (A : OracleAlgorithm d N S) (k : ℕ) (hkd : k ≤ d)
    (t : ℕ) (j : Fin d) (w : Exogenous S × OrthogonalGroup d) : Exogenous S × Transcript N :=
  (w.1,jointHistory A k hkd t j w)

abbrev jointPastSigma (A : OracleAlgorithm d N S) (k : ℕ) (hkd : k ≤ d) (t : ℕ) (j : Fin d) :
    MeasurableSpace (Exogenous S × OrthogonalGroup d) :=
  (inferInstance : MeasurableSpace (Exogenous S × Transcript N)).comap (jointObservation A k hkd t j)

def jointCenter (A : OracleAlgorithm d N S) (k : ℕ) (hkd : k ≤ d)
    (t : ℕ) (j : Fin d) (w : Exogenous S × OrthogonalGroup d) : Space d :=
  centerFromTranscript A id w.1.2 w.1.1 k hkd t (jointHistory A k hkd t j w)

theorem jointObservation_measurable (A : OracleAlgorithm d N S) (k : ℕ) (hkd : k ≤ d)
    (t : ℕ) (j : Fin d) : Measurable (jointObservation A k hkd t j) :=
  measurable_fst.prodMk (jointHistory_measurable A k hkd t j)

theorem jointCenter_stronglyMeasurable_past (A : OracleAlgorithm d N S)
    (k : ℕ) (hkd : k ≤ d) (t : ℕ) (j : Fin d) :
    StronglyMeasurable[jointPastSigma A k hkd t j] (jointCenter A k hkd t j) := by
  have ho : @Measurable (Exogenous S × OrthogonalGroup d) (Exogenous S × Transcript N)
      (jointPastSigma A k hkd t j) _ (jointObservation A k hkd t j) :=
    measurable_iff_comap_le.mpr le_rfl
  have hm := (centerFromTranscript_joint_measurable A k hkd t).comp ho
  have hmc : @Measurable (Exogenous S × OrthogonalGroup d) (Space d)
      (jointPastSigma A k hkd t j) _ (jointCenter A k hkd t j) := by
    change @Measurable (Exogenous S × OrthogonalGroup d) (Space d)
      (jointPastSigma A k hkd t j) _ (fun w =>
        centerFromTranscript A id w.1.2 w.1.1 k hkd t (jointHistory A k hkd t j w))
    simpa only [Function.comp_def,jointObservation] using hm
  exact hmc.stronglyMeasurable

theorem jointCenter_eq_fixed (A : OracleAlgorithm d N S) (k : ℕ) (hkd : k ≤ d)
    (t : ℕ) (j : Fin d) (w : Exogenous S × OrthogonalGroup d) :
    jointCenter A k hkd t j w =
      actualCenter (stoppedObserver A id w.1.2 w.1.1 k hkd) id w.1.2 () k hkd t j w.2 := by
  unfold jointCenter actualCenter
  rw [stoppedObserver_center_eq]
  rfl

theorem jointCenter_eq_projected (A : OracleAlgorithm d N S) (k : ℕ) (hkd : k ≤ d)
    (t : ℕ) (ht : t ≤ N) (j : Fin d) (w : Exogenous S × OrthogonalGroup d) :
    jointCenter A k hkd t j w = projectedCenter (jointFrame A k hkd t j w) (column w.2 j) := by
  rw [jointCenter_eq_fixed,actualCenter_eq_projected _ _ _ _ _ _ t ht]
  simp only [actualState,stoppedObserver_frame_eq]
  rfl

theorem jointCenter_norm_le_one (A : OracleAlgorithm d N S) (k : ℕ) (hkd : k ≤ d)
    (t : ℕ) (ht : t ≤ N) (j : Fin d) (w : Exogenous S × OrthogonalGroup d) :
    ‖jointCenter A k hkd t j w‖ ≤ 1 := by
  rw [jointCenter_eq_fixed]
  exact actualCenter_norm_le_one _ _ _ _ _ _ t ht j w.2

theorem joint_conditional_mean (A : OracleAlgorithm d N S) (k : ℕ) (hkd : k ≤ d)
    (t : ℕ) (ht : t ≤ N) (j : Fin d)
    (γ : Measure (Exogenous S)) [IsProbabilityMeasure γ] :
    (γ.prod (orthogonalHaarProbability d))[(fun w => column w.2 j) | jointPastSigma A k hkd t j]
      =ᵐ[γ.prod (orthogonalHaarProbability d)] jointCenter A k hkd t j := by
  let μ := γ.prod (orthogonalHaarProbability d)
  have hm : jointPastSigma A k hkd t j ≤
      (inferInstance : MeasurableSpace (Exogenous S × OrthogonalGroup d)) :=
    (jointObservation_measurable A k hkd t j).comap_le
  have hC : Integrable (jointCenter A k hkd t j) μ := by
    apply Integrable.of_bound ((jointCenter_stronglyMeasurable_past A k hkd t j).mono hm).aestronglyMeasurable 1
    exact Filter.Eventually.of_forall (jointCenter_norm_le_one A k hkd t ht j)
  have hθ : Integrable (fun w : Exogenous S × OrthogonalGroup d => column w.2 j) μ := by
    apply Integrable.of_bound ((measurable_column j).comp measurable_snd).aestronglyMeasurable 1
    exact Filter.Eventually.of_forall (fun w => le_of_eq ((orthonormal_column w.2).norm_eq_one j))
  have hinv : ∀ s : Set (Exogenous S × OrthogonalGroup d),
      MeasurableSet[jointPastSigma A k hkd t j] s →
        (jointOrbit A k hkd t j (negativeControl d)) ⁻¹' s = s := by
    intro s hs
    rcases hs with ⟨b,hb,rfl⟩
    ext w
    have hh := jointOrbit_fixes_history A k hkd t ht j (negativeControl d) w
    have ho : jointObservation A k hkd t j (jointOrbit A k hkd t j (negativeControl d) w) =
        jointObservation A k hkd t j w := by
      apply Prod.ext
      · rfl
      · exact hh
    change jointObservation A k hkd t j (jointOrbit A k hkd t j (negativeControl d) w) ∈ b ↔ _
    rw [ho]
    rfl
  have hodd : ∀ w : Exogenous S × OrthogonalGroup d,
      (column (jointOrbit A k hkd t j (negativeControl d) w).2 j -
        jointCenter A k hkd t j (jointOrbit A k hkd t j (negativeControl d) w)) =
      -(column w.2 j-jointCenter A k hkd t j w) := by
    intro w
    have hc : jointCenter A k hkd t j (jointOrbit A k hkd t j (negativeControl d) w) =
        jointCenter A k hkd t j w := by
      change centerFromTranscript A id w.1.2 w.1.1 k hkd t
        (jointHistory A k hkd t j (jointOrbit A k hkd t j (negativeControl d) w)) = _
      rw [jointOrbit_fixes_history A k hkd t ht]
      rfl
    rw [hc]
    change column (rotateAtState (jointFrame A k hkd t j w) (negativeControl d)*w.2) j - _ = _
    rw [column_mul_action,rotateNegative_action,← jointCenter_eq_projected A k hkd t ht j w]
    module
  have hz := condExp_zero_of_invariant_odd_map (jointPastSigma A k hkd t j) hm
    (jointOrbit A k hkd t j (negativeControl d))
    (jointOrbit_measurePreserving A k hkd t ht j (negativeControl d) γ) hinv
    (fun w => column w.2 j-jointCenter A k hkd t j w) (hθ.sub hC) hodd
  have hd := condExp_sub hθ hC (jointPastSigma A k hkd t j)
  have hceC := condExp_of_stronglyMeasurable hm
    (jointCenter_stronglyMeasurable_past A k hkd t j) hC
  filter_upwards [hz,hd] with w hw hsub
  rw [hceC] at hsub
  have he : (μ[fun w => column w.2 j | jointPastSigma A k hkd t j]) w -
      jointCenter A k hkd t j w = 0 := hsub.symm.trans hw
  exact sub_eq_zero.mp he

end
end Task006.AdaptiveSphereGlobal
