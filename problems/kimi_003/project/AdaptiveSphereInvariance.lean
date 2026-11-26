import AdaptiveSphereActualStep

/-! Actual finite adaptive residual invariance on Haar probability. The proof
inducts through the canonical scalar reply recursion and explicit Householder
updates, and applies only to a genuinely rank-stopped observation protocol. -/

open MeasureTheory Set
open scoped Matrix RealInnerProductSpace

namespace Task006.AdaptiveSphereInvariance

open Task006.Full Task006.Full.OracleAlgorithm
open Task006.HaarRebalancing Task006.AdaptiveSphereBlock
open Task006.AdaptiveSphereFrame Task006.AdaptiveSphereResidualFrame
open Task006.AdaptiveSphereState Task006.AdaptiveSphereAction
open Task006.AdaptiveSphereStepControls Task006.AdaptiveSphereStopped
open Task006.AdaptiveSphereTranscript Task006.AdaptiveSphereMeasurable
open Task006.AdaptiveSphereActualStep Task006.AdaptiveSphereOrbit

noncomputable section
variable {d N : ℕ} {S Ω : Type*} [MeasurableSpace S]

/-- Every constructed residual-frame rotation preserves the actual Haar prior
and fixes the entire observed stopped transcript, despite arbitrary measurable
adaptive query choices. No posterior invariance is a premise. -/
theorem rankStopped_residual_invariance (A : OracleAlgorithm d N S)
    (weight : Ω → ℝ) (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d)
    (j : Fin d) (hstop : RankStopped A weight tape seed k hkd)
    (t : ℕ) (ht : t ≤ N) :
    (∀ g : ResidualControls d,
      MeasurePreserving (orbitTransform A weight tape seed k hkd t j g)
        (orthogonalHaarProbability d) (orthogonalHaarProbability d)) ∧
    (∀ (g : ResidualControls d) (Q : OrthogonalGroup d),
      history A weight tape seed t j (orbitTransform A weight tape seed k hkd t j g Q) =
        history A weight tape seed t j Q) := by
  induction t with
  | zero =>
    exact ⟨orbitTransform_zero_measurePreserving A weight tape seed k hkd j,
      orbitTransform_zero_fixes_history A weight tape seed k hkd j⟩
  | succ t ih =>
    have hlt : t < N := by omega
    let ti : Fin N := ⟨t,hlt⟩
    obtain ⟨hmp,hfix⟩ := ih (by omega)
    have hnewmp (g : ResidualControls d) :
        MeasurePreserving (orbitTransform A weight tape seed k hkd (t+1) j g)
          (orthogonalHaarProbability d) (orthogonalHaarProbability d) := by
      have hcontrol : Measurable (stepControls A weight tape seed k hkd ti g) := by
        have hr := (stepControls_joint_measurable A weight tape seed k hkd ti).comp
          (measurable_const.prodMk measurable_id : Measurable
            (fun h : Transcript N => (g,h)))
        simpa only [Function.comp_def] using hr
      have h := observable_dependent_symmetry_measurePreserving
        (history A weight tape seed t j) (measurable_history A weight tape seed t j)
        (stepControls A weight tape seed k hkd ti g) hcontrol
        (orbitTransform A weight tape seed k hkd t j) hmp
        (orbitTransform_joint_measurable A weight tape seed k hkd t j)
        (orbitTransform_control_continuous A weight tape seed k hkd t j) hfix
      have heq : (fun Q => orbitTransform A weight tape seed k hkd t j
          (stepControls A weight tape seed k hkd ti g (history A weight tape seed t j Q)) Q) =
          orbitTransform A weight tape seed k hkd (t+1) j g := by
        funext Q
        exact (orbitTransform_step_factorization A weight tape seed k hkd ti j g Q).symm
      rw [heq] at h
      exact h
    refine ⟨hnewmp, ?_⟩
    intro g Q
    apply next_history_fixed_of_old_history_fixed A weight tape seed k hkd ti j g Q hstop
    rw [orbitTransform_step_factorization A weight tape seed k hkd ti j g Q]
    exact hfix _ Q

/-- Instantiation for the real stopped observer constructed from any original
canonical randomized adaptive algorithm, with its seed and tape fixed only for
this posterior argument. -/
theorem stoppedObserver_residual_invariance (A : OracleAlgorithm d N S)
    (weight : Ω → ℝ) (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d)
    (j : Fin d) (t : ℕ) (ht : t ≤ N) :
    (∀ g : ResidualControls d,
      MeasurePreserving
        (orbitTransform (stoppedObserver A weight tape seed k hkd) weight tape () k hkd t j g)
        (orthogonalHaarProbability d) (orthogonalHaarProbability d)) ∧
    (∀ (g : ResidualControls d) (Q : OrthogonalGroup d),
      history (stoppedObserver A weight tape seed k hkd) weight tape () t j
        (orbitTransform (stoppedObserver A weight tape seed k hkd) weight tape () k hkd t j g Q) =
      history (stoppedObserver A weight tape seed k hkd) weight tape () t j Q) :=
  rankStopped_residual_invariance _ _ _ _ _ _ j
    (stoppedObserver_rankStopped A weight tape seed k hkd) t ht

#print axioms rankStopped_residual_invariance
#print axioms stoppedObserver_residual_invariance
end
end Task006.AdaptiveSphereInvariance
