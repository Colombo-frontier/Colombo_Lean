import AdaptiveSphereFullPosterior

/-! Full-rank conditional distributions are point masses at the observed
center, without any stopping or invariance premise. -/
open MeasureTheory Set ProbabilityTheory
open scoped Matrix RealInnerProductSpace

namespace Task006.AdaptiveSphereKernel
open Task006.Full Task006.Full.OracleAlgorithm
open Task006.HaarRebalancing Task006.AdaptiveSphereBlock
open Task006.AdaptiveSphereFrame Task006.AdaptiveSphereResidualFrame
open Task006.AdaptiveSphereState Task006.AdaptiveSphereAction
open Task006.AdaptiveSphereTranscript Task006.AdaptiveSphereMeasurable
open Task006.AdaptiveSphereGeometry Task006.PosteriorCenter Task006.AdaptiveSphereActualStep
open Task006.AdaptiveSphereMean Task006.AdaptiveSphereReframe Task006.AdaptiveSphere
open Task006.AdaptiveSphereIsotropy Task006.PosteriorResidualEnergy
noncomputable section
variable {d N : ℕ} {S Ω : Type*} [MeasurableSpace S]

def fullRank (d : ℕ) : Fin (d+1) := ⟨d,Nat.lt_succ_self d⟩

theorem prefixPart_full_dimension (x : E d) : prefixPart d x = x := by
  apply WithLp.ofLp_injective 2
  funext i
  simp [prefixPart,i.isLt]

theorem projectedCenter_full_rank (state : FrameState d) (hfull : state.1.val=d) (θ : E d) :
    projectedCenter state θ = θ := by
  rw [projectedCenter,hfull,prefixPart_full_dimension,action_inverse_cancel]

def observedGatedCenter (A : OracleAlgorithm d N S) (weight : Ω → ℝ) (tape : ℕ → Ω)
    (seed : S) (k : ℕ) (hkd : k ≤ d) (t : ℕ)
    (H : Transcript N → ResidualControls d) (h : Transcript N) : E d :=
  if (observedFrame A weight tape seed k hkd t H h).1 = fullRank d then
    centerFromTranscript A weight tape seed k hkd t h else 0

theorem observedGatedCenter_measurable (A : OracleAlgorithm d N S) (weight : Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d) (t : ℕ)
    (H : Transcript N → ResidualControls d) (hH : Measurable H) :
    Measurable (observedGatedCenter A weight tape seed k hkd t H) := by
  have hs := measurable_fst.comp (observedFrame_measurable A weight tape seed k hkd t H hH)
  change Measurable (fun h => if (observedFrame A weight tape seed k hkd t H h).1 = fullRank d then
    centerFromTranscript A weight tape seed k hkd t h else 0)
  exact Measurable.ite (hs (measurableSet_singleton (fullRank d)))
    (measurable_centerFromTranscript A weight tape seed k hkd t) measurable_const

theorem rankTheta_full_eq_observed (A : OracleAlgorithm d N S) (weight : Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d) (t : ℕ) (ht : t ≤ N)
    (j : Fin d) (H : Transcript N → ResidualControls d) (Q : OrthogonalGroup d) :
    rankTheta A weight tape seed k hkd t j H (fullRank d) Q =
      observedGatedCenter A weight tape seed k hkd t H (history A weight tape seed t j Q) := by
  unfold rankTheta observedGatedCenter
  split_ifs with hr
  · have hfull : (actualState A weight tape seed k hkd t j Q).1.val=d := by
      exact congrArg Fin.val hr
    have hc := actualCenter_eq_projected A weight tape seed k hkd t ht j Q
    rw [projectedCenter_full_rank _ hfull] at hc
    exact hc.symm
  · rfl

/-- Once the actual observed span fills the ambient space, the full regular
conditional distribution of Θ is the Dirac law at its observed center. -/
theorem full_rank_condDistrib_dirac (A : OracleAlgorithm d N S) (weight : Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d) (t : ℕ) (ht : t ≤ N)
    (j : Fin d) (H : Transcript N → ResidualControls d) (hH : Measurable H) :
    ∀ᵐ h ∂(orthogonalHaarProbability d).map (history A weight tape seed t j),
      (observedFrame A weight tape seed k hkd t H h).1 = fullRank d →
      condDistrib (fun Q => column Q j) (history A weight tape seed t j) (orthogonalHaarProbability d) h =
        Measure.dirac (centerFromTranscript A weight tape seed k hkd t h) := by
  classical
  let p : Transcript N → Prop := fun h => (observedFrame A weight tape seed k hkd t H h).1 = fullRank d
  have hp : MeasurableSet {h : Transcript N | p h} :=
    (measurable_fst.comp (observedFrame_measurable A weight tape seed k hkd t H hH))
      (measurableSet_singleton (fullRank d))
  have hg := condDistrib_observable_gate (orthogonalHaarProbability d)
    (history A weight tape seed t j) (measurable_history A weight tape seed t j)
    (fun Q => column Q j) (measurable_column j) p hp
  have hc := condDistrib_comp_self (μ := orthogonalHaarProbability d)
    (history A weight tape seed t j) (observedGatedCenter_measurable A weight tape seed k hkd t H hH)
  have heq : observedGatedCenter A weight tape seed k hkd t H ∘ history A weight tape seed t j =
      rankTheta A weight tape seed k hkd t j H (fullRank d) := by
    funext Q
    exact (rankTheta_full_eq_observed A weight tape seed k hkd t ht j H Q).symm
  rw [heq] at hc
  filter_upwards [hg,hc] with h hgate hcenter
  intro hR
  have hgate' : condDistrib (rankTheta A weight tape seed k hkd t j H (fullRank d))
      (history A weight tape seed t j) (orthogonalHaarProbability d) h =
      condDistrib (fun Q => column Q j) (history A weight tape seed t j) (orthogonalHaarProbability d) h :=
    hgate hR
  rw [← hgate',hcenter,Kernel.deterministic_apply,observedGatedCenter,if_pos hR]

#print axioms projectedCenter_full_rank
#print axioms rankTheta_full_eq_observed
#print axioms full_rank_condDistrib_dirac
end
end Task006.AdaptiveSphereKernel
