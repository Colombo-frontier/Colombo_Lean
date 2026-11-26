import SampleReuse.RandomFrameTranscript
import SampleReuse.CurvatureJet
import SampleReuse.CurvatureFrameCore

noncomputable section
namespace SampleReuse.RandomFrame

open SecondOrder

def truncatedFrameCore {d T : ℕ} (U : Point (T+1) →ₗᵢ[ℝ] Point d)
    (A β : ℝ) (k : ℕ) : Point d → ℝ :=
  scalarLinearScaling (truncatedCurvatureChain T k) A (curvatureFrameMap U β)

/-- Actual order-two jet equality survives the ambient frame projection and
the amplitude/length scaling in the curvature hard instance. -/
theorem frameCore_truncateJet {d T : ℕ} (U : Point (T+1) →ₗᵢ[ℝ] Point d)
    (A β : ℝ) (k : ℕ) (x : Point d)
    (htail : ∀ i : Fin (T+1), k ≤ i.val+1 → |curvatureFrameMap U β x i| ≤ 1/2) :
    ScalarJetEq (curvatureFrameCore U A β) (truncatedFrameCore U A β k) x := by
  exact ((deterministicCurvatureChain_truncate T k (curvatureFrameMap U β x) htail).comp_linear
    (curvatureFrameMap U β)).const_mul A

variable {Ω : Type*}

/-- Coupling uses the actual jets of the scaled, frame-embedded chain. The
inequalities are tested only at the adaptive ideal queries, including the flat
boundary; no conclusion about arbitrary oracle replies is postulated. -/
theorem frameCore_transcript_coupling {d T : ℕ}
    (query : ∀ n, Ω → (Fin n → ℝ × Point d × (Point d →L[ℝ] Point d)) → Point d)
    (U : Point (T+1) →ₗᵢ[ℝ] Point d) (A β : ℝ) (ω : Ω) (N : ℕ)
    (htail : ∀ n < N, ∀ i : Fin (T+1), n+1 ≤ i.val+1 →
      |curvatureFrameMap U β
        (queryAt query (fun n (_ : Unit) => fullJet (truncatedFrameCore U A β (n+1)))
          ω () n) i| ≤ 1/2) :
    responseHistory query (fun _ (_ : Unit) => fullJet (curvatureFrameCore U A β)) ω () N =
      responseHistory query (fun n (_ : Unit) => fullJet (truncatedFrameCore U A β (n+1)))
        ω () N := by
  apply fullJet_transcript_coupling
  intro n hn
  exact frameCore_truncateJet U A β (n+1) _ (htail n hn)

end SampleReuse.RandomFrame
