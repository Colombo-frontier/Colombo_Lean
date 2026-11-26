import SampleReuse.RandomFramePrefixLoss
import SampleReuse.RandomFramePrefix

noncomputable section
namespace SampleReuse.RandomFrame

open SecondOrder

def frameColumns {d T : ℕ} (U : Point (T+1) →ₗᵢ[ℝ] Point d) (j : ℕ) : Point d :=
  if hj : j < T+1 then U (blockUnit ⟨j, hj⟩ (1:ℝ)) else 0

theorem frameColumns_prefix {d T n : ℕ} (U : Point (T+1) →ₗᵢ[ℝ] Point d) (hn : n ≤ T) :
    (fun i : Fin (n+1) => frameColumns U i.val) =
      (fun i => U (blockUnit (Fin.castLE (by omega) i) (1:ℝ))) := by
  funext i
  have hi : i.val < T+1 := by omega
  simp only [frameColumns, dif_pos hi]
  rfl

def radialPrefixOracle {d T : ℕ} (U : Point (T+1) →ₗᵢ[ℝ] Point d) (A β b R : ℝ) :=
  prefixOracle (fun n => prefixRadialReply (d := d) T n A β b R) (fun _ : Unit => frameColumns U)

theorem radialPrefixOracle_actual_reply {d T n : ℕ}
    (U : Point (T+1) →ₗᵢ[ℝ] Point d) (A β b R : ℝ) (hn : n ≤ T) (x : Point d) :
    radialPrefixOracle U A β b R n () x = fullJet (truncatedRadialFrame U A β b R (n+1)) x := by
  rw [truncatedRadialFrame_eq_prefix U A β b R hn]
  simp only [radialPrefixOracle, prefixOracle, prefixRadialReply, frameColumns_prefix U hn]

variable {Ω : Type*}

/-- The concrete ideal oracle has a measurable prefix-only scalar formula.
The actual radial full-jet execution is coupled to that oracle on the exact
small-hidden-projection event. No conditional uniformity or jet premise is
assumed: the latter is proved from the hard scalar loss. -/
theorem radialPrefix_transcript_coupling {d T : ℕ}
    (query : ∀ n, Ω → (Fin n → ℝ × Point d × (Point d →L[ℝ] Point d)) → Point d)
    (U : Point (T+1) →ₗᵢ[ℝ] Point d) (A β b : ℝ) {R : ℝ} (hR : 0 < R)
    (ω : Ω) (N : ℕ) (hN : N ≤ T+1)
    (htail : ∀ n < N,
      ‖queryAt query (radialPrefixOracle U A β b R) ω () n‖ ≤ 2*R →
      ∀ i : Fin (T+1), n+1 ≤ i.val+1 →
        |curvatureFrameMap U β (queryAt query (radialPrefixOracle U A β b R) ω () n) i| ≤ 1/2) :
    responseHistory query
      (fun _ (_ : Unit) => fullJet (radialGlobalization (curvatureFrameCore U A β) b R)) ω () N =
      responseHistory query (radialPrefixOracle U A β b R) ω () N := by
  apply responseHistory_coupling
  intro n hn
  rw [radialPrefixOracle_actual_reply U A β b R (by omega)]
  exact fullJet_eq_of_scalarJetEq (radialFrame_truncateJet U A β b hR (n+1) _ (htail n hn))

end SampleReuse.RandomFrame
