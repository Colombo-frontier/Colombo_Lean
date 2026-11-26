import SampleReuse.RandomFrameJet
import SampleReuse.RadialGeometry

noncomputable section
namespace SampleReuse.RandomFrame

open SecondOrder Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem scalarJetEq_of_eventuallyEq {f g : E → ℝ} {x : E}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (h : f =ᶠ[𝓝 x] g) :
    ScalarJetEq f g x :=
  ⟨hf, hg, h.eq_of_nhds, h.fderiv_eq, h.fderiv.fderiv_eq⟩

theorem radialGlobalization_jet_congr {f g : E → ℝ} {x : E}
    (h : ScalarJetEq f g x) (b : ℝ) {R : ℝ} (hR : 0 < R) :
    ScalarJetEq (radialGlobalization f b R) (radialGlobalization g b R) x :=
  ((ScalarJetEq.refl (radialCutoffLoss_contDiff hR 2) x).mul h).add
    (ScalarJetEq.refl (radialWallLoss_contDiff b hR 2) x)

/-- Strictly outside the cutoff ball, the full value/gradient/Hessian reply is
exactly the frame-independent radial wall reply. -/
theorem radialGlobalization_exteriorJet {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (b : ℝ) {R : ℝ} (hR : 0 < R) {x : E} (hx : 2*R < ‖x‖) :
    ScalarJetEq (radialGlobalization f b R) (radialWallLoss b R) x := by
  apply scalarJetEq_of_eventuallyEq
    (((radialCutoffLoss_contDiff hR 2).mul hf).add (radialWallLoss_contDiff b hR 2))
    (radialWallLoss_contDiff b hR 2)
  have hn : ∀ᶠ y : E in 𝓝 x, 2*R < ‖y‖ :=
    continuous_norm.continuousAt.eventually (lt_mem_nhds hx)
  filter_upwards [hn] with y hy
  have hc : radialCutoff (‖y‖/R) = 0 :=
    radialCutoff_zero ((le_div_iff₀ hR).mpr hy.le)
  simp only [radialGlobalization, radialCutoffLoss, hc, zero_mul, zero_add]

def truncatedRadialFrame {d T : ℕ} (U : Point (T+1) →ₗᵢ[ℝ] Point d)
    (A β b R : ℝ) (k : ℕ) : Point d → ℝ :=
  radialGlobalization (truncatedFrameCore U A β k) b R

theorem radialFrame_truncateJet {d T : ℕ} (U : Point (T+1) →ₗᵢ[ℝ] Point d)
    (A β b : ℝ) {R : ℝ} (hR : 0 < R) (k : ℕ) (x : Point d)
    (htail : ‖x‖ ≤ 2*R → ∀ i : Fin (T+1), k ≤ i.val+1 →
      |curvatureFrameMap U β x i| ≤ 1/2) :
    ScalarJetEq (radialGlobalization (curvatureFrameCore U A β) b R)
      (truncatedRadialFrame U A β b R k) x := by
  by_cases hx : ‖x‖ ≤ 2*R
  · exact radialGlobalization_jet_congr (frameCore_truncateJet U A β k x (htail hx)) b hR
  · have hcore := frameCore_truncateJet U A β k 0 (by
      intro i hi
      simp only [map_zero, Pi.zero_apply, abs_zero]
      norm_num)
    exact (radialGlobalization_exteriorJet hcore.left_smooth b hR (lt_of_not_ge hx)).trans
      (radialGlobalization_exteriorJet hcore.right_smooth b hR (lt_of_not_ge hx)).symm

variable {Ω : Type*}

theorem radialFrame_transcript_coupling {d T : ℕ}
    (query : ∀ n, Ω → (Fin n → ℝ × Point d × (Point d →L[ℝ] Point d)) → Point d)
    (U : Point (T+1) →ₗᵢ[ℝ] Point d) (A β b : ℝ) {R : ℝ} (hR : 0 < R)
    (ω : Ω) (N : ℕ)
    (htail : ∀ n < N,
      ‖queryAt query (fun n (_ : Unit) => fullJet (truncatedRadialFrame U A β b R (n+1))) ω () n‖ ≤
        2*R → ∀ i : Fin (T+1), n+1 ≤ i.val+1 →
      |curvatureFrameMap U β
        (queryAt query (fun n (_ : Unit) => fullJet (truncatedRadialFrame U A β b R (n+1))) ω () n) i| ≤ 1/2) :
    responseHistory query
      (fun _ (_ : Unit) => fullJet (radialGlobalization (curvatureFrameCore U A β) b R)) ω () N =
    responseHistory query
      (fun n (_ : Unit) => fullJet (truncatedRadialFrame U A β b R (n+1))) ω () N := by
  apply fullJet_transcript_coupling
  intro n hn
  exact radialFrame_truncateJet U A β b hR (n+1) _ (htail n hn)

end SampleReuse.RandomFrame
