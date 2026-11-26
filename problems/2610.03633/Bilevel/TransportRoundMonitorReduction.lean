import Bilevel.TransportRoundBatchEnergy

/-! The concrete monitor's double residual equals the fresh complement of
the full paired domain. Thus its implementation only needs the actual frozen
generator family and the actual paired store, not an extra unknown source
space or a new full-frame probability premise. -/
noncomputable section
namespace Bilevel.TransportRound
open EuclideanGaussian OrthogonalAction TransportNetwork TransportEdgePosterior ProjectionGeometry
set_option maxHeartbeats 600000

theorem residual_nested {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {A B : Submodule ℝ E} (h : A≤B) (x : E) :
    ProjectionGeometry.residual B (ProjectionGeometry.residual A x)=ProjectionGeometry.residual B x := by
  have hp : project B (project A x)=project A x :=
    Submodule.orthogonalProjection_eq_self_iff.mpr (h (project_mem A x))
  have hsub : project B (x-project A x)=project B x-project B (project A x) := by
    exact congrArg (fun y : B => (y : E)) (map_sub B.orthogonalProjection x (project A x))
  dsimp only [ProjectionGeometry.residual]
  rw [hsub,hp]
  abel

theorem residualSpace_nested {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {A B : Submodule ℝ E} (h : A≤B) (F : Submodule ℝ E) :
    residualSpace B (residualSpace A F)=residualSpace B F := by
  ext x
  constructor
  · rintro ⟨y,⟨z,hz,rfl⟩,rfl⟩
    exact ⟨z,hz,(residual_nested h z).symm⟩
  · rintro ⟨z,hz,rfl⟩
    exact ⟨ProjectionGeometry.residual A z,⟨z,hz,rfl⟩,residual_nested h z⟩

theorem forwardMonitor_reduced {n D m T : ℕ} (hT : T≤D) (t : ℕ)
    (g : Generators n D m) (z : Latent n D) (P : Edge n → Pairs D) (W : Known n D) (e : Edge n) :
    forwardMonitor hT t g z P W e ↔ TransportControllerEdge.angleBad (W (dst e))
      (residualSpace (domain (hardPairs T hT e z++P e)) (known g (src e))) (z.2 e) := by
  have hA : protectedDomain (frame T hT z (src e)) (P e) (oldProtected T t (src e))≤
      domain (hardPairs T hT e z++P e) := by
    rw [domain_append,hardPairs_domain]
    exact sup_le le_sup_right ((protectedSpace_le_frame _ _).trans le_sup_left)
  unfold forwardMonitor
  rw [residualSpace_nested hA]

theorem reverseMonitor_reduced {n D m T : ℕ} (hT : T≤D) (t : ℕ)
    (g : Generators n D m) (z : Latent n D) (P : Edge n → Pairs D) (W : Known n D) (e : Edge n) :
    reverseMonitor hT t g z P W e ↔ TransportControllerEdge.angleBad (W (src e))
      (residualSpace (domain (reverseHardPairs T hT e z++swapPairs (forwardPairs e g z++P e)))
        (known g (dst e))) ((z.2 e)⁻¹) := by
  have hA : protectedDomain (frame T hT z (dst e)) (swapPairs (forwardPairs e g z++P e))
      (oldProtected T t (src e))≤domain (reverseHardPairs T hT e z++swapPairs (forwardPairs e g z++P e)) := by
    rw [domain_append]
    have hH : domain (reverseHardPairs T hT e z)=frameSpace (frame T hT z (dst e)) :=
      TransportControllerPairedStore.domain_pairs (frame T hT z (dst e),frame T hT z (src e))
    rw [hH]
    exact sup_le le_sup_right ((protectedSpace_le_frame _ _).trans le_sup_left)
  unfold reverseMonitor
  rw [residualSpace_nested hA]

end Bilevel.TransportRound
