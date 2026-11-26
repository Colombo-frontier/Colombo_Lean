import Bilevel.TransportRoundFresh
import Bilevel.TransportControllerStore

/-! Concrete measurable generator stores for the old complementary domain
and the fresh complementary range. No measurable choice of orthonormal basis
is used by the executed monitor. -/
noncomputable section
open MeasureTheory
namespace Bilevel.TransportGeneratorStore
open EuclideanGaussian ProjectionGeometry TransportRound
set_option maxHeartbeats 500000

def residualFamily {D r : ℕ} (A : ProjectionStore.Store D) (v : Fin r → Space D) : Fin r → Space D :=
  fun i => ProjectionStore.residual D A (v i)

theorem residualFamily_measurable (D r : ℕ) :
    Measurable (fun p : ProjectionStore.Store D × (Fin r → Space D) => residualFamily p.1 p.2) := by
  apply measurable_pi_lambda
  intro i
  exact ProjectionStore.residual_measurable D _ measurable_fst _ ((measurable_pi_apply i).comp measurable_snd)

theorem residualFamily_span {D r : ℕ} (A : Submodule ℝ (Space D)) (v : Fin r → Space D) :
    span (residualFamily (ProjectionStore.ofSubspace D A) v) = residualSpace A (span v) := by
  unfold residualSpace span
  rw [Submodule.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨i,rfl⟩
    exact ⟨v i,⟨i,rfl⟩,(ProjectionStore.residual_subspace D A (v i)).symm⟩
  · rintro ⟨y,⟨i,rfl⟩,rfl⟩
    exact ⟨i,ProjectionStore.residual_subspace D A (v i)⟩

def freshFamily {D h a r : ℕ} (hard : Fin h → Space D) (old : Fin a → Space D)
    (input : Fin r → Space D) : Fin r → Space D :=
  residualFamily (projector D (residualFamily (projector D hard) old))
    (residualFamily (projector D hard) input)

theorem freshFamily_span {D h a r : ℕ} (hard : Fin h → Space D) (old : Fin a → Space D)
    (input : Fin r → Space D) :
    span (freshFamily hard old input) = freshSpace (span hard) (span old) (span input) := by
  simp only [freshFamily,projector_correct,residualFamily_span,freshSpace]

theorem freshFamily_measurable (D h a r : ℕ) :
    Measurable (fun p : (Fin h → Space D) × (Fin a → Space D) × (Fin r → Space D) =>
      freshFamily p.1 p.2.1 p.2.2) := by
  have hH : Measurable (fun p : (Fin h → Space D) × (Fin a → Space D) × (Fin r → Space D) =>
      projector D p.1) := (projector_measurable D h).comp measurable_fst
  have hA := (residualFamily_measurable D a).comp (hH.prodMk (measurable_fst.comp measurable_snd))
  have hU := (residualFamily_measurable D r).comp (hH.prodMk (measurable_snd.comp measurable_snd))
  exact (residualFamily_measurable D r).comp (((projector_measurable D a).comp hA).prodMk hU)

theorem freshSpace_projector_measurable (D h a r : ℕ) :
    Measurable (fun p : (Fin h → Space D) × (Fin a → Space D) × (Fin r → Space D) =>
      ProjectionStore.ofSubspace D (freshSpace (span p.1) (span p.2.1) (span p.2.2))) := by
  have hh := (projector_measurable D r).comp (freshFamily_measurable D h a r)
  change Measurable (fun p : (Fin h → Space D) × (Fin a → Space D) × (Fin r → Space D) =>
    projector D (freshFamily p.1 p.2.1 p.2.2)) at hh
  simpa only [projector_correct,freshFamily_span] using hh

end Bilevel.TransportGeneratorStore
