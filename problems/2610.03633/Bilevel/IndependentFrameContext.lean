import Bilevel.OrdinaryFrameObserver
import Bilevel.TransportNetworkAuxiliary

/-! Exact prior factorization for a selected auxiliary frame. Its independent
context contains the full original network, every other auxiliary orientation,
and private randomness. The selected full orientation is excluded. This is a
prior product identity, not an interchange of transcript and full-frame
conditionings. -/
noncomputable section
open MeasureTheory
namespace Bilevel.IndependentFrame
open EuclideanGaussian ProjectionPosterior

abbrev Context (C : Type*) (D k : ℕ) := C × (Fin k → OrthogonalHaar.Group D)

def expose {C : Type*} {D k T : ℕ} (hT : T≤D) (i : Fin (k+1))
    (p : C × (Fin (k+1) → OrthogonalHaar.Group D)) : Context C D k × Frame D T :=
  ((p.1,fun j => p.2 (i.succAbove j)),HaarFrame.frame D T hT (p.2 i))

theorem expose_preserving {C : Type*} [MeasurableSpace C] (ρ : Measure C)
    [SFinite ρ]
    {D k T : ℕ} (hT : T≤D) (i : Fin (k+1)) :
    MeasurePreserving (expose (C := C) hT i)
      (ρ.prod (Measure.pi (fun _ : Fin (k+1) => OrthogonalHaar.law D)))
      ((ρ.prod (Measure.pi (fun _ : Fin k => OrthogonalHaar.law D))).prod (HaarFrame.frameLaw D T hT)) := by
  have hp := measurePreserving_piFinSuccAbove (fun _ : Fin (k+1) => OrthogonalHaar.law D) i
  have hs := (Measure.measurePreserving_swap (μ := OrthogonalHaar.law D)
    (ν := Measure.pi (fun _ : Fin k => OrthogonalHaar.law D))).comp hp
  have hc := (MeasurePreserving.id ρ).prod hs
  have ha := (measurePreserving_prodAssoc ρ
    (Measure.pi (fun _ : Fin k => OrthogonalHaar.law D)) (OrthogonalHaar.law D)).symm
      (MeasurableEquiv.prodAssoc : (C × (Fin k → OrthogonalHaar.Group D)) × OrthogonalHaar.Group D ≃ᵐ
        C × ((Fin k → OrthogonalHaar.Group D) × OrthogonalHaar.Group D))
  have hf : MeasurePreserving (HaarFrame.frame D T hT) (OrthogonalHaar.law D)
      (HaarFrame.frameLaw D T hT) := ⟨HaarFrame.frame_measurable D T hT,rfl⟩
  have hh := ((MeasurePreserving.id
    (ρ.prod (Measure.pi (fun _ : Fin k => OrthogonalHaar.law D)))).prod hf).comp (ha.comp hc)
  convert hh using 1

def auxiliaryExpose {C : Type*} {n D k T : ℕ} (hT : T≤D) (i : Fin (k+1))
    (p : C × TransportNetworkAuxiliary.Sample n D (k+1)) :
    Context (C × TransportNetwork.Latent n D) D k × Frame D T :=
  (((p.1,p.2.1),fun j => p.2.2 (i.succAbove j)),TransportNetworkAuxiliary.auxiliaryFrame T hT i p.2)

theorem auxiliaryExpose_preserving {C : Type*} [MeasurableSpace C] (ρ : Measure C)
    [SFinite ρ]
    {n D k T : ℕ} (hT : T≤D) (i : Fin (k+1)) :
    MeasurePreserving (auxiliaryExpose (C := C) (n := n) hT i)
      (ρ.prod (TransportNetworkAuxiliary.law n D (k+1)))
      (((ρ.prod (TransportNetwork.law n D)).prod
        (Measure.pi (fun _ : Fin k => OrthogonalHaar.law D))).prod (HaarFrame.frameLaw D T hT)) := by
  have ha := (measurePreserving_prodAssoc ρ (TransportNetwork.law n D)
    (Measure.pi (fun _ : Fin (k+1) => OrthogonalHaar.law D))).symm
      (MeasurableEquiv.prodAssoc : (C × TransportNetwork.Latent n D) ×
        (Fin (k+1) → OrthogonalHaar.Group D) ≃ᵐ C × TransportNetworkAuxiliary.Sample n D (k+1))
  have hh := (expose_preserving (ρ.prod (TransportNetwork.law n D)) hT i).comp ha
  exact hh

end Bilevel.IndependentFrame
