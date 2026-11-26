import Mathlib.MeasureTheory.Constructions.Pi

/-! Explicit measurable product regrouping used to isolate raw coordinates.
Every identity concerns the original product law. -/

noncomputable section
namespace GradientHessian.ProductRearrangement
open MeasureTheory

variable {A B C D E : Type*} [MeasurableSpace A] [MeasurableSpace B]
  [MeasurableSpace C] [MeasurableSpace D] [MeasurableSpace E]

def swapFront : A × B × C ≃ᵐ B × A × C :=
  MeasurableEquiv.prodAssoc.symm.trans
    ((MeasurableEquiv.prodComm.prodCongr (MeasurableEquiv.refl C)).trans MeasurableEquiv.prodAssoc)

theorem swapFront_apply (x : A × B × C) : swapFront x = (x.2.1,x.1,x.2.2) := rfl

theorem swapFront_preserving (μ : Measure A) (ν : Measure B) (ρ : Measure C)
    [SFinite μ] [SFinite ν] [SFinite ρ] :
    MeasurePreserving (swapFront (A := A) (B := B) (C := C))
      (μ.prod (ν.prod ρ)) (ν.prod (μ.prod ρ)) := by
  exact (measurePreserving_prodAssoc ν μ ρ).comp
    ((Measure.measurePreserving_swap.prod (MeasurePreserving.id ρ)).comp
      ((measurePreserving_prodAssoc μ ν ρ).symm MeasurableEquiv.prodAssoc))

def gather : (A × B) × C × D ≃ᵐ (A × C) × B × D :=
  MeasurableEquiv.prodAssoc.trans
    (((MeasurableEquiv.refl A).prodCongr swapFront).trans MeasurableEquiv.prodAssoc.symm)

theorem gather_apply (x : (A × B) × C × D) : gather x = ((x.1.1,x.2.1),x.1.2,x.2.2) := rfl

theorem gather_preserving (μ : Measure A) (ν : Measure B) (ρ : Measure C) (τ : Measure D)
    [SFinite μ] [SFinite ν] [SFinite ρ] [SFinite τ] :
    MeasurePreserving (gather (A := A) (B := B) (C := C) (D := D))
      ((μ.prod ν).prod (ρ.prod τ)) ((μ.prod ρ).prod (ν.prod τ)) := by
  exact ((measurePreserving_prodAssoc μ ρ (ν.prod τ)).symm MeasurableEquiv.prodAssoc).comp
    (((MeasurePreserving.id μ).prod (swapFront_preserving ν ρ τ)).comp
      (measurePreserving_prodAssoc μ ν (ρ.prod τ)))

def pairHeads : (A × B) × (C × D) × E ≃ᵐ (A × C) × B × D × E :=
  ((MeasurableEquiv.refl (A×B)).prodCongr MeasurableEquiv.prodAssoc).trans gather

theorem pairHeads_apply (x : (A × B) × (C × D) × E) :
    pairHeads x = ((x.1.1,x.2.1.1),x.1.2,x.2.1.2,x.2.2) := rfl

theorem pairHeads_preserving (μ : Measure A) (ν : Measure B) (ρ : Measure C)
    (τ : Measure D) (σ : Measure E)
    [SFinite μ] [SFinite ν] [SFinite ρ] [SFinite τ] [SFinite σ] :
    MeasurePreserving (pairHeads (A := A) (B := B) (C := C) (D := D) (E := E))
      ((μ.prod ν).prod ((ρ.prod τ).prod σ)) ((μ.prod ρ).prod (ν.prod (τ.prod σ))) := by
  exact (gather_preserving μ ν ρ (τ.prod σ)).comp
    ((MeasurePreserving.id (μ.prod ν)).prod (measurePreserving_prodAssoc ρ τ σ))

def split {n : ℕ} (i : Fin (n+1)) : (Fin (n+1) → A) ≃ᵐ A × (Fin n → A) :=
  MeasurableEquiv.piFinSuccAbove (fun _ => A) i

theorem split_head {n : ℕ} (i : Fin (n+1)) (f : Fin (n+1) → A) : (split i f).1=f i := rfl

theorem split_rest {n : ℕ} (i : Fin (n+1)) (f : Fin (n+1) → A) (j : Fin n) :
    (split i f).2 j=f (i.succAbove j) := rfl

theorem split_preserving {n : ℕ} (i : Fin (n+1)) (μ : Measure A) [SigmaFinite μ] :
    MeasurePreserving (split (A := A) i) (Measure.pi (fun _ : Fin (n+1) => μ))
      (μ.prod (Measure.pi (fun _ : Fin n => μ))) :=
  measurePreserving_piFinSuccAbove (fun _ => μ) i

end GradientHessian.ProductRearrangement
