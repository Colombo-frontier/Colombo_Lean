import GradientHessian.ProductRearrangement

/-! Composable isolation of a coordinate from finite arrays and products. -/

noncomputable section
namespace GradientHessian.ProductCoordinateFactor
open MeasureTheory ProductRearrangement

variable {A T R B : Type*} [MeasurableSpace A] [MeasurableSpace T]
  [MeasurableSpace R] [MeasurableSpace B]

def liftArray (f : A ≃ᵐ T × R) {n : ℕ} (i : Fin (n+1)) :
    (Fin (n+1) → A) ≃ᵐ T × R × (Fin n → A) :=
  (split i).trans ((f.prodCongr (MeasurableEquiv.refl (Fin n → A))).trans MeasurableEquiv.prodAssoc)

theorem liftArray_target (f : A ≃ᵐ T × R) {n : ℕ} (i : Fin (n+1)) (x : Fin (n+1) → A) :
    (liftArray f i x).1=(f (x i)).1 := rfl

theorem liftArray_preserving (f : A ≃ᵐ T × R) {n : ℕ} (i : Fin (n+1))
    (μ : Measure A) (ν : Measure T) (ρ : Measure R) [SigmaFinite μ] [SFinite ν] [SFinite ρ]
    (hf : MeasurePreserving f μ (ν.prod ρ)) :
    MeasurePreserving (liftArray f i) (Measure.pi (fun _ : Fin (n+1) => μ))
      (ν.prod (ρ.prod (Measure.pi (fun _ : Fin n => μ)))) :=
  (measurePreserving_prodAssoc ν ρ _).comp
    ((hf.prod (MeasurePreserving.id _)).comp (split_preserving i μ))

def rightFactor (f : A ≃ᵐ T × R) : B × A ≃ᵐ T × B × R :=
  ((MeasurableEquiv.refl B).prodCongr f).trans swapFront

theorem rightFactor_target (f : A ≃ᵐ T × R) (x : B × A) :
    (rightFactor f x).1=(f x.2).1 := rfl

theorem rightFactor_preserving (f : A ≃ᵐ T × R) (μ : Measure A) (ν : Measure T)
    (ρ : Measure R) (σ : Measure B) [SFinite μ] [SFinite ν] [SFinite ρ] [SFinite σ]
    (hf : MeasurePreserving f μ (ν.prod ρ)) :
    MeasurePreserving (rightFactor (B := B) f) (σ.prod μ) (ν.prod (σ.prod ρ)) :=
  (swapFront_preserving σ ν ρ).comp ((MeasurePreserving.id σ).prod hf)

def leftFactor (f : A ≃ᵐ T × R) : A × B ≃ᵐ T × R × B :=
  (f.prodCongr (MeasurableEquiv.refl B)).trans MeasurableEquiv.prodAssoc

theorem leftFactor_target (f : A ≃ᵐ T × R) (x : A × B) : (leftFactor f x).1=(f x.1).1 := rfl

theorem leftFactor_preserving (f : A ≃ᵐ T × R) (μ : Measure A) (ν : Measure T)
    (ρ : Measure R) (σ : Measure B) [SFinite μ] [SFinite ν] [SFinite ρ] [SFinite σ]
    (hf : MeasurePreserving f μ (ν.prod ρ)) :
    MeasurePreserving (leftFactor (B := B) f) (μ.prod σ) (ν.prod (ρ.prod σ)) :=
  (measurePreserving_prodAssoc ν ρ σ).comp (hf.prod (MeasurePreserving.id σ))

end GradientHessian.ProductCoordinateFactor
