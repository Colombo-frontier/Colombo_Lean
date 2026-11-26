import GradientHessian.ProductRearrangement

/-! Adjoining an arbitrary independent private seed preserves the exact
target-versus-external-data product factorization. -/

noncomputable section
namespace GradientHessian.RawFactorSeed
open MeasureTheory

variable {Ω Θ W Seed : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ]
  [MeasurableSpace W] [MeasurableSpace Seed]

def factor (e : Ω ≃ᵐ Θ × W) : Ω × Seed ≃ᵐ Θ × (W × Seed) :=
  (e.prodCongr (MeasurableEquiv.refl Seed)).trans MeasurableEquiv.prodAssoc

@[simp] theorem factor_apply (e : Ω ≃ᵐ Θ × W) (q : Ω × Seed) :
    factor e q=((e q.1).1,(e q.1).2,q.2) := rfl

theorem factor_preserving (e : Ω ≃ᵐ Θ × W)
    (ρ : Measure Ω) (ν : Measure Θ) (μ : Measure W) (σ : Measure Seed)
    [SFinite ρ] [SFinite ν] [SFinite μ] [SFinite σ]
    (he : MeasurePreserving e ρ (ν.prod μ)) :
    MeasurePreserving (factor e) (ρ.prod σ) (ν.prod (μ.prod σ)) :=
  (measurePreserving_prodAssoc ν μ σ).comp (he.prod (MeasurePreserving.id σ))

end GradientHessian.RawFactorSeed
