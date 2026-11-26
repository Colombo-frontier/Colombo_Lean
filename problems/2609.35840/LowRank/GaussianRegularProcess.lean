import LowRank.GaussianRevealProcess

/-! Every pivot encountered by a finite adaptive revelation process is
strictly positive almost surely when the Gaussian entry variance is positive. -/

namespace LowRank
open MeasureTheory
noncomputable section
universe u

def GaussianPolicy.Regular (r s : ℕ) : (n : ℕ) → {S : Type u} → [MeasurableSpace S] →
    GaussianPolicy r s n S → S × Matrix (Fin (r + n)) (Fin (s + n)) ℝ → Prop
  | 0, _, _, _, _ => True
  | n + 1, _, _, policy, p =>
      let b := EuclideanSpace.basisFun (Fin (r + n + 1)) ℝ
      let c := EuclideanSpace.basisFun (Fin (s + n + 1)) ℝ
      let step := adaptiveGaussianStep b c policy.1.1 p
      0 < ‖(basisCoordinates c).symm step.1.2.1‖ ∧ GaussianPolicy.Regular r s n policy.2 step

theorem gaussianPolicy_regular_ae (r s n : ℕ) {S : Type u} [MeasurableSpace S]
    (ν : Measure S) [SFinite ν] (policy : GaussianPolicy r s n S)
    {v : NNReal} (hv : v ≠ 0) :
    ∀ᵐ p ∂ν.prod (iidMatrixLaw (r + n) (s + n) v), GaussianPolicy.Regular r s n policy p := by
  induction n generalizing S with
  | zero => exact Filter.Eventually.of_forall (fun _ => trivial)
  | succ n ih =>
    let b := EuclideanSpace.basisFun (Fin (r + n + 1)) ℝ
    let c := EuclideanSpace.basisFun (Fin (s + n + 1)) ℝ
    let ξ := (iidVectorLaw (s + n + 1) v).prod (iidVectorLaw (r + n) v)
    have hp : ∀ᵐ e ∂ξ, 0 < ‖(basisCoordinates c).symm e.1‖ :=
      Measure.quasiMeasurePreserving_fst.ae (rowGauge_pivot_positive_ae c hv)
    have hp' : ∀ᵐ p ∂ν.prod ξ, 0 < ‖(basisCoordinates c).symm p.2.1‖ :=
      Measure.quasiMeasurePreserving_snd.ae hp
    have hp'' : ∀ᵐ p ∂(ν.prod ξ).prod (iidMatrixLaw (r + n) (s + n) v),
        0 < ‖(basisCoordinates c).symm p.1.2.1‖ := Measure.quasiMeasurePreserving_fst.ae hp'
    have hstep := adaptiveGaussianStep_preserving ν b c policy.1.1 policy.1.2 v
    have hfirst := hstep.quasiMeasurePreserving.ae hp''
    have htail := hstep.quasiMeasurePreserving.ae (ih (ν.prod ξ) policy.2)
    filter_upwards [hfirst, htail] with p hρ ht
    exact ⟨hρ, ht⟩

end
end LowRank
