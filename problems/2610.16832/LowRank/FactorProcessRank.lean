import LowRank.FactorProcess

/-! Nonzero Gaussian pivots keep every exposed square block nonsingular
throughout the cumulative adaptive factorization. -/

namespace LowRank
open Matrix MeasureTheory
noncomputable section
universe u

theorem finalFactorData_A_injective_ae (d t r s n q : ℕ) {S : Type u}
    [MeasurableSpace S] (ν : Measure S) [SFinite ν]
    (policy : GaussianPolicy r s n S) (st : S → FactorData d t q (r + n) (s + n))
    {v : NNReal} (hv : v ≠ 0)
    (hA : ∀ᵐ x ∂ν, Function.Injective (Matrix.mulVec (st x).1.1)) :
    ∀ᵐ h ∂gaussianHistoryLaw r s n ν v,
      Function.Injective (Matrix.mulVec (finalFactorData d t r s n q policy st h).1.1) := by
  induction n generalizing q S with
  | zero => exact hA
  | succ n ih =>
    let b := EuclideanSpace.basisFun (Fin (r + n + 1)) ℝ
    let c := EuclideanSpace.basisFun (Fin (s + n + 1)) ℝ
    let ξ := (iidVectorLaw (s + n + 1) v).prod (iidVectorLaw (r + n) v)
    have hp : ∀ᵐ e ∂ξ, 0 < ‖(basisCoordinates c).symm e.1‖ :=
      Measure.quasiMeasurePreserving_fst.ae (rowGauge_pivot_positive_ae c hv)
    have hp' : ∀ᵐ p ∂ν.prod ξ, 0 < ‖(basisCoordinates c).symm p.2.1‖ :=
      Measure.quasiMeasurePreserving_snd.ae hp
    have hA' : ∀ᵐ p ∂ν.prod ξ, Function.Injective (Matrix.mulVec (st p.1).1.1) :=
      Measure.quasiMeasurePreserving_fst.ae hA
    apply ih (q + 1) (ν.prod ξ) policy.2
      (fun p => updateFactorData b c (policy.1.1 p.1) (st p.1) p.2)
    filter_upwards [hp', hA'] with p hρ hAp
    exact updateFactorData_A_injective b c _ _ _ hAp (ne_of_gt hρ)

theorem runGaussianPolicy_factor_A_injective_ae (d t r s n q : ℕ) {S : Type u}
    [MeasurableSpace S] (ν : Measure S) [SFinite ν]
    (policy : GaussianPolicy r s n S) (st : S → FactorData d t q (r + n) (s + n))
    {v : NNReal} (hv : v ≠ 0)
    (hA : ∀ᵐ x ∂ν, Function.Injective (Matrix.mulVec (st x).1.1)) :
    ∀ᵐ p ∂ν.prod (iidMatrixLaw (r + n) (s + n) v),
      Function.Injective (Matrix.mulVec
        (finalFactorData d t r s n q policy st (runGaussianPolicy r s n policy p).1).1.1) := by
  have h := finalFactorData_A_injective_ae d t r s n q ν policy st hv hA
  have hp : ∀ᵐ p ∂(gaussianHistoryLaw r s n ν v).prod (iidMatrixLaw r s v),
      Function.Injective (Matrix.mulVec (finalFactorData d t r s n q policy st p.1).1.1) :=
    Measure.quasiMeasurePreserving_fst.ae h
  exact (runGaussianPolicy_preserving r s n ν policy v).quasiMeasurePreserving.ae hp

end
end LowRank
