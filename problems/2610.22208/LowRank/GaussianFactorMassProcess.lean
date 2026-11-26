import LowRank.GaussianFactorMassStep
import LowRank.GaussianUnitPolicy

/-! The cumulative expected kernel mass along the actual adaptive Gaussian
factor process. The induction uses the same represented input at each step
and the full enlarged-history/residual product law. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix BigOperators
noncomputable section
universe u

theorem gaussianFactor_final_mass_mean_le (d t r s n q : ℕ) {S : Type u} [MeasurableSpace S]
    (ν : Measure S) [IsProbabilityMeasure ν] (policy : GaussianPolicy r s n S)
    (hunit : GaussianPolicy.IsUnit r s n policy)
    (st : S → FactorData d t q (r + n) (s + n)) (hst : Measurable st)
    (horth : ∀ x, (st x).Orthogonal)
    (hA : ∀ᵐ x ∂ν, Function.Injective (st x).1.1.mulVec)
    (hs : s ≤ r) {v : NNReal} (hv : v ≠ 0) :
    (∫ p, factorKernelMass (finalFactorData d t r s n q policy st p.1) p.2
      ∂(gaussianHistoryLaw r s n ν v).prod (iidMatrixLaw r s v)) ≤
        (∫ p, factorKernelMass (st p.1) p.2 ∂ν.prod (iidMatrixLaw (r + n) (s + n) v)) +
          ∑ j ∈ Finset.range n, ((r : ℝ) - s) / (r + j + 1) := by
  induction n generalizing q S with
  | zero =>
    simp only [gaussianHistoryLaw, finalFactorData, Finset.range_zero, Finset.sum_empty,
      add_zero, Nat.add_zero]
    exact le_rfl
  | succ n ih =>
    let b := EuclideanSpace.basisFun (Fin (r + n + 1)) ℝ
    let c := EuclideanSpace.basisFun (Fin (s + n + 1)) ℝ
    let ξ := (iidVectorLaw (s + n + 1) v).prod (iidVectorLaw (r + n) v)
    let st' := fun p : S × ((Fin (s + n + 1) → ℝ) × (Fin (r + n) → ℝ)) =>
      updateFactorData b c (policy.1.1 p.1) (st p.1) p.2
    have hst' : Measurable st' := measurable_updateFactorData b c _ _ _
      (policy.1.2.comp measurable_fst) (hst.comp measurable_fst) measurable_snd
    have horth' : ∀ p, (st' p).Orthogonal :=
      fun p => updateFactorData_orthogonal b c _ _ _ (horth p.1)
    have hA' : ∀ᵐ p ∂ν.prod ξ, Function.Injective (st' p).1.1.mulVec :=
      gaussianFactor_update_A_injective_ae ν b c st policy.1.1 hA hv
    have htail := ih (q + 1) (ν.prod ξ) policy.2 hunit.2 st' hst' horth' hA'
    have hstep := gaussianFactor_mass_step_mean_le ν b c st policy.1.1 hst policy.1.2
      horth hA hunit.1 (by omega) hv
    have hstep' :
        (∫ p, factorKernelMass (st' p.1) p.2 ∂(ν.prod ξ).prod (iidMatrixLaw (r + n) (s + n) v)) ≤
          (∫ p, factorKernelMass (st p.1) p.2 ∂ν.prod (iidMatrixLaw (r + (n + 1)) (s + (n + 1)) v)) +
            ((r : ℝ) - s) / (r + n + 1) := by
      have he : (((r + n + 1 : ℕ) : ℝ) - (s + n + 1 : ℕ)) / (r + n + 1 : ℕ) =
          ((r : ℝ) - s) / (r + n + 1) := by push_cast; ring
      rw [he] at hstep
      simpa only [Nat.add_assoc] using hstep
    change (∫ p, factorKernelMass (finalFactorData d t r s n (q + 1) policy.2 st' p.1) p.2
      ∂(gaussianHistoryLaw r s n (ν.prod ξ) v).prod (iidMatrixLaw r s v)) ≤ _
    calc
      _ ≤ (∫ p, factorKernelMass (st' p.1) p.2 ∂(ν.prod ξ).prod (iidMatrixLaw (r + n) (s + n) v)) +
          ∑ j ∈ Finset.range n, ((r : ℝ) - s) / (r + j + 1) := htail
      _ ≤ ((∫ p, factorKernelMass (st p.1) p.2
            ∂ν.prod (iidMatrixLaw (r + (n + 1)) (s + (n + 1)) v)) + ((r : ℝ) - s) / (r + n + 1)) +
          ∑ j ∈ Finset.range n, ((r : ℝ) - s) / (r + j + 1) := add_le_add_right hstep' _
      _ = _ := by rw [Finset.sum_range_succ]; ring

theorem gaussianFactor_run_mass_mean_le (d t r s n q : ℕ) {S : Type u} [MeasurableSpace S]
    (ν : Measure S) [IsProbabilityMeasure ν] (policy : GaussianPolicy r s n S)
    (hunit : GaussianPolicy.IsUnit r s n policy)
    (st : S → FactorData d t q (r + n) (s + n)) (hst : Measurable st)
    (horth : ∀ x, (st x).Orthogonal)
    (hA : ∀ᵐ x ∂ν, Function.Injective (st x).1.1.mulVec)
    (hs : s ≤ r) {v : NNReal} (hv : v ≠ 0) :
    (∫ p, factorKernelMass
        (finalFactorData d t r s n q policy st (runGaussianPolicy r s n policy p).1)
        (runGaussianPolicy r s n policy p).2 ∂ν.prod (iidMatrixLaw (r + n) (s + n) v)) ≤
      (∫ p, factorKernelMass (st p.1) p.2 ∂ν.prod (iidMatrixLaw (r + n) (s + n) v)) +
        ∑ j ∈ Finset.range n, ((r : ℝ) - s) / (r + j + 1) := by
  have hm := measurable_factorKernelMass (finalFactorData d t r s n q policy st ∘ Prod.fst) Prod.snd
    ((measurable_finalFactorData d t r s n q policy st hst).comp measurable_fst) measurable_snd
  have hp := runGaussianPolicy_preserving r s n ν policy v
  have hi := integral_map_of_stronglyMeasurable
    (μ := ν.prod (iidMatrixLaw (r + n) (s + n) v)) hp.measurable hm.stronglyMeasurable
  rw [hp.map_eq] at hi
  dsimp only [Function.comp_def] at hi
  rw [← hi]
  exact gaussianFactor_final_mass_mean_le d t r s n q ν policy hunit st hst horth hA hs hv

end
end LowRank
