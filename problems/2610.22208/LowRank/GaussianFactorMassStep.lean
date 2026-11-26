import LowRank.GaussianFactorQueryMean

/-! Integrate the exact mass-update identity against the genuine one-step
revelation law. This is the induction step for cumulative query mass. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix BigOperators
noncomputable section

variable {E F S : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
  [MeasurableSpace S] {d t q r s : ℕ}

theorem gaussianFactor_update_A_injective_ae (ν : Measure S) [IsProbabilityMeasure ν]
    (b : OrthonormalBasis (Fin (r + 1)) ℝ E) (c : OrthonormalBasis (Fin (s + 1)) ℝ F)
    (st : S → FactorData d t q (r + 1) (s + 1)) (u : S → Fin (r + 1) → ℝ)
    (hA : ∀ᵐ x ∂ν, Function.Injective (st x).1.1.mulVec) {v : NNReal} (hv : v ≠ 0) :
    ∀ᵐ p ∂ν.prod ((iidVectorLaw (s + 1) v).prod (iidVectorLaw r v)),
      Function.Injective (updateFactorData b c (u p.1) (st p.1) p.2).1.1.mulVec := by
  let ξ := (iidVectorLaw (s + 1) v).prod (iidVectorLaw r v)
  have hp : ∀ᵐ e ∂ξ, 0 < ‖(basisCoordinates c).symm e.1‖ :=
    Measure.quasiMeasurePreserving_fst.ae (rowGauge_pivot_positive_ae c hv)
  have hp' : ∀ᵐ p ∂ν.prod ξ, 0 < ‖(basisCoordinates c).symm p.2.1‖ :=
    Measure.quasiMeasurePreserving_snd.ae hp
  have hA' : ∀ᵐ p ∂ν.prod ξ, Function.Injective (st p.1).1.1.mulVec :=
    Measure.quasiMeasurePreserving_fst.ae hA
  filter_upwards [hp', hA'] with p hρ hAp
  exact updateFactorData_A_injective b c _ _ _ hAp (ne_of_gt hρ)

theorem gaussianFactor_mass_step_mean_le (ν : Measure S) [IsProbabilityMeasure ν]
    (b : OrthonormalBasis (Fin (r + 1)) ℝ E) (c : OrthonormalBasis (Fin (s + 1)) ℝ F)
    (st : S → FactorData d t q (r + 1) (s + 1)) (u : S → Fin (r + 1) → ℝ)
    (hst : Measurable st) (hu : Measurable u) (horth : ∀ x, (st x).Orthogonal)
    (hA : ∀ᵐ x ∂ν, Function.Injective (st x).1.1.mulVec)
    (hunit : ∀ x, ‖(basisCoordinates b).symm (u x)‖ = 1)
    (hs : s ≤ r) {v : NNReal} (hv : v ≠ 0) :
    (∫ p, factorKernelMass (updateFactorData b c (u p.1.1) (st p.1.1) p.1.2) p.2
      ∂(ν.prod ((iidVectorLaw (s + 1) v).prod (iidVectorLaw r v))).prod (iidMatrixLaw r s v)) ≤
        (∫ p, factorKernelMass (st p.1) p.2 ∂ν.prod (iidMatrixLaw (r + 1) (s + 1) v)) +
          (((r + 1 : ℕ) : ℝ) - (s + 1 : ℕ)) / (r + 1 : ℕ) := by
  let μ := ν.prod (iidMatrixLaw (r + 1) (s + 1) v)
  let st' := fun p : S × ((Fin (s + 1) → ℝ) × (Fin r → ℝ)) =>
    updateFactorData b c (u p.1) (st p.1) p.2
  have hst' : Measurable st' := measurable_updateFactorData b c _ _ _
    (hu.comp measurable_fst) (hst.comp measurable_fst) measurable_snd
  have hm := measurable_factorKernelMass (st' ∘ Prod.fst) Prod.snd
    (hst'.comp measurable_fst) measurable_snd
  have hstep := adaptiveGaussianStep_preserving ν b c u hu v
  have hmap := integral_map_of_stronglyMeasurable (μ := μ) hstep.measurable hm.stronglyMeasurable
  rw [hstep.map_eq] at hmap
  dsimp only [Function.comp_def, st'] at hmap
  have hdot : ∀ x, u x ⬝ᵥ u x = 1 := fun x => basis_unit_dot b _ (hunit x)
  have hi := factorKernelMass_integrable μ (st ∘ Prod.fst) Prod.snd
    (hst.comp measurable_fst) measurable_snd (fun p => horth p.1)
  have hqi := factorQueryMass_integrable μ (st ∘ Prod.fst) Prod.snd (u ∘ Prod.fst)
    (hst.comp measurable_fst) measurable_snd (hu.comp measurable_fst)
    (fun p => horth p.1) (fun p => hdot p.1)
  calc
    _ = ∫ p, factorKernelMass (st p.1) p.2 + factorQueryMass (st p.1) p.2 (u p.1) ∂μ := by
      rw [hmap]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun p => factorKernelMass_step b c (u p.1) (hunit p.1) (st p.1) p.2)
    _ = (∫ p, factorKernelMass (st p.1) p.2 ∂μ) +
        (∫ p, factorQueryMass (st p.1) p.2 (u p.1) ∂μ) := integral_add hi hqi
    _ ≤ _ := add_le_add_left (gaussianFactor_query_mean_le ν st u hst hu horth hA hdot (by omega) hv) _

end
end LowRank
