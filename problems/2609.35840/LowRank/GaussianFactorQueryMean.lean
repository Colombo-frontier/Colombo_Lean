import LowRank.FactorKernelMass
import Mathlib.MeasureTheory.Integral.Prod

/-! A unit query at an arbitrary exposed factor state. The state is
independent of the iid residual block; the query may depend measurably on
the entire exposed state. Its mean kernel mass is at most (r-s)/r. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix BigOperators
noncomputable section

theorem kernelProjector_comp_entryIntegrable {Ω a b : Type*} [MeasurableSpace Ω]
    [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → Matrix a b ℝ) (hX : Measurable X) :
    EntryIntegrable (fun ω => leftKernelProjector (X ω)) μ := by
  intro i j
  have hm := (measurable_pi_apply j).comp ((measurable_pi_apply i).comp
    (measurable_leftKernelProjector.comp hX))
  exact (integrable_const (1 : ℝ)).mono' hm.stronglyMeasurable.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun ω => (leftKernelProjector_isProjector (X ω)).entry_norm_le_one i j))

theorem factorQueryMass_integrable {Ω : Type*} [MeasurableSpace Ω] {d t q r s : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (st : Ω → FactorData d t q r s) (D : Ω → Matrix (Fin r) (Fin s) ℝ)
    (u : Ω → Fin r → ℝ) (hst : Measurable st) (hD : Measurable D) (hu : Measurable u)
    (horth : ∀ ω, (st ω).Orthogonal) (hunit : ∀ ω, u ω ⬝ᵥ u ω = 1) :
    Integrable (fun ω => factorQueryMass (st ω) (D ω) (u ω)) μ := by
  exact unit_quadratic_integrable μ u
    (fun i => ((measurable_pi_apply i).comp hu).stronglyMeasurable.aestronglyMeasurable)
    (Filter.Eventually.of_forall hunit)
    (fun ω => (factorKernelProjector (st ω) (D ω)).submatrix Sum.inr Sum.inr)
    (fun i j => factorKernelProjector_entryIntegrable μ st D hst hD horth (Sum.inr i) (Sum.inr j))

theorem gaussianFactor_query_mean_le {S : Type*} [MeasurableSpace S] {d t q r s : ℕ}
    (ν : Measure S) [IsProbabilityMeasure ν] (st : S → FactorData d t q r s)
    (u : S → Fin r → ℝ) (hst : Measurable st) (hu : Measurable u)
    (horth : ∀ x, (st x).Orthogonal)
    (hA : ∀ᵐ x ∂ν, Function.Injective (st x).1.1.mulVec)
    (hunit : ∀ x, u x ⬝ᵥ u x = 1) (hs : s ≤ r) {v : NNReal} (hv : v ≠ 0) :
    (∫ p, factorQueryMass (st p.1) p.2 (u p.1) ∂ν.prod (iidMatrixLaw r s v)) ≤
      ((r : ℝ) - s) / r := by
  let μ := ν.prod (iidMatrixLaw r s v)
  have hF : Integrable (fun p => factorQueryMass (st p.1) p.2 (u p.1)) μ :=
    factorQueryMass_integrable μ (st ∘ Prod.fst) Prod.snd (u ∘ Prod.fst)
      (hst.comp measurable_fst) measurable_snd (hu.comp measurable_fst)
      (fun p => horth p.1) (fun p => hunit p.1)
  have hG : Integrable (fun p : S × Matrix (Fin r) (Fin s) ℝ =>
      u p.1 ⬝ᵥ (leftKernelProjector p.2 *ᵥ u p.1)) μ :=
    unit_quadratic_integrable μ (u ∘ Prod.fst)
      (fun i => ((measurable_pi_apply i).comp (hu.comp measurable_fst)).stronglyMeasurable.aestronglyMeasurable)
      (Filter.Eventually.of_forall (fun p => hunit p.1))
      (fun p => leftKernelProjector p.2) (kernelProjector_comp_entryIntegrable μ Prod.snd measurable_snd)
  have hAle : ∀ᵐ p ∂μ, Function.Injective (st p.1).1.1.mulVec :=
    Measure.quasiMeasurePreserving_fst.ae hA
  have hDle : ∀ᵐ p ∂μ, Function.Injective p.2.mulVec :=
    Measure.quasiMeasurePreserving_snd.ae (iidMatrixLaw_mulVec_injective_ae r s hs hv)
  have hle : ∀ᵐ p ∂μ, factorQueryMass (st p.1) p.2 (u p.1) ≤
      u p.1 ⬝ᵥ (leftKernelProjector p.2 *ᵥ u p.1) := by
    filter_upwards [hAle, hDle] with p hA hD
    exact loewner_quadratic_le (factorKernelProjector_bottom_le_of_blocks (st p.1) p.2
      (horth p.1) hA hD) (u p.1)
  have hmean : (∫ p : S × Matrix (Fin r) (Fin s) ℝ,
      u p.1 ⬝ᵥ (leftKernelProjector p.2 *ᵥ u p.1) ∂μ) = ((r : ℝ) - s) / r := by
    rw [integral_prod _ hG]
    have hi : ∀ x, (∫ D, u x ⬝ᵥ (leftKernelProjector D *ᵥ u x) ∂iidMatrixLaw r s v) =
        ((r : ℝ) - s) / r := by
      intro x
      rw [integral_quadratic (leftKernelProjector_entryIntegrable _), gaussianKernelMean_isotropic r s hs hv]
      simp only [Matrix.smul_mulVec_assoc, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul, hunit, mul_one]
    simp only [hi, integral_const, measureReal_univ_eq_one, one_smul]
  exact (integral_mono_ae hF hG hle).trans_eq hmean

end
end LowRank
