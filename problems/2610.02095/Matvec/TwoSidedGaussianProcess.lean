import Matvec.TwoSidedGaussianStep
import LowRank.GaussianRevealProcess

/-!
# Finite adaptive two-sided Gaussian revelation processes

At every step both query directions are arbitrary measurable functions of the
entire previously exposed state. This constructs the finite process and proves
its joint law by induction from the actual two-sided step, without a posterior
assumption. The exposed-history type and product measure are shared with the
existing coordinate-revelation library because the recorded coordinate sizes
are identical; the policy and execution below are genuinely two-sided.
-/

namespace Matvec
open Matrix MeasureTheory ProbabilityTheory
noncomputable section
universe u

/-- A fixed-horizon policy may inspect every prior exposed coordinate when
selecting either query direction. No normalization assumption is imposed. -/
def TwoSidedPolicy (r s : ℕ) : (n : ℕ) → (S : Type u) → [MeasurableSpace S] → Type u
  | 0, _, _ => PUnit
  | n + 1, S, _ =>
      ({q : S → Fin (r + n + 1) → ℝ // Measurable q} ×
        {q : S → Fin (s + n + 1) → ℝ // Measurable q}) ×
      TwoSidedPolicy r s n (S × ((Fin (s + n + 1) → ℝ) × (Fin (r + n) → ℝ)))

def runTwoSidedPolicy (r s : ℕ) : (n : ℕ) → {S : Type u} → [MeasurableSpace S] →
    TwoSidedPolicy r s n S → S × Matrix (Fin (r + n)) (Fin (s + n)) ℝ →
    LowRank.GaussianHistory r s n S × Matrix (Fin r) (Fin s) ℝ
  | 0, _, _, _, p => p
  | n + 1, _, _, policy, p => runTwoSidedPolicy r s n policy.2
      (twoSidedGaussianStep
        (fun z => queryGauge (EuclideanSpace.basisFun (Fin (r + n + 1)) ℝ) (policy.1.1.1 z))
        (fun z => queryGauge (EuclideanSpace.basisFun (Fin (s + n + 1)) ℝ) (policy.1.2.1 z)) p)

/-- The entire process preserves the product of exposed-history law and a
fresh iid Gaussian residual, with unchanged entry variance. -/
theorem runTwoSidedPolicy_preserving (r s n : ℕ) {S : Type u} [MeasurableSpace S]
    (ν : Measure S) [SFinite ν] (policy : TwoSidedPolicy r s n S) (v : NNReal) :
    MeasurePreserving (runTwoSidedPolicy r s n policy)
      (ν.prod (LowRank.iidMatrixLaw (r + n) (s + n) v))
      ((LowRank.gaussianHistoryLaw r s n ν v).prod (LowRank.iidMatrixLaw r s v)) := by
  induction n generalizing S with
  | zero => exact MeasurePreserving.id _
  | succ n ih =>
    have hs := queryGaussianStep_preserving ν
      (EuclideanSpace.basisFun (Fin (r + n + 1)) ℝ)
      (EuclideanSpace.basisFun (Fin (s + n + 1)) ℝ)
      policy.1.1.1 policy.1.2.1 policy.1.1.2 policy.1.2.2 v
    exact (ih (ν.prod ((LowRank.iidVectorLaw (s + n + 1) v).prod
      (LowRank.iidVectorLaw (r + n) v))) policy.2).comp hs

theorem runTwoSidedPolicy_residual_law (r s n : ℕ) {S : Type u} [MeasurableSpace S]
    (ν : Measure S) [IsProbabilityMeasure ν] (policy : TwoSidedPolicy r s n S) (v : NNReal) :
    (ν.prod (LowRank.iidMatrixLaw (r + n) (s + n) v)).map
      (fun p => (runTwoSidedPolicy r s n policy p).2) = LowRank.iidMatrixLaw r s v := by
  have hp := runTwoSidedPolicy_preserving r s n ν policy v
  calc
    _ = ((ν.prod (LowRank.iidMatrixLaw (r + n) (s + n) v)).map
        (runTwoSidedPolicy r s n policy)).map Prod.snd :=
      (Measure.map_map measurable_snd hp.measurable).symm
    _ = _ := by rw [hp.map_eq]; simp

theorem runTwoSidedPolicy_independent (r s n : ℕ) {S : Type u} [MeasurableSpace S]
    (ν : Measure S) [IsProbabilityMeasure ν] (policy : TwoSidedPolicy r s n S) (v : NNReal) :
    IndepFun (fun p => (runTwoSidedPolicy r s n policy p).1)
      (fun p => (runTwoSidedPolicy r s n policy p).2)
      (ν.prod (LowRank.iidMatrixLaw (r + n) (s + n) v)) := by
  have hp := runTwoSidedPolicy_preserving r s n ν policy v
  rw [indepFun_iff_map_prod_eq_prod_map_map hp.measurable.fst.aemeasurable
    hp.measurable.snd.aemeasurable]
  change (ν.prod (LowRank.iidMatrixLaw (r + n) (s + n) v)).map
    (runTwoSidedPolicy r s n policy) = _
  rw [hp.map_eq, runTwoSidedPolicy_residual_law]
  congr 1
  symm
  calc
    _ = ((ν.prod (LowRank.iidMatrixLaw (r + n) (s + n) v)).map
        (runTwoSidedPolicy r s n policy)).map Prod.fst :=
      (Measure.map_map measurable_fst hp.measurable).symm
    _ = _ := by rw [hp.map_eq]; simp

/-- Any measurable decoding of the enlarged history remains independent of
the residual. A concrete oracle compiler must separately prove its replay identity. -/
theorem runTwoSidedPolicy_decoded_independent (r s n : ℕ) {S T : Type u}
    [MeasurableSpace S] [MeasurableSpace T]
    (ν : Measure S) [IsProbabilityMeasure ν] (policy : TwoSidedPolicy r s n S) (v : NNReal)
    (decode : LowRank.GaussianHistory r s n S → T) (hdecode : Measurable decode) :
    IndepFun (fun p => decode (runTwoSidedPolicy r s n policy p).1)
      (fun p => (runTwoSidedPolicy r s n policy p).2)
      (ν.prod (LowRank.iidMatrixLaw (r + n) (s + n) v)) := by
  simpa only [Function.comp_def, id_eq] using
    (runTwoSidedPolicy_independent r s n ν policy v).comp hdecode measurable_id

theorem runTwoSidedPolicy_conditional_bounded (r s n : ℕ) {S : Type u} [MeasurableSpace S]
    (ν : Measure S) [IsProbabilityMeasure ν] (policy : TwoSidedPolicy r s n S) (v : NNReal)
    (φ : Matrix (Fin r) (Fin s) ℝ → ℝ) (hφ : Measurable φ)
    (C : ℝ) (hbound : ∀ D, ‖φ D‖ ≤ C) :
    let μ := ν.prod (LowRank.iidMatrixLaw (r + n) (s + n) v)
    let T := fun p => (runTwoSidedPolicy r s n policy p).1
    let Z := fun p => (runTwoSidedPolicy r s n policy p).2
    Integrable (φ ∘ Z) μ ∧
      μ[φ ∘ Z | MeasurableSpace.comap T inferInstance] =ᵐ[μ]
        (fun _ => ∫ D, φ D ∂LowRank.iidMatrixLaw r s v) := by
  let μ := ν.prod (LowRank.iidMatrixLaw (r + n) (s + n) v)
  let T := fun p => (runTwoSidedPolicy r s n policy p).1
  let Z := fun p => (runTwoSidedPolicy r s n policy p).2
  have hp := runTwoSidedPolicy_preserving r s n ν policy v
  have hT : Measurable T := hp.measurable.fst
  have hZ : Measurable Z := hp.measurable.snd
  have hZlaw : MeasurePreserving Z μ (LowRank.iidMatrixLaw r s v) :=
    ⟨hZ, runTwoSidedPolicy_residual_law r s n ν policy v⟩
  have hφint : Integrable φ (LowRank.iidMatrixLaw r s v) :=
    (integrable_const C).mono' hφ.stronglyMeasurable.aestronglyMeasurable
      (Filter.Eventually.of_forall hbound)
  refine ⟨(hZlaw.integrable_comp hφ.stronglyMeasurable.aestronglyMeasurable).mpr hφint, ?_⟩
  have hind : IndepFun Z T μ := (runTwoSidedPolicy_independent r s n ν policy v).symm
  have hsm : StronglyMeasurable[(inferInstance : MeasurableSpace (Matrix (Fin r) (Fin s) ℝ)).comap Z]
      (φ ∘ Z) := (hφ.comp (comap_measurable Z)).stronglyMeasurable
  have hc := condExp_indep_eq hZ.comap_le hT.comap_le hsm ((IndepFun_iff_Indep Z T μ).mp hind)
  have hi : (∫ p, φ (Z p) ∂μ) = ∫ D, φ D ∂LowRank.iidMatrixLaw r s v := by
    rw [← hZlaw.map_eq, integral_map_of_stronglyMeasurable hZ hφ.stronglyMeasurable]
  simpa only [Function.comp_def, hi] using hc

end
end Matvec
