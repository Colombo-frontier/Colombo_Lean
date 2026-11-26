import LowRank.GaussianFactorNoAtoms
import LowRank.FactorInitial

/-! Integrate conditional nonconcentration over the whole revealed history,
then pull it back to the original random matrix and random seed. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix
noncomputable section

theorem measurable_representedMatrix {S : Type*} [MeasurableSpace S] {d t q r s : ℕ}
    (st : S → FactorData d t q r s) (D : S → Matrix (Fin r) (Fin s) ℝ)
    (hst : Measurable st) (hD : Measurable D) :
    Measurable (fun x => representedMatrix (st x) (D x)) := by
  have hc : Measurable (fun x => fromBlocks (st x).1.1 0 (st x).1.2 (D x)) := by
    apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro j
    cases i <;> cases j <;> simp only [fromBlocks_apply₁₁, fromBlocks_apply₁₂,
      fromBlocks_apply₂₁, fromBlocks_apply₂₂] <;> fun_prop
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  simp only [representedMatrix, Matrix.mul_apply, Matrix.transpose_apply]
  fun_prop

theorem history_annihilator_zero_ae {S : Type*} [MeasurableSpace S]
    (ν : Measure S) [SFinite ν] {d t q r s : ℕ} (hs : 0 < s)
    {v : NNReal} (hv : v ≠ 0) (st : S → FactorData d t q r s) (hst : Measurable st)
    (ho : ∀ᵐ x ∂ν, (st x).Orthogonal) (hA : ∀ᵐ x ∂ν, IsUnit (st x).1.1)
    (Q : S → Matrix (Fin d) (Fin d) ℝ) (hQ : Measurable Q) :
    ∀ᵐ p ∂ν.prod (iidMatrixLaw r s v),
      Q p.1 * representedMatrix (st p.1) p.2 = 0 → Q p.1 = 0 := by
  have hx := measurable_representedMatrix (fun p : S × Matrix (Fin r) (Fin s) ℝ => st p.1)
    Prod.snd (hst.comp measurable_fst) measurable_snd
  have hm : Measurable (fun p : S × Matrix (Fin r) (Fin s) ℝ =>
      Q p.1 * representedMatrix (st p.1) p.2) := by
    apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro j
    simp only [Matrix.mul_apply]
    fun_prop
  have he : MeasurableSet {p : S × Matrix (Fin r) (Fin s) ℝ |
      Q p.1 * representedMatrix (st p.1) p.2 = 0 → Q p.1 = 0} := by
    simp only [imp_iff_not_or]
    exact ((measurableSet_singleton 0).preimage hm).compl.union
      ((measurableSet_singleton 0).preimage (hQ.comp measurable_fst))
  apply (Measure.ae_prod_iff_ae_ae he).mpr
  filter_upwards [ho, hA] with x hox hAx
  by_cases hzero : Q x = 0
  · exact Filter.Eventually.of_forall (fun _ _ => hzero)
  · filter_upwards [representedMatrix_annihilator_ne_ae hs hv (st x) hox hAx (Q x) hzero]
      with D hD
    exact fun h => (hD h).elim

theorem gaussianPolicy_annihilator_zero_ae (r s n : ℕ) (hs : 0 < s)
    {S : Type*} [MeasurableSpace S] (ν : Measure S) [SFinite ν]
    (policy : GaussianPolicy r s n S) {v : NNReal} (hv : v ≠ 0)
    (Q : GaussianHistory r s n S → Matrix (Fin (r + n)) (Fin (r + n)) ℝ)
    (hQ : Measurable Q) :
    ∀ᵐ p ∂ν.prod (iidMatrixLaw (r + n) (s + n) v),
      Q (runGaussianPolicy r s n policy p).1 * p.2 = 0 →
        Q (runGaussianPolicy r s n policy p).1 = 0 := by
  let st := finalFactorData (r + n) (s + n) r s n 0 policy
    (fun _ => initialFactorData (r + n) (s + n))
  have ho : ∀ᵐ h ∂gaussianHistoryLaw r s n ν v, (st h).Orthogonal :=
    Filter.Eventually.of_forall (fun h => finalFactorData_orthogonal _ _ _ _ _ _ policy _
      (fun _ => initialFactorData_orthogonal _ _) h)
  have hA : ∀ᵐ h ∂gaussianHistoryLaw r s n ν v, IsUnit (st h).1.1 := by
    filter_upwards [finalFactorData_A_injective_ae (r + n) (s + n) r s n 0 ν policy
      (fun _ => initialFactorData (r + n) (s + n)) hv
      (Filter.Eventually.of_forall (fun _ => initialFactorData_A_injective _ _))] with h hh
    exact Matrix.mulVec_injective_iff_isUnit.mp hh
  have hprod := history_annihilator_zero_ae (gaussianHistoryLaw r s n ν v) hs hv st
    (measurable_finalFactorData _ _ _ _ _ _ policy _ measurable_const) ho hA Q hQ
  have hactual := (runGaussianPolicy_preserving r s n ν policy v).quasiMeasurePreserving.ae hprod
  filter_upwards [hactual] with p hp
  simpa only [st, initialFactorData_final_reconstruct] using hp

end
end LowRank
