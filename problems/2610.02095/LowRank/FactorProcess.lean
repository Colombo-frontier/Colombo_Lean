import LowRank.FactorDataMeasurable
import LowRank.GaussianRevealProcess

/-! Cumulative complete factorization along the actual adaptive Gaussian
revelation process. The final factors reconstruct the same ambient matrix.
Their measurable dependence on the enlarged history preserves independence
of the remaining Gaussian block. -/

namespace LowRank
open Matrix MeasureTheory
noncomputable section
universe u

/-- Recursive indexing avoids transports at every revelation. -/
def factorCount : ℕ → ℕ → ℕ
  | 0, q => q
  | n + 1, q => factorCount n (q + 1)

theorem factorCount_eq (n q : ℕ) : factorCount n q = q + n := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih => simp only [factorCount, ih]; omega

def finalFactorData (d t r s : ℕ) : (n q : ℕ) → {S : Type u} → [MeasurableSpace S] →
    GaussianPolicy r s n S → (S → FactorData d t q (r + n) (s + n)) →
    GaussianHistory r s n S → FactorData d t (factorCount n q) r s
  | 0, _, _, _, _, st => st
  | n + 1, q, _, _, policy, st => finalFactorData d t r s n (q + 1) policy.2
      (fun p => updateFactorData (EuclideanSpace.basisFun (Fin (r + n + 1)) ℝ)
        (EuclideanSpace.basisFun (Fin (s + n + 1)) ℝ) (policy.1.1 p.1) (st p.1) p.2)

theorem measurable_finalFactorData (d t r s n q : ℕ) {S : Type u} [MeasurableSpace S]
    (policy : GaussianPolicy r s n S) (st : S → FactorData d t q (r + n) (s + n))
    (hst : Measurable st) : Measurable (finalFactorData d t r s n q policy st) := by
  induction n generalizing q S with
  | zero => exact hst
  | succ n ih =>
    exact ih (q + 1) policy.2 _
      (measurable_updateFactorData _ _ _ _ _ (policy.1.2.comp measurable_fst)
        (hst.comp measurable_fst) measurable_snd)

theorem finalFactorData_orthogonal (d t r s n q : ℕ) {S : Type u} [MeasurableSpace S]
    (policy : GaussianPolicy r s n S) (st : S → FactorData d t q (r + n) (s + n))
    (hst : ∀ x, (st x).Orthogonal) (h : GaussianHistory r s n S) :
    (finalFactorData d t r s n q policy st h).Orthogonal := by
  induction n generalizing q S with
  | zero => exact hst h
  | succ n ih =>
    exact ih (q + 1) policy.2 _
      (fun p => updateFactorData_orthogonal _ _ _ _ _ (hst p.1)) h

/-- No probabilistic or unit-vector premise is required for reconstruction. -/
theorem finalFactorData_preserves_matrix (d t r s n q : ℕ) {S : Type u} [MeasurableSpace S]
    (policy : GaussianPolicy r s n S) (st : S → FactorData d t q (r + n) (s + n))
    (p : S × Matrix (Fin (r + n)) (Fin (s + n)) ℝ) :
    let out := runGaussianPolicy r s n policy p
    representedMatrix (finalFactorData d t r s n q policy st out.1) out.2 =
      representedMatrix (st p.1) p.2 := by
  induction n generalizing q S with
  | zero => rfl
  | succ n ih =>
    let b := EuclideanSpace.basisFun (Fin (r + n + 1)) ℝ
    let c := EuclideanSpace.basisFun (Fin (s + n + 1)) ℝ
    let st' := fun z : S × ((Fin (s + n + 1) → ℝ) × (Fin (r + n) → ℝ)) =>
      updateFactorData b c (policy.1.1 z.1) (st z.1) z.2
    let step := adaptiveGaussianStep b c policy.1.1 p
    change representedMatrix (finalFactorData d t r s n (q + 1) policy.2 st'
      (runGaussianPolicy r s n policy.2 step).1)
      (runGaussianPolicy r s n policy.2 step).2 = _
    rw [ih (q + 1) policy.2 st' step]
    exact updateFactorData_preserves_matrix b c (policy.1.1 p.1) (st p.1) p.2

theorem finalFactorData_residual_independent (d t r s n q : ℕ) {S : Type u}
    [MeasurableSpace S] (ν : Measure S) [IsProbabilityMeasure ν]
    (policy : GaussianPolicy r s n S) (st : S → FactorData d t q (r + n) (s + n))
    (hst : Measurable st) (v : NNReal) :
    ProbabilityTheory.IndepFun
      (fun p => finalFactorData d t r s n q policy st (runGaussianPolicy r s n policy p).1)
      (fun p => (runGaussianPolicy r s n policy p).2)
      (ν.prod (iidMatrixLaw (r + n) (s + n) v)) := by
  exact (runGaussianPolicy_independent r s n ν policy v).comp
    (measurable_finalFactorData d t r s n q policy st hst) measurable_id

theorem finalFactorData_joint_law (d t r s n q : ℕ) {S : Type u} [MeasurableSpace S]
    (ν : Measure S) [SFinite ν] (policy : GaussianPolicy r s n S)
    (st : S → FactorData d t q (r + n) (s + n)) (hst : Measurable st) (v : NNReal) :
    MeasurePreserving
      (fun p => (finalFactorData d t r s n q policy st (runGaussianPolicy r s n policy p).1,
        (runGaussianPolicy r s n policy p).2))
      (ν.prod (iidMatrixLaw (r + n) (s + n) v))
      (((gaussianHistoryLaw r s n ν v).map (finalFactorData d t r s n q policy st)).prod
        (iidMatrixLaw r s v)) := by
  have hf : MeasurePreserving (finalFactorData d t r s n q policy st)
      (gaussianHistoryLaw r s n ν v)
      ((gaussianHistoryLaw r s n ν v).map (finalFactorData d t r s n q policy st)) :=
    ⟨measurable_finalFactorData d t r s n q policy st hst, rfl⟩
  exact (hf.prod (MeasurePreserving.id (iidMatrixLaw r s v))).comp
    (runGaussianPolicy_preserving r s n ν policy v)

end
end LowRank
