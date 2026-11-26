import LowRank.GaussianAdaptiveStep

/-! Arbitrarily many adaptive Gaussian block revelations. The policy at each
step can use the full previous enlarged state. Dimensions decrease by one in
both directions, while the entry variance remains fixed throughout. -/

namespace LowRank
open MeasureTheory
noncomputable section

universe u

def GaussianHistory (r s : ℕ) : ℕ → Type u → Type u
  | 0, S => S
  | n + 1, S => GaussianHistory r s n
      (S × ((Fin (s + n + 1) → ℝ) × (Fin (r + n) → ℝ)))

instance gaussianHistoryMeasurable (r s n : ℕ) (S : Type u) [MeasurableSpace S] :
    MeasurableSpace (GaussianHistory r s n S) := by
  induction n generalizing S with
  | zero => exact inferInstanceAs (MeasurableSpace S)
  | succ n ih => exact ih (S × ((Fin (s + n + 1) → ℝ) × (Fin (r + n) → ℝ)))

/-- Every selected vector is jointly measurable in the current enlarged state.
The distribution invariant does not require unit length; the oracle-reply
connection separately imposes unit length. -/
def GaussianPolicy (r s : ℕ) : (n : ℕ) → (S : Type u) → [MeasurableSpace S] → Type u
  | 0, _, _ => PUnit
  | n + 1, S, _ =>
      {q : S → Fin (r + n + 1) → ℝ // Measurable q} ×
        GaussianPolicy r s n (S × ((Fin (s + n + 1) → ℝ) × (Fin (r + n) → ℝ)))

def gaussianHistoryLaw (r s : ℕ) : (n : ℕ) → {S : Type u} → [MeasurableSpace S] →
    Measure S → NNReal → Measure (GaussianHistory r s n S)
  | 0, _, _, ν, _ => ν
  | n + 1, _, _, ν, v => gaussianHistoryLaw r s n
      (ν.prod ((iidVectorLaw (s + n + 1) v).prod (iidVectorLaw (r + n) v))) v

instance gaussianHistoryLaw_sfinite (r s n : ℕ) {S : Type u} [MeasurableSpace S]
    (ν : Measure S) [SFinite ν] (v : NNReal) : SFinite (gaussianHistoryLaw r s n ν v) := by
  induction n generalizing S with
  | zero => exact inferInstanceAs (SFinite ν)
  | succ n ih =>
    exact ih (ν.prod ((iidVectorLaw (s + n + 1) v).prod (iidVectorLaw (r + n) v)))

instance gaussianHistoryLaw_probability (r s n : ℕ) {S : Type u} [MeasurableSpace S]
    (ν : Measure S) [IsProbabilityMeasure ν] (v : NNReal) :
    IsProbabilityMeasure (gaussianHistoryLaw r s n ν v) := by
  induction n generalizing S with
  | zero => exact inferInstanceAs (IsProbabilityMeasure ν)
  | succ n ih =>
    exact ih (ν.prod ((iidVectorLaw (s + n + 1) v).prod (iidVectorLaw (r + n) v)))

def runGaussianPolicy (r s : ℕ) : (n : ℕ) → {S : Type u} → [MeasurableSpace S] →
    GaussianPolicy r s n S →
    S × Matrix (Fin (r + n)) (Fin (s + n)) ℝ →
    GaussianHistory r s n S × Matrix (Fin r) (Fin s) ℝ
  | 0, _, _, _, p => p
  | n + 1, _, _, policy, p => runGaussianPolicy r s n policy.2
      (adaptiveGaussianStep (EuclideanSpace.basisFun (Fin (r + n + 1)) ℝ)
        (EuclideanSpace.basisFun (Fin (s + n + 1)) ℝ) policy.1.1 p)

/-- The entire adaptive process sends the original product law to a product
law of enlarged history and a smaller iid Gaussian block. -/
theorem runGaussianPolicy_preserving (r s n : ℕ) {S : Type u} [MeasurableSpace S]
    (ν : Measure S) [SFinite ν] (policy : GaussianPolicy r s n S) (v : NNReal) :
    MeasurePreserving (runGaussianPolicy r s n policy)
      (ν.prod (iidMatrixLaw (r + n) (s + n) v))
      ((gaussianHistoryLaw r s n ν v).prod (iidMatrixLaw r s v)) := by
  induction n generalizing S with
  | zero => exact MeasurePreserving.id _
  | succ n ih =>
    have hstep := adaptiveGaussianStep_preserving ν
      (EuclideanSpace.basisFun (Fin (r + n + 1)) ℝ)
      (EuclideanSpace.basisFun (Fin (s + n + 1)) ℝ) policy.1.1 policy.1.2 v
    exact (ih (ν.prod ((iidVectorLaw (s + n + 1) v).prod (iidVectorLaw (r + n) v)))
      policy.2).comp hstep

theorem runGaussianPolicy_residual_law (r s n : ℕ) {S : Type u} [MeasurableSpace S]
    (ν : Measure S) [IsProbabilityMeasure ν] (policy : GaussianPolicy r s n S) (v : NNReal) :
    (ν.prod (iidMatrixLaw (r + n) (s + n) v)).map
      (fun p => (runGaussianPolicy r s n policy p).2) = iidMatrixLaw r s v := by
  have h := runGaussianPolicy_preserving r s n ν policy v
  calc
    _ = ((ν.prod (iidMatrixLaw (r + n) (s + n) v)).map
        (runGaussianPolicy r s n policy)).map Prod.snd :=
      (Measure.map_map measurable_snd h.measurable).symm
    _ = _ := by rw [h.map_eq]; simp

theorem runGaussianPolicy_independent (r s n : ℕ) {S : Type u} [MeasurableSpace S]
    (ν : Measure S) [IsProbabilityMeasure ν] (policy : GaussianPolicy r s n S) (v : NNReal) :
    ProbabilityTheory.IndepFun (fun p => (runGaussianPolicy r s n policy p).1)
      (fun p => (runGaussianPolicy r s n policy p).2)
      (ν.prod (iidMatrixLaw (r + n) (s + n) v)) := by
  have h := runGaussianPolicy_preserving r s n ν policy v
  rw [ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map h.measurable.fst.aemeasurable
    h.measurable.snd.aemeasurable]
  change (ν.prod (iidMatrixLaw (r + n) (s + n) v)).map (runGaussianPolicy r s n policy) = _
  rw [h.map_eq, runGaussianPolicy_residual_law]
  congr 1
  symm
  calc
    _ = ((ν.prod (iidMatrixLaw (r + n) (s + n) v)).map
        (runGaussianPolicy r s n policy)).map Prod.fst :=
      (Measure.map_map measurable_fst h.measurable).symm
    _ = _ := by rw [h.map_eq]; simp

end
end LowRank
