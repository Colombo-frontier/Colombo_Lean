import LowRank.GaussianMatrixColumns

/-! A genuine adaptive revelation step: rotate the hidden row space using a
measurable query chosen from the prior state, then reveal one row and column.
The residual has the same scalar variance and remains independent of the
entire enlarged state. -/

namespace LowRank
open MeasureTheory
noncomputable section

variable {E F S : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
  [MeasurableSpace S] {r s : ℕ}

def adaptiveGaussianStep (b : OrthonormalBasis (Fin (r + 1)) ℝ E)
    (c : OrthonormalBasis (Fin (s + 1)) ℝ F) (q : S → Fin (r + 1) → ℝ)
    (p : S × Matrix (Fin (r + 1)) (Fin (s + 1)) ℝ) :
    (S × ((Fin (s + 1) → ℝ) × (Fin r → ℝ))) × Matrix (Fin r) (Fin s) ℝ :=
  let Y := rotateMatrixColumns b (rowGauge b (q p.1)) p.2
  let out := revealGaussianBlock c Y
  ((p.1, out.1), out.2)

theorem adaptiveGaussianStep_preserving (ν : Measure S) [SFinite ν]
    (b : OrthonormalBasis (Fin (r + 1)) ℝ E) (c : OrthonormalBasis (Fin (s + 1)) ℝ F)
    (q : S → Fin (r + 1) → ℝ) (hq : Measurable q) (v : NNReal) :
    MeasurePreserving (adaptiveGaussianStep b c q)
      (ν.prod (iidMatrixLaw (r + 1) (s + 1) v))
      ((ν.prod ((iidVectorLaw (s + 1) v).prod (iidVectorLaw r v))).prod (iidMatrixLaw r s v)) := by
  exact (revealGaussianBlock_with_state ν c v).comp
    (query_rotation_preserving ν b q hq v)

theorem adaptiveGaussianStep_residual_law (ν : Measure S) [IsProbabilityMeasure ν]
    (b : OrthonormalBasis (Fin (r + 1)) ℝ E) (c : OrthonormalBasis (Fin (s + 1)) ℝ F)
    (q : S → Fin (r + 1) → ℝ) (hq : Measurable q) (v : NNReal) :
    (ν.prod (iidMatrixLaw (r + 1) (s + 1) v)).map
      (fun p => (adaptiveGaussianStep b c q p).2) = iidMatrixLaw r s v := by
  have h := adaptiveGaussianStep_preserving ν b c q hq v
  calc
    _ = ((ν.prod (iidMatrixLaw (r + 1) (s + 1) v)).map
        (adaptiveGaussianStep b c q)).map Prod.snd :=
      (Measure.map_map measurable_snd h.measurable).symm
    _ = _ := by rw [h.map_eq]; simp

theorem adaptiveGaussianStep_independent (ν : Measure S) [IsProbabilityMeasure ν]
    (b : OrthonormalBasis (Fin (r + 1)) ℝ E) (c : OrthonormalBasis (Fin (s + 1)) ℝ F)
    (q : S → Fin (r + 1) → ℝ) (hq : Measurable q) (v : NNReal) :
    ProbabilityTheory.IndepFun (fun p => (adaptiveGaussianStep b c q p).1)
      (fun p => (adaptiveGaussianStep b c q p).2)
      (ν.prod (iidMatrixLaw (r + 1) (s + 1) v)) := by
  have h := adaptiveGaussianStep_preserving ν b c q hq v
  rw [ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map h.measurable.fst.aemeasurable
    h.measurable.snd.aemeasurable]
  change (ν.prod (iidMatrixLaw (r + 1) (s + 1) v)).map (adaptiveGaussianStep b c q) = _
  rw [h.map_eq, adaptiveGaussianStep_residual_law ν b c q hq]
  congr 1
  symm
  calc
    _ = ((ν.prod (iidMatrixLaw (r + 1) (s + 1) v)).map
        (adaptiveGaussianStep b c q)).map Prod.fst :=
      (Measure.map_map measurable_fst h.measurable).symm
    _ = _ := by rw [h.map_eq]; simp

end
end LowRank
