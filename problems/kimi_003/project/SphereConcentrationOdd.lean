import SphereConcentrationLevy

/-!
Oddness of an actual scalar function and rotational invariance of the concrete
sphere law imply that zero is a median. No median premise is introduced for
odd secants.
-/

open Set MeasureTheory ProbabilityTheory
open Task006.HaarRebalancing
open scoped ENNReal NNReal

namespace Task006.SphereConcentration
noncomputable section

/-- Odd functions of a uniform sphere vector have a symmetric real law. -/
theorem odd_uniform_scalar_map_neg_eq {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {v : Ω → EuclideanSpace ℝ (Fin d)} (hv : UniformSphereLaw v μ)
    {a : EuclideanSpace ℝ (Fin d) → ℝ} (ha : Measurable a)
    (hodd : ∀ x, a (-x) = -a x) :
    Measure.map (fun ω => -a (v ω)) μ = Measure.map (fun ω => a (v ω)) μ := by
  have hfun : (fun ω => -a (v ω)) = a ∘ (fun ω => -v ω) := by
    funext ω
    exact (hodd (v ω)).symm
  rw [hfun]
  calc
    Measure.map (a ∘ (fun ω => -v ω)) μ =
        Measure.map a (Measure.map (fun ω => -v ω) μ) := by
      have hvneg : AEMeasurable (fun ω => -v ω) μ := hv.measurable.neg
      exact (AEMeasurable.map_map_of_aemeasurable ha.aemeasurable hvneg).symm
    _ = Measure.map a (Measure.map v μ) := by
      rw [show Measure.map (fun ω => -v ω) μ = Measure.map v μ from
        hv.rotationInvariant (LinearIsometryEquiv.neg ℝ)]
    _ = Measure.map (fun ω => a (v ω)) μ :=
      AEMeasurable.map_map_of_aemeasurable ha.aemeasurable hv.measurable

/-- The genuine median-zero property follows from symmetry and total mass. -/
theorem odd_uniform_has_zero_median {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {v : Ω → EuclideanSpace ℝ (Fin d)} (hv : UniformSphereLaw v μ)
    {a : EuclideanSpace ℝ (Fin d) → ℝ} (ha : Measurable a)
    (hodd : ∀ x, a (-x) = -a x) :
    (1 / 2 : ℝ) ≤ μ.real {ω | a (v ω) ≤ 0} ∧
      (1 / 2 : ℝ) ≤ μ.real {ω | 0 ≤ a (v ω)} := by
  have hX : AEMeasurable (fun ω => a (v ω)) μ :=
    ha.aemeasurable.comp_aemeasurable hv.measurable
  have hsym : μ.real {ω | 0 ≤ a (v ω)} = μ.real {ω | a (v ω) ≤ 0} := by
    have hXneg : AEMeasurable (fun ω => -a (v ω)) μ := hX.neg
    have h := real_event_eq_of_map_eq hXneg hX
      (odd_uniform_scalar_map_neg_eq hv ha hodd) (s := Iic 0) measurableSet_Iic
    change μ.real {ω | -a (v ω) ≤ 0} = μ.real {ω | a (v ω) ≤ 0} at h
    simpa only [neg_nonpos] using h
  have hcover : {ω | a (v ω) ≤ 0} ∪ {ω | 0 ≤ a (v ω)} = univ := by
    ext ω
    simp only [mem_union, mem_setOf_eq, mem_univ, iff_true]
    exact le_total _ _
  have hsum := measureReal_union_le (μ := μ) {ω | a (v ω) ≤ 0} {ω | 0 ≤ a (v ω)}
  rw [hcover, probReal_univ] at hsum
  constructor <;> linarith

end
end Task006.SphereConcentration
