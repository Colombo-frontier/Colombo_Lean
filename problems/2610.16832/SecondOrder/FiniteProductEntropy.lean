import SecondOrder.FiniteRelativeEntropy
import Mathlib.MeasureTheory.Constructions.Pi

open MeasureTheory InformationTheory
open scoped BigOperators Classical ENNReal

namespace SecondOrder
noncomputable section

variable {ι α : Type*} [Fintype ι] [Fintype α]

/-- The independent product law, with its probability mass verified directly. -/
def finitePiPMF (p : ι → PMF α) : PMF (ι → α) :=
  PMF.ofFintype (fun w => ∏ i, p i (w i)) (by
    rw [← Fintype.prod_sum]
    simp only [← tsum_fintype, PMF.tsum_coe, Finset.prod_const_one])

@[simp] theorem finitePiPMF_apply (p : ι → PMF α) (w : ι → α) :
    finitePiPMF p w = ∏ i, p i (w i) := rfl

theorem finitePiPMF_toReal (p : ι → PMF α) (w : ι → α) :
    (finitePiPMF p w).toReal = ∏ i, (p i (w i)).toReal := by
  simp [finitePiPMF_apply, ENNReal.toReal_prod]

theorem finitePiPMF_ne_zero (p : ι → PMF α) (hp : ∀ i a, p i a ≠ 0) (w : ι → α) :
    finitePiPMF p w ≠ 0 := by
  rw [finitePiPMF_apply]
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => hp i (w i))

/-- Summing out every other coordinate gives the exact marginal expectation. -/
theorem finitePiPMF_coordinate_mean (p : ι → PMF α) (i : ι) (X : α → ℝ) :
    pmfMean (finitePiPMF p) (fun w => X (w i)) = pmfMean (p i) X := by
  let g : ι → α → ℝ := fun j a => (p j a).toReal * (if j = i then X a else 1)
  have he (w : ι → α) : (∏ j, (p j (w j)).toReal)*X (w i) = ∏ j, g j (w j) := by
    dsimp [g]
    rw [Finset.prod_mul_distrib]
    simp
  have hs (j : ι) : (∑ a, g j a) = if j = i then pmfMean (p i) X else 1 := by
    by_cases h : j = i
    · subst j; simp [g, pmfMean, smul_eq_mul]
    · simp [g, h, pmf_toReal_sum]
  simp only [pmfMean, smul_eq_mul, finitePiPMF_toReal]
  rw [show (∑ w, (∏ j, (p j (w j)).toReal)*X (w i)) = ∑ w, ∏ j, g j (w j)
    from Finset.sum_congr rfl (fun w _ => he w), ← Fintype.prod_sum]
  simp only [hs]
  simp [pmfMean, smul_eq_mul]

theorem pmfKL_finitePi (p q : ι → PMF α)
    (hp : ∀ i a, p i a ≠ 0) (hq : ∀ i a, q i a ≠ 0) :
    pmfKL (finitePiPMF p) (finitePiPMF q) = ∑ i, pmfKL (p i) (q i) := by
  have hlog (w : ι → α) :
      Real.log ((finitePiPMF p w).toReal/(finitePiPMF q w).toReal) =
        ∑ i, Real.log ((p i (w i)).toReal/(q i (w i)).toReal) := by
    rw [finitePiPMF_toReal, finitePiPMF_toReal, ← Finset.prod_div_distrib]
    apply Real.log_prod
    intro i _
    exact div_ne_zero
      ((ENNReal.toReal_pos (hp i (w i)) ((p i).apply_ne_top _)).ne')
      ((ENNReal.toReal_pos (hq i (w i)) ((q i).apply_ne_top _)).ne')
  change pmfMean (finitePiPMF p) (fun w =>
    Real.log ((finitePiPMF p w).toReal/(finitePiPMF q w).toReal)) = _
  simp_rw [hlog]
  rw [pmfMean_finset_sum]
  exact Finset.sum_congr rfl (fun i _ => finitePiPMF_coordinate_mean p i
    (fun a => Real.log ((p i a).toReal/(q i a).toReal)))

theorem klDiv_finitePi [MeasurableSpace α] [MeasurableSingletonClass α]
    (p q : ι → PMF α) (hp : ∀ i a, p i a ≠ 0) (hq : ∀ i a, q i a ≠ 0) :
    klDiv (finitePiPMF p).toMeasure (finitePiPMF q).toMeasure =
      ENNReal.ofReal (∑ i, pmfKL (p i) (q i)) := by
  rw [klDiv_pmf _ _ (finitePiPMF_ne_zero q hq), pmfKL_finitePi p q hp hq]

theorem finitePiPMF_toMeasure [MeasurableSpace α] [MeasurableSingletonClass α]
    (p : ι → PMF α) :
    (finitePiPMF p).toMeasure = Measure.pi (fun i => (p i).toMeasure) := by
  apply Measure.ext_of_singleton
  intro w
  have hs : ({w} : Set (ι → α)) = Set.univ.pi (fun i => {w i}) := by
    ext z
    simp only [Set.mem_singleton_iff, Set.mem_pi, Set.mem_univ, forall_true_left]
    exact funext_iff
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), finitePiPMF_apply, hs,
    Measure.pi_pi]
  exact Finset.prod_congr rfl (fun i _ =>
    (PMF.toMeasure_apply_singleton (p i) (w i) (measurableSet_singleton _)).symm)

end
end SecondOrder
