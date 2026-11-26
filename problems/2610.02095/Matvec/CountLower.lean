import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-! Lower-tail transfer from many correlated diagonal events to their sum.
No independence assumption is made or needed. -/
namespace Matvec
open MeasureTheory Set
open scoped BigOperators

theorem probability_lower_of_bounded_mean {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ)
    (hf : Measurable f) (B p : ℝ) (hB : 0 < B) (hp : 0 ≤ p)
    (hf0 : ∀ ω, 0 ≤ f ω) (hfB : ∀ ω, f ω ≤ B)
    (hmean : B * p ≤ ∫ ω, f ω ∂μ) :
    p / 2 ≤ μ.real {ω | B * p / 2 ≤ f ω} := by
  let E := {ω | B * p / 2 ≤ f ω}
  have hE : MeasurableSet E := measurableSet_le measurable_const hf
  have hi : Integrable f μ := (integrable_const B).mono' hf.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hf0 ω)] using hfB ω)
  have hEi : Integrable (E.indicator (fun _ : Ω => B)) μ :=
    (integrable_const B).indicator hE
  have hpoint (ω : Ω) : f ω ≤ B * p / 2 + E.indicator (fun _ => B) ω := by
    by_cases he : ω ∈ E
    · rw [Set.indicator_of_mem he]
      have hnonneg : 0 ≤ B * p / 2 := by positivity
      linarith [hfB ω]
    · rw [Set.indicator_of_not_mem he, add_zero]
      exact le_of_lt (lt_of_not_ge he)
  have h := integral_mono hi ((integrable_const (B * p / 2)).add hEi) hpoint
  simp only [Pi.add_apply] at h
  rw [integral_add (integrable_const _) hEi, integral_const,
    measureReal_univ_eq_one, smul_eq_mul, one_mul, integral_indicator_const _ hE,
    smul_eq_mul] at h
  nlinarith

theorem sum_lower_probability_of_marginals {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] [Nonempty ι] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ι → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (hX0 : ∀ i ω, 0 ≤ X i ω) (T p : ℝ) (hT : 0 ≤ T) (hp : 0 ≤ p)
    (htail : ∀ i, p ≤ μ.real {ω | T ≤ X i ω}) :
    p / 2 ≤ μ.real {ω | (Fintype.card ι : ℝ) * p * T / 2 ≤ ∑ i, X i ω} := by
  classical
  let A : ι → Set Ω := fun i => {ω | T ≤ X i ω}
  let f : Ω → ℝ := fun ω => ∑ i, (A i).indicator (fun _ => (1 : ℝ)) ω
  have hA (i : ι) : MeasurableSet (A i) := measurableSet_le measurable_const (hX i)
  have hfi (i : ι) : Integrable ((A i).indicator (fun _ : Ω => (1 : ℝ))) μ :=
    (integrable_const 1).indicator (hA i)
  have hf : Measurable f := Finset.measurable_sum _ (fun i _ =>
    measurable_const.indicator (hA i))
  have hf0 : ∀ ω, 0 ≤ f ω := by
    intro ω
    apply Finset.sum_nonneg
    intro i _
    exact Set.indicator_nonneg (fun _ _ => by norm_num) _
  have hfB : ∀ ω, f ω ≤ Fintype.card ι := by
    intro ω
    calc
      f ω ≤ ∑ _ : ι, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        by_cases he : ω ∈ A i <;> simp [he]
      _ = _ := by simp
  have hmean : (Fintype.card ι : ℝ) * p ≤ ∫ ω, f ω ∂μ := by
    unfold f
    rw [integral_finset_sum _ (fun i _ => hfi i)]
    simp_rw [integral_indicator_const _ (hA _), smul_eq_mul, mul_one]
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using
      Finset.sum_le_sum (s := Finset.univ) (fun i _ => htail i)
  have hB : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hprob := probability_lower_of_bounded_mean μ f hf _ p hB hp hf0 hfB hmean
  refine hprob.trans (measureReal_mono ?_)
  intro ω hω
  have hsum : T * f ω ≤ ∑ i, X i ω := by
    unfold f
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    by_cases he : ω ∈ A i
    · simpa only [Set.indicator_of_mem he, mul_one] using he
    · simpa only [Set.indicator_of_not_mem he, mul_zero] using hX0 i ω
  have h := mul_le_mul_of_nonneg_left hω hT
  dsimp only [Set.mem_setOf_eq]
  nlinarith

end Matvec
