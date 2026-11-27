import Nonsmooth.SoftInequalityStep

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {α ι : Type} [Fintype ι]

def softInequalityWeight (f : ι → α → ℝ) (n : ℕ) (x : α) : ℝ :=
  ∏ i, softInequalityStep n (f i x)

def softInequalityRegion (f : ι → α → ℝ) : Set α := {x | ∀ i, f i x ≤ 0}

theorem softInequalityWeight_pos (f : ι → α → ℝ) (n : ℕ) (x : α) :
    0 < softInequalityWeight f n x := Finset.prod_pos (fun i _ => softInequalityStep_pos n (f i x))

theorem softInequalityWeight_le_one (f : ι → α → ℝ) (n : ℕ) (x : α) :
    softInequalityWeight f n x ≤ 1 := Finset.prod_le_one
      (fun i _ => (softInequalityStep_pos n (f i x)).le) (fun i _ => softInequalityStep_le_one n (f i x))

theorem softInequalityWeight_tendsto (f : ι → α → ℝ) (x : α) (hx : ∀ i, f i x ≠ 0) :
    Tendsto (fun n => softInequalityWeight f n x) atTop
      (𝓝 ((softInequalityRegion f).indicator (fun _ => (1 : ℝ)) x)) := by
  classical
  let b : ι → ℝ := fun i => if f i x ≤ 0 then 1 else 0
  have hi (i : ι) : Tendsto (fun n => softInequalityStep n (f i x)) atTop (𝓝 (b i)) := by
    by_cases h : f i x ≤ 0
    · have hn : f i x < 0 := lt_of_le_of_ne h (hx i)
      simpa only [b, if_pos h] using softInequalityStep_tendsto_of_neg hn
    · simpa only [b, if_neg h] using softInequalityStep_tendsto_of_pos (lt_of_not_ge h)
  have hp := tendsto_finset_prod Finset.univ (fun i _ => hi i)
  have he : (∏ i, b i) = (softInequalityRegion f).indicator (fun _ => (1 : ℝ)) x := by
    by_cases h : x ∈ softInequalityRegion f
    · rw [Set.indicator_of_mem h]
      exact Finset.prod_eq_one (fun i _ => if_pos (h i))
    · rw [Set.indicator_of_notMem h]
      have hn : ¬ ∀ i, f i x ≤ 0 := h
      obtain ⟨i, hi⟩ := not_forall.mp hn
      exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)
  simpa only [softInequalityWeight, he] using hp

theorem softInequalityWeight_contDiff {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ι → E → ℝ) (hf : ∀ i, ContDiff ℝ ⊤ (f i)) (n : ℕ) :
    ContDiff ℝ ⊤ (softInequalityWeight f n) := by
  exact contDiff_prod (fun i _ => (softInequalityStep_contDiff n).comp (hf i))

variable [MeasurableSpace α]

theorem softInequalityWeight_measurable (f : ι → α → ℝ) (hf : ∀ i, Measurable (f i)) (n : ℕ) :
    Measurable (softInequalityWeight f n) := by
  have hi (i : ι) : Measurable (fun x => softInequalityStep n (f i x)) :=
    (softInequalityStep_contDiff n).continuous.measurable.comp (hf i)
  unfold softInequalityWeight
  fun_prop

theorem softInequalityRegion_measurable (f : ι → α → ℝ) (hf : ∀ i, Measurable (f i)) :
    MeasurableSet (softInequalityRegion f) := by
  have he : softInequalityRegion f = ⋂ i, {x | f i x ≤ 0} := by
    ext x
    simp only [softInequalityRegion, mem_setOf_eq, mem_iInter]
  rw [he]
  exact MeasurableSet.iInter (fun i => measurableSet_le (hf i) measurable_const)

/-- The explicit smooth weights converge to the closed inequality region
outside its null boundary hyper-surfaces. -/
theorem softInequalityWeight_ae_tendsto (μ : Measure α) (f : ι → α → ℝ)
    (hzero : ∀ i, μ {x | f i x = 0} = 0) :
    ∀ᵐ x ∂μ, Tendsto (fun n => softInequalityWeight f n x) atTop
      (𝓝 ((softInequalityRegion f).indicator (fun _ => (1 : ℝ)) x)) := by
  have hi (i : ι) : ∀ᵐ x ∂μ, f i x ≠ 0 := by
    simpa only [ae_iff, not_not] using hzero i
  filter_upwards [ae_all_iff.mpr hi] with x hx
  exact softInequalityWeight_tendsto f x hx

end
end Nonsmooth
