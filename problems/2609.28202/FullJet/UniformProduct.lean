import FullJet.UniformConditioning
import Mathlib.Data.Fintype.BigOperators

open scoped BigOperators ENNReal

namespace FullJet

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq α]

/-- The uniform law on a finite Cartesian product. -/
noncomputable def uniformPi (s : ι → Finset α) (hs : ∀ j, (s j).Nonempty) : PMF (ι → α) :=
  PMF.uniformOfFinset (Fintype.piFinset s) (Fintype.piFinset_nonempty.mpr hs)

theorem piFinset_filter_rect (s : ι → Finset α) (A : ι → Set α)
    [∀ j, DecidablePred (· ∈ A j)] :
    (Fintype.piFinset s).filter (fun f => ∀ j, f j ∈ A j) =
      Fintype.piFinset (fun j => (s j).filter (· ∈ A j)) := by
  ext f
  simp only [Finset.mem_filter, Fintype.mem_piFinset, forall_and]

/-- Rectangle probabilities factor, proving independence of the coordinates
without assuming an independence hypothesis. -/
theorem uniformPi_rect_probability (s : ι → Finset α) (hs : ∀ j, (s j).Nonempty)
    (A : ι → Set α) :
    ((uniformPi s hs).toOuterMeasure {f | ∀ j, f j ∈ A j}).toReal =
      ∏ j, ((PMF.uniformOfFinset (s j) (hs j)).toOuterMeasure (A j)).toReal := by
  classical
  unfold uniformPi
  simp only [PMF.toOuterMeasure_uniformOfFinset_apply, ENNReal.toReal_div,
    ENNReal.toReal_natCast]
  have hfilter : (Fintype.piFinset s).filter (fun f => f ∈ {f | ∀ j, f j ∈ A j}) =
      Fintype.piFinset (fun j => (s j).filter (· ∈ A j)) := by
    ext f
    simp only [Finset.mem_filter, Set.mem_setOf_eq, Fintype.mem_piFinset, forall_and]
  trans ((Fintype.piFinset (fun j => (s j).filter (· ∈ A j))).card : ℝ) /
    (Fintype.piFinset s).card
  · congr 3
    convert hfilter using 1
    ext f
    simp only [Finset.mem_filter]
  · rw [Fintype.card_piFinset, Fintype.card_piFinset]
    simp only [Nat.cast_prod, Finset.prod_div_distrib]

theorem uniformPi_coordinate_probability (s : ι → Finset α) (hs : ∀ j, (s j).Nonempty)
    (j : ι) (B : Set α) :
    ((uniformPi s hs).toOuterMeasure {f | f j ∈ B}).toReal =
      ((PMF.uniformOfFinset (s j) (hs j)).toOuterMeasure B).toReal := by
  classical
  have hset : {f : ι → α | f j ∈ B} = {f | ∀ l, f l ∈ if l = j then B else Set.univ} := by
    ext f
    simp only [Set.mem_setOf_eq]
    constructor
    · intro hf l
      by_cases h : l = j <;> simp [h, hf]
    · intro hf
      simpa using hf j
  rw [hset, uniformPi_rect_probability]
  calc
    _ = ∏ l, if l = j then ((PMF.uniformOfFinset (s l) (hs l)).toOuterMeasure B).toReal else 1 := by
      apply Finset.prod_congr rfl
      intro l hl
      by_cases h : l = j
      · simp [h]
      · have hu : (PMF.uniformOfFinset (s l) (hs l)).toOuterMeasure Set.univ = 1 :=
          (PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr (Set.subset_univ _)
        simp [h, hu]
    _ = _ := Fintype.prod_ite_eq' _ _

/-- Conditioning a Cartesian uniform law on coordinatewise restrictions
leaves a Cartesian uniform law on the restricted factors. -/
theorem uniformPi_condition_rect (s : ι → Finset α) (hs : ∀ j, (s j).Nonempty)
    (A : ι → Set α) [∀ j, DecidablePred (· ∈ A j)]
    (hA : ∀ j, ((s j).filter (· ∈ A j)).Nonempty)
    (hpos : ∃ f ∈ {f | ∀ j, f j ∈ A j}, f ∈ (uniformPi s hs).support) :
    (uniformPi s hs).filter {f | ∀ j, f j ∈ A j} hpos =
      uniformPi (fun j => (s j).filter (· ∈ A j)) hA := by
  have hrect : ((Fintype.piFinset s).filter (fun f => ∀ j, f j ∈ A j)).Nonempty := by
    rw [piFinset_filter_rect]
    exact Fintype.piFinset_nonempty.mpr hA
  unfold uniformPi
  rw [uniformOfFinset_filter (Fintype.piFinset s) (Fintype.piFinset_nonempty.mpr hs)
    {f | ∀ j, f j ∈ A j} hrect hpos]
  congr 1
  convert piFinset_filter_rect s A using 1

theorem uniformPi_rect_feasible (s : ι → Finset α) (hs : ∀ j, (s j).Nonempty)
    (A : ι → Set α) [∀ j, DecidablePred (· ∈ A j)]
    (hpos : ∃ f ∈ {f | ∀ j, f j ∈ A j}, f ∈ (uniformPi s hs).support) :
    ∀ j, ((s j).filter (· ∈ A j)).Nonempty := by
  obtain ⟨f, hfA, hfs⟩ := hpos
  have hmem : f ∈ Fintype.piFinset s := by
    simpa only [uniformPi, PMF.mem_support_uniformOfFinset_iff] using hfs
  intro j
  exact ⟨f j, Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mp hmem j, hfA j⟩⟩

/-- The actual conditional joint probabilities are products of the individual
conditional probabilities. No independence is introduced as a premise. -/
theorem uniformPi_conditional_rect_probability (s : ι → Finset α) (hs : ∀ j, (s j).Nonempty)
    (A B : ι → Set α) [∀ j, DecidablePred (· ∈ A j)]
    (hpos : ∃ f ∈ {f | ∀ j, f j ∈ A j}, f ∈ (uniformPi s hs).support) :
    (((uniformPi s hs).filter {f | ∀ j, f j ∈ A j} hpos).toOuterMeasure
      {f | ∀ j, f j ∈ B j}).toReal =
      ∏ j, ((PMF.uniformOfFinset ((s j).filter (· ∈ A j))
        (uniformPi_rect_feasible s hs A hpos j)).toOuterMeasure (B j)).toReal := by
  rw [uniformPi_condition_rect s hs A (uniformPi_rect_feasible s hs A hpos) hpos]
  exact uniformPi_rect_probability _ _ _

end FullJet
