import Matvec.Amplification

/-! Independent repetition for scalar estimates with one-sided reliability. -/

namespace Matvec

open MeasureTheory
noncomputable section

variable {Seed : Type*} [MeasurableSpace Seed]

def repeatedMaximum (estimate : Seed → ℝ) (S : ℕ) (seeds : Fin (S + 1) → Seed) : ℝ :=
  bestCandidate (fun x : ℝ => -x) S (fun i => estimate (seeds i))

theorem measurable_repeatedMaximum (estimate : Seed → ℝ) (hm : Measurable estimate) (S : ℕ) :
    Measurable (repeatedMaximum estimate S) :=
  (measurable_bestCandidate (fun x : ℝ => -x) measurable_neg S).comp
    (measurable_pi_lambda _ fun i => hm.comp (measurable_pi_apply i))

theorem repeatedMaximum_lower_failure (μ : Measure Seed) [IsProbabilityMeasure μ]
    (estimate : Seed → ℝ) (S : ℕ) (a : ℝ) :
    (Measure.pi (fun _ : Fin (S + 1) => μ)).real
      {seeds | repeatedMaximum estimate S seeds < a} =
      (μ.real {seed | estimate seed < a}) ^ (S + 1) := by
  have hevent : {seeds : Fin (S + 1) → Seed | repeatedMaximum estimate S seeds < a} =
      {seeds | ∀ i, seeds i ∈ {seed | estimate seed < a}} := by
    ext seeds
    have h := bestCandidate_failure_iff (fun x : ℝ => -x) S
      (fun i => estimate (seeds i)) (-a)
    simpa only [neg_lt_neg_iff] using h
  rw [hevent]
  exact independent_all_failure μ _ (S + 1)

theorem pi_coordinate_probability (μ : Measure Seed) [IsProbabilityMeasure μ]
    (S : ℕ) (i : Fin S) (event : Set Seed) :
    (Measure.pi (fun _ : Fin S => μ)).real {seeds | seeds i ∈ event} = μ.real event := by
  have heq : {seeds : Fin S → Seed | seeds i ∈ event} =
      Set.pi Set.univ (fun j => if j = i then event else Set.univ) := by
    ext seeds
    simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · intro h j
      by_cases hj : j = i
      · simpa [hj] using h
      · simp [hj]
    · intro h
      simpa using h i
  rw [heq]
  simp only [Measure.real, Measure.pi_pi]
  simp [apply_ite]

theorem repeatedMaximum_upper_failure (μ : Measure Seed) [IsProbabilityMeasure μ]
    (estimate : Seed → ℝ) (S : ℕ) (b : ℝ) :
    (Measure.pi (fun _ : Fin (S + 1) => μ)).real
      {seeds | b < repeatedMaximum estimate S seeds} ≤
      (S + 1 : ℝ) * μ.real {seed | b < estimate seed} := by
  have hsub : {seeds : Fin (S + 1) → Seed | b < repeatedMaximum estimate S seeds} ⊆
      ⋃ i : Fin (S + 1), {seeds | b < estimate (seeds i)} := by
    intro seeds hs
    obtain ⟨i, hi⟩ := bestCandidate_mem (fun x : ℝ => -x) S (fun i => estimate (seeds i))
    apply Set.mem_iUnion.mpr
    refine ⟨i, ?_⟩
    exact (show b < bestCandidate (fun x : ℝ => -x) S (fun i => estimate (seeds i)) from hs).trans_le hi.le
  calc
    _ ≤ (Measure.pi (fun _ : Fin (S + 1) => μ)).real
        (⋃ i : Fin (S + 1), {seeds | b < estimate (seeds i)}) := measureReal_mono hsub
    _ ≤ ∑ i : Fin (S + 1), (Measure.pi (fun _ : Fin (S + 1) => μ)).real
        {seeds | b < estimate (seeds i)} := measureReal_iUnion_fintype_le _
    _ = _ := by
      have he (i : Fin (S + 1)) := pi_coordinate_probability μ (S + 1) i {seed | b < estimate seed}
      simp only [Set.mem_setOf_eq] at he
      simp only [he, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_add, Nat.cast_one]

/-- A repeated maximum boosts the lower guarantee and loses at most S+1
times the upper failure probability. All repeats use an actual product law. -/
theorem repeatedMaximum_success (μ : Measure Seed) [IsProbabilityMeasure μ]
    (estimate : Seed → ℝ) (hm : Measurable estimate) (S : ℕ) (a b p δ : ℝ)
    (hsuccess : p ≤ μ.real {seed | a ≤ estimate seed ∧ estimate seed ≤ b})
    (hupper : μ.real {seed | b < estimate seed} ≤ δ) :
    1 - (1 - p) ^ (S + 1) - (S + 1 : ℝ) * δ ≤
      (Measure.pi (fun _ : Fin (S + 1) => μ)).real
        {seeds | a ≤ repeatedMaximum estimate S seeds ∧ repeatedMaximum estimate S seeds ≤ b} := by
  have hlow : μ.real {seed | estimate seed < a} ≤ 1 - p := by
    have hcomp : {seed | estimate seed < a} = {seed | a ≤ estimate seed}ᶜ := by ext seed; simp
    rw [hcomp, measureReal_compl (measurableSet_le measurable_const hm), measureReal_univ_eq_one]
    have hs : p ≤ μ.real {seed | a ≤ estimate seed} :=
      hsuccess.trans (measureReal_mono (fun _ h => h.1))
    linarith
  have hlower := repeatedMaximum_lower_failure μ estimate S a
  have hlowerbound : (Measure.pi (fun _ : Fin (S + 1) => μ)).real
      {seeds | repeatedMaximum estimate S seeds < a} ≤ (1 - p) ^ (S + 1) := by
    rw [hlower]
    exact pow_le_pow_left₀ measureReal_nonneg hlow _
  have hupperbound := (repeatedMaximum_upper_failure μ estimate S b).trans
    (mul_le_mul_of_nonneg_left hupper (by positivity : (0 : ℝ) ≤ S + 1))
  let good := {seeds : Fin (S + 1) → Seed |
    a ≤ repeatedMaximum estimate S seeds ∧ repeatedMaximum estimate S seeds ≤ b}
  have hmeas : MeasurableSet good :=
    (measurableSet_le measurable_const (measurable_repeatedMaximum estimate hm S)).inter
      (measurableSet_le (measurable_repeatedMaximum estimate hm S) measurable_const)
  have heq : goodᶜ = {seeds | repeatedMaximum estimate S seeds < a} ∪
      {seeds | b < repeatedMaximum estimate S seeds} := by
    ext seeds
    simp only [good, Set.mem_compl_iff, Set.mem_setOf_eq, not_and_or, not_le, Set.mem_union]
  have hu := measureReal_union_le (μ := Measure.pi (fun _ : Fin (S + 1) => μ))
    {seeds | repeatedMaximum estimate S seeds < a} {seeds | b < repeatedMaximum estimate S seeds}
  rw [← heq, measureReal_compl hmeas, measureReal_univ_eq_one] at hu
  change _ ≤ (Measure.pi (fun _ : Fin (S + 1) => μ)).real good
  linarith

end
end Matvec
