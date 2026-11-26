import FullJet.InitializedRows
import Mathlib.Logic.Equiv.Prod

open scoped BigOperators

namespace FullJet

theorem uniform_map_equiv {α β : Type*} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (e : α ≃ β) : (PMF.uniformOfFintype α).map e = PMF.uniformOfFintype β := by
  classical
  unfold PMF.uniformOfFintype
  rw [uniformOfFinset_map_injOn _ _ e e.injective.injOn]
  congr 1
  exact Finset.image_univ_of_surjective e.surjective

theorem uniform_pair_event_probability {α β : Type*} [Fintype α] [Fintype β]
    [Nonempty α] [Nonempty β] (A : β → Set α) :
    ((PMF.uniformOfFintype (α × β)).toOuterMeasure {z | z.1 ∈ A z.2}).toReal =
      ∑ b, ((PMF.uniformOfFintype β) b).toReal *
        ((PMF.uniformOfFintype α).toOuterMeasure (A b)).toReal := by
  classical
  rw [pmf_event_toReal, Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  rw [pmf_event_toReal, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  simp only [Set.mem_setOf_eq, uniform_product_mass]
  by_cases h : a ∈ A b <;> simp [h, mul_comm]

/-- A fresh coordinate is uniform even when all the other coordinates are
made available as side information. This is proved for the actual product law. -/
theorem uniform_coordinate_event_probability {ι α : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype α] [Nonempty α] (j : ι) (A : ({l : ι // l ≠ j} → α) → Set α) :
    ((PMF.uniformOfFintype (ι → α)).toOuterMeasure
      {x | x j ∈ A (fun l => x l)}).toReal =
      ∑ y, ((PMF.uniformOfFintype ({l : ι // l ≠ j} → α)) y).toReal *
        ((PMF.uniformOfFintype α).toOuterMeasure (A y)).toReal := by
  let e := Equiv.funSplitAt j α
  change ((PMF.uniformOfFintype (ι → α)).toOuterMeasure
    (e ⁻¹' {z | z.1 ∈ A z.2})).toReal = _
  rw [← PMF.toOuterMeasure_map_apply, uniform_map_equiv e]
  exact uniform_pair_event_probability A

theorem uniform_coordinate_event_le {ι α : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype α] [Nonempty α] (j : ι) (A : ({l : ι // l ≠ j} → α) → Set α)
    (δ : ℝ) (hA : ∀ y, ((PMF.uniformOfFintype α).toOuterMeasure (A y)).toReal ≤ δ) :
    ((PMF.uniformOfFintype (ι → α)).toOuterMeasure {x | x j ∈ A (fun l => x l)}).toReal ≤ δ := by
  rw [uniform_coordinate_event_probability]
  calc
    _ ≤ ∑ y, ((PMF.uniformOfFintype ({l : ι // l ≠ j} → α)) y).toReal * δ :=
      Finset.sum_le_sum (fun y _ => mul_le_mul_of_nonneg_left (hA y) ENNReal.toReal_nonneg)
    _ = δ := by rw [← Finset.sum_mul, pmf_toReal_sum, one_mul]

noncomputable def fixedChainLaw (n D k T : ℕ) (hk : k ≤ n) :
    PMF (Fin T → FixedTableSample n D k) := by
  letI := fixedColumn_nonempty hk
  exact PMF.uniformOfFintype _

abbrev OtherStageSamples (n D k T : ℕ) (j : Fin T) :=
  {l : Fin T // l ≠ j} → FixedTableSample n D k

def stageInitializedAlignment {n D k T : ℕ} {κ : Type*} (j : Fin T)
    (initialIndex : OtherStageSamples n D k T j → Fin n)
    (ask : OtherStageSamples n D k T j → (Fin D → Bool) → List (Fin D → Bool) → Fin n)
    (q : ℕ) (w : OtherStageSamples n D k T j → (Fin D → Bool) →
      (Fin q → Fin D → Bool) → κ → EuclideanSpace ℝ (Fin D)) (a : ℝ) :
    Set (Fin T → FixedTableSample n D k) :=
  {x | x j ∈ initializedAlignmentEvent (initialIndex (fun l => x l))
    (ask (fun l => x l)) q (w (fun l => x l)) a}

/-- In the actual independent chain distribution, the one-stage bound
survives arbitrary side information consisting of all other stage samples. -/
theorem stage_initialized_alignment_quarter {n D k T : ℕ} {κ : Type*} [Fintype κ]
    (hn : 0 < n) (hD : 0 < D) (hk : k ≤ n)
    (m : ℝ) (hm : 0 ≤ m) (hbalance : 2 * (k : ℝ) = n + m)
    (j : Fin T) (initialIndex : OtherStageSamples n D k T j → Fin n)
    (ask : OtherStageSamples n D k T j → (Fin D → Bool) → List (Fin D → Bool) → Fin n)
    (q : ℕ) (hbudget : 8 * m + 9 * (q + 1 : ℕ) ≤ n)
    (w : OtherStageSamples n D k T j → (Fin D → Bool) →
      (Fin q → Fin D → Bool) → κ → EuclideanSpace ℝ (Fin D))
    (hw : ∀ y b v l, ‖w y b v l‖ ≤ 1) (a : ℝ) (ha : 0 < a)
    (hqueries : (q + 1 : ℕ) * (m / n) ^ 2 ≤ a ^ 2 / 1024)
    (hdim : 32 * Real.log 2 ≤ a ^ 2 * D)
    (hfamily : (Fintype.card κ : ℝ) ≤ Real.exp (a ^ 2 * D / 4)) :
    ((fixedChainLaw n D k T hk).toOuterMeasure
      (stageInitializedAlignment j initialIndex ask q w a)).toReal ≤ 1 / 4 := by
  letI := fixedColumn_nonempty hk
  apply uniform_coordinate_event_le j
    (fun y : OtherStageSamples n D k T j => initializedAlignmentEvent (initialIndex y) (ask y) q (w y) a)
  intro y
  exact initialized_row_alignment_quarter hn hD hk m hm hbalance (initialIndex y) (ask y) q hbudget
    (w y) (hw y) a ha hqueries hdim hfamily

end FullJet
