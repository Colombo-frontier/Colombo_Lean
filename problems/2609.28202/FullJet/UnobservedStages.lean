import FullJet.StageEventCounting

open scoped BigOperators InnerProductSpace

namespace FullJet

theorem uniform_first_event_probability {α β : Type*} [Fintype α] [Fintype β]
    [Nonempty α] [Nonempty β] (A : Set α) :
    ((PMF.uniformOfFintype (α × β)).toOuterMeasure {z | z.1 ∈ A}).toReal =
      ((PMF.uniformOfFintype α).toOuterMeasure A).toReal := by
  rw [uniform_pair_event_probability (fun _ : β => A), ← Finset.sum_mul, pmf_toReal_sum, one_mul]

theorem fixedTable_unobserved_alignment_tail {n D k : ℕ} {κ : Type*} [Fintype κ]
    (hk : k ≤ n) (hD : 0 < D) (w : κ → EuclideanSpace ℝ (Fin D))
    (hw : ∀ l, ‖w l‖ ≤ 1) (a : ℝ) (ha : 0 ≤ a) :
    ((fixedTableLaw n D k hk).toOuterMeasure
      {ω | ∃ l, a ≤ ⟪sampledDirection ω, w l⟫_ℝ}).toReal ≤
      Fintype.card κ * Real.exp (-(a ^ 2 * D / 2)) := by
  classical
  letI := fixedColumn_nonempty hk
  let A : Set (Fin D → Bool) := {theta | ∃ l,
    a ≤ ⟪normalizedVector (fun j => rareSign (theta j)), w l⟫_ℝ}
  change ((PMF.uniformOfFintype ((Fin D → Bool) × (Fin D → FixedColumn n k))).toOuterMeasure
    {z | z.1 ∈ A}).toReal ≤ _
  rw [uniform_first_event_probability, pmf_event_toReal]
  simp_rw [uniform_cube_mass]
  simpa only [Finset.sum_filter, Set.mem_setOf_eq] using euclidean_any_alignment_tail D w a ha hw hD

def stageUnobservedAlignment {n D k T : ℕ} {κ : Type*} (j : Fin T)
    (w : OtherStageSamples n D k T j → κ → EuclideanSpace ℝ (Fin D)) (a : ℝ) :
    Set (Fin T → FixedTableSample n D k) :=
  {x | ∃ l, a ≤ ⟪sampledDirection (x j), w (fun t => x t) l⟫_ℝ}

/-- As long as candidate directions omit the target stage's sample, even
access to every other stage preserves the exponential alignment tail. -/
theorem stage_unobserved_alignment_tail {n D k T : ℕ} {κ : Type*} [Fintype κ]
    (hk : k ≤ n) (hD : 0 < D) (j : Fin T)
    (w : OtherStageSamples n D k T j → κ → EuclideanSpace ℝ (Fin D))
    (hw : ∀ y l, ‖w y l‖ ≤ 1) (a : ℝ) (ha : 0 ≤ a) :
    ((fixedChainLaw n D k T hk).toOuterMeasure (stageUnobservedAlignment j w a)).toReal ≤
      Fintype.card κ * Real.exp (-(a ^ 2 * D / 2)) := by
  letI := fixedColumn_nonempty hk
  apply uniform_coordinate_event_le j (fun y : OtherStageSamples n D k T j =>
    {ω | ∃ l, a ≤ ⟪sampledDirection ω, w y l⟫_ℝ})
  intro y
  exact fixedTable_unobserved_alignment_tail hk hD (w y) (hw y) a ha

/-- The union over stages and attempted directions has logarithmic dimension
cost. Applying this to an oracle requires a separate no-leakage coupling. -/
theorem chain_unobserved_alignment_tail {n D k T : ℕ} {κ : Type*} [Fintype κ]
    (hk : k ≤ n) (hD : 0 < D)
    (w : (j : Fin T) → OtherStageSamples n D k T j → κ → EuclideanSpace ℝ (Fin D))
    (hw : ∀ j y l, ‖w j y l‖ ≤ 1) (a : ℝ) (ha : 0 ≤ a) :
    ((fixedChainLaw n D k T hk).toOuterMeasure
      {x | ∃ j, x ∈ stageUnobservedAlignment j (w j) a}).toReal ≤
      T * Fintype.card κ * Real.exp (-(a ^ 2 * D / 2)) := by
  have h := pmf_union_bound (fixedChainLaw n D k T hk) (fun j => stageUnobservedAlignment j (w j) a)
  refine h.trans ?_
  calc
    _ ≤ ∑ _ : Fin T, Fintype.card κ * Real.exp (-(a ^ 2 * D / 2)) :=
      Finset.sum_le_sum (fun j _ => stage_unobserved_alignment_tail hk hD j (w j) (hw j) a ha)
    _ = _ := by simp; ring

end FullJet
