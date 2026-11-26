import Bilevel.ConditionalConfidenceTail

/-! Measurability of the actual least-index median-distance selector. -/
noncomputable section
open MeasureTheory
namespace Bilevel.ConditionalConfidence

variable {E : Type*} [PseudoMetricSpace E] {q : ℕ} [NeZero q]

theorem radius_le_iff_capacity (z : Fin q → E) (i : Fin q) (r : ℝ) :
    radius z i ≤ r ↔ half q ≤ (ball z i r).card := by
  constructor
  · intro h
    apply (radius_capacity z i).trans
    apply Finset.card_le_card
    intro j hj
    exact mem_ball.mpr ((mem_ball.mp hj).trans h)
  · exact radius_le_of_capacity z i

theorem selectedIndex_eq_iff (z : Fin q → E) (i : Fin q) :
    selectedIndex z = i ↔
      (∀ j, radius z i ≤ radius z j) ∧
        (∀ j, j < i → radius z i < radius z j) := by
  constructor
  · intro hi
    constructor
    · intro j
      simpa only [hi] using selected_radius_le z j
    · intro j hji
      by_contra h
      have hji' : radius z j ≤ radius z i := le_of_not_gt h
      have hopt : ∀ k, radius z j ≤ radius z k := fun k =>
        hji'.trans (by simpa only [hi] using selected_radius_le z k)
      have hj := selectedIndex_le_of_optimal z j hopt
      rw [hi] at hj
      exact (not_lt_of_ge hj) hji
  · rintro ⟨hmin, hstrict⟩
    apply le_antisymm (selectedIndex_le_of_optimal z i hmin)
    by_contra h
    have hi := hstrict (selectedIndex z) (lt_of_not_ge h)
    exact (not_lt_of_ge (selected_radius_le z i)) hi

section Measurability
variable {Ω : Type*} [MeasurableSpace Ω]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (Z : Ω → Fin q → E) (hZ : ∀ i, Measurable (fun ω => Z ω i))

include hZ

omit [NeZero q] in
theorem ball_card_measurable (i : Fin q) (r : ℝ) :
    Measurable (fun ω => ((ball (Z ω) i r).card : ℝ)) := by
  classical
  have hm : Measurable (fun ω => ∑ j : Fin q,
      if dist (Z ω i) (Z ω j) ≤ r then (1 : ℝ) else 0) := by
    apply Finset.measurable_sum
    intro j _
    exact Measurable.ite (measurableSet_le ((hZ i).dist (hZ j)) measurable_const)
      measurable_const measurable_const
  simpa only [Finset.sum_boole, ball] using hm

theorem radius_measurable (i : Fin q) : Measurable (fun ω => radius (Z ω) i) := by
  apply measurable_of_Iic
  intro r
  have hm := measurableSet_le (measurable_const (a := (half q : ℝ)))
    (ball_card_measurable Z hZ i r)
  convert hm using 1
  ext ω
  simp only [Set.mem_preimage, Set.mem_Iic, radius_le_iff_capacity, Set.mem_setOf_eq,
    Nat.cast_le]

theorem selectedIndex_fiber_measurable (i : Fin q) :
    MeasurableSet {ω | selectedIndex (Z ω) = i} := by
  have hmin : MeasurableSet {ω | ∀ j, radius (Z ω) i ≤ radius (Z ω) j} := by
    simp only [Set.setOf_forall]
    exact MeasurableSet.iInter fun j => measurableSet_le
      (radius_measurable Z hZ i) (radius_measurable Z hZ j)
  have hstrict : MeasurableSet {ω | ∀ j, j < i → radius (Z ω) i < radius (Z ω) j} := by
    simp only [Set.setOf_forall]
    apply MeasurableSet.iInter
    intro j
    apply MeasurableSet.iInter
    intro _
    exact measurableSet_lt (radius_measurable Z hZ i) (radius_measurable Z hZ j)
  simpa only [selectedIndex_eq_iff, Set.setOf_and] using hmin.inter hstrict

theorem select_measurable : Measurable (fun ω => select (Z ω)) := by
  intro s hs
  have heq : (fun ω => select (Z ω)) ⁻¹' s =
      ⋃ i : Fin q, {ω | selectedIndex (Z ω) = i} ∩ (fun ω => Z ω i) ⁻¹' s := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · intro h
      exact ⟨selectedIndex (Z ω), rfl, h⟩
    · rintro ⟨i, hi, h⟩
      simpa only [select, hi] using h
  rw [heq]
  exact MeasurableSet.iUnion fun i => (selectedIndex_fiber_measurable Z hZ i).inter (hZ i hs)

end Measurability
end Bilevel.ConditionalConfidence
