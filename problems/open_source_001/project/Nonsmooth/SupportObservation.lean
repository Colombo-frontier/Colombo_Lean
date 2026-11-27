import Nonsmooth.FiniteSupport
import Nonsmooth.HistoryPolicy

open MeasureTheory
open scoped InnerProductSpace
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {k : ℕ} [Nonempty (Fin k)]

theorem support_maximizers_nonempty (a : Fin k → E) (x : E) :
    (Finset.univ.filter (fun i => finiteSupport a x = ⟪a i, x⟫_ℝ)).Nonempty := by
  classical
  obtain ⟨i, hi⟩ := finiteSupport_attained a x
  exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩

/-- The least maximizing row. This index is recorded for analysis only. -/
def supportWinner (a : Fin k → E) (x : E) : Fin k := by
  classical
  exact (Finset.univ.filter (fun i => finiteSupport a x = ⟪a i, x⟫_ℝ)).min'
    (support_maximizers_nonempty a x)

theorem supportWinner_attained (a : Fin k → E) (x : E) :
    finiteSupport a x = ⟪a (supportWinner a x), x⟫_ℝ := by
  classical
  exact (Finset.mem_filter.mp (Finset.min'_mem _ (support_maximizers_nonempty a x))).2

theorem supportWinner_le (a : Fin k → E) (x : E) {i : Fin k}
    (hi : finiteSupport a x = ⟪a i, x⟫_ℝ) : supportWinner a x ≤ i := by
  classical
  exact Finset.min'_le _ i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)

theorem supportWinner_eq_iff (a : Fin k → E) (x : E) (i : Fin k) :
    supportWinner a x = i ↔ finiteSupport a x = ⟪a i, x⟫_ℝ ∧
      ∀ j : Fin k, j < i → ⟪a j, x⟫_ℝ < finiteSupport a x := by
  constructor
  · intro hi
    refine ⟨hi ▸ supportWinner_attained a x, ?_⟩
    intro j hj
    apply lt_of_le_of_ne (finiteSupport_ge a x j)
    intro he
    have h := supportWinner_le a x he.symm
    rw [hi] at h
    exact (not_le_of_gt hj) h
  · rintro ⟨hi, hlt⟩
    apply le_antisymm (supportWinner_le a x hi)
    by_contra h
    have hh := hlt (supportWinner a x) (lt_of_not_ge h)
    rw [supportWinner_attained a x] at hh
    exact (lt_irrefl _) hh

/-- The constraints on one row imposed by a maximum and its least active index.
Strict inequalities retain the deterministic tie rule even for repeated or zero queries. -/
def supportObservationCell (i w : Fin k) (x : E) (y : ℝ) : Set E :=
  {b | ⟪b, x⟫_ℝ ≤ y ∧ (i = w → ⟪b, x⟫_ℝ = y) ∧ (i < w → ⟪b, x⟫_ℝ < y)}

theorem support_observation_fiber (a : Fin k → E) (x : E) (w : Fin k) (y : ℝ) :
    (supportWinner a x = w ∧ finiteSupport a x = y) ↔
      ∀ i, a i ∈ supportObservationCell i w x y := by
  constructor
  · rintro ⟨hw, hy⟩ i
    have h := (supportWinner_eq_iff a x w).mp hw
    refine ⟨hy ▸ finiteSupport_ge a x i, ?_, ?_⟩
    · intro hi
      subst i
      exact h.1.symm.trans hy
    · intro hi
      exact (h.2 i hi).trans_eq hy
  · intro h
    have hy : finiteSupport a x = y := le_antisymm
      ((Finset.sup'_le_iff _ _).mpr (fun i _ => (h i).1))
      (by rw [← (h w).2.1 rfl]; exact finiteSupport_ge a x w)
    refine ⟨(supportWinner_eq_iff a x w).mpr ⟨?_, ?_⟩, hy⟩
    · exact hy.trans ((h w).2.1 rfl).symm
    · intro i hi
      exact ((h i).2.2 hi).trans_eq hy.symm

theorem supportObservationCell_convex (i w : Fin k) (x : E) (y : ℝ) :
    Convex ℝ (supportObservationCell i w x y) := by
  have hl : IsLinearMap ℝ (fun b : E => ⟪b, x⟫_ℝ) :=
    ⟨fun a b => inner_add_left a b x, fun c b => real_inner_smul_left _ _ _⟩
  have he : Convex ℝ {b : E | i = w → ⟪b, x⟫_ℝ = y} := by
    by_cases h : i = w
    · simpa only [h, true_implies] using convex_hyperplane hl y
    · simpa only [h, false_implies, Set.setOf_true] using (convex_univ : Convex ℝ (Set.univ : Set E))
  have ht : Convex ℝ {b : E | i < w → ⟪b, x⟫_ℝ < y} := by
    by_cases h : i < w
    · simpa only [h, true_implies] using convex_halfSpace_lt hl y
    · simpa only [h, false_implies, Set.setOf_true] using (convex_univ : Convex ℝ (Set.univ : Set E))
  exact (convex_halfSpace_le hl y).inter (he.inter ht)

variable [MeasurableSpace E] [BorelSpace E]

theorem supportObservationCell_measurable (i w : Fin k) (x : E) (y : ℝ) :
    MeasurableSet (supportObservationCell i w x y) := by
  have hm : Measurable (fun b : E => ⟪b, x⟫_ℝ) := (continuous_id.inner continuous_const).measurable
  have he : MeasurableSet {b : E | i = w → ⟪b, x⟫_ℝ = y} := by
    by_cases h : i = w
    · simpa only [h, true_implies] using measurableSet_eq_fun hm measurable_const
    · simp only [h, false_implies, Set.setOf_true, MeasurableSet.univ]
  have ht : MeasurableSet {b : E | i < w → ⟪b, x⟫_ℝ < y} := by
    by_cases h : i < w
    · simpa only [h, true_implies] using measurableSet_lt hm measurable_const
    · simp only [h, false_implies, Set.setOf_true, MeasurableSet.univ]
  exact (measurableSet_le hm measurable_const).inter (he.inter ht)

theorem supportWinner_measurable [SecondCountableTopology E] :
    Measurable (fun z : (Fin k → E) × E => supportWinner z.1 z.2) := by
  apply measurable_to_countable'
  intro i
  have he : (fun z : (Fin k → E) × E => supportWinner z.1 z.2) ⁻¹' {i} =
      {z | finiteSupport z.1 z.2 = ⟪z.1 i, z.2⟫_ℝ ∧
        ∀ j : Fin k, j < i → ⟪z.1 j, z.2⟫_ℝ < finiteSupport z.1 z.2} := by
    ext z
    exact supportWinner_eq_iff z.1 z.2 i
  rw [he]
  have hm (j : Fin k) : Measurable (fun z : (Fin k → E) × E => ⟪z.1 j, z.2⟫_ℝ) :=
    (((continuous_apply j).comp continuous_fst).inner continuous_snd).measurable
  refine (measurableSet_eq_fun finiteSupport_joint_continuous.measurable (hm i)).inter ?_
  have hall (j : Fin k) : MeasurableSet {z : (Fin k → E) × E |
      j < i → ⟪z.1 j, z.2⟫_ℝ < finiteSupport z.1 z.2} := by
    by_cases hj : j < i
    · simpa only [hj, true_implies] using measurableSet_lt (hm j) finiteSupport_joint_continuous.measurable
    · simp only [hj, false_implies, Set.setOf_true, MeasurableSet.univ]
  convert MeasurableSet.iInter hall using 1
  ext z
  simp only [Set.mem_iInter, Set.mem_setOf_eq]
  rfl

end
end Nonsmooth
