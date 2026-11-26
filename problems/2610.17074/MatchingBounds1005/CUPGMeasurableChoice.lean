import MatchingBounds1005.CUPGFiniteChoice

/-! Measurability of bounded stopping and response-only finite minimization. -/
noncomputable section
open MeasureTheory

namespace MatchingBounds1005.CUPG

theorem measurableSet_nat_choice {X : Type*} [MeasurableSpace X]
    (P : X → ℕ → Prop) (hP : ∀ n, MeasurableSet {x | P x n})
    {I : X → ℕ} (hI : Measurable I) : MeasurableSet {x | P x (I x)} := by
  have he : {x | P x (I x)} = ⋃ n : ℕ, {x | I x = n} ∩ {x | P x n} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro h; exact ⟨I x, rfl, h⟩
    · rintro ⟨n, hn, hp⟩; simpa only [hn] using hp
  rw [he]
  exact MeasurableSet.iUnion (fun n => ((measurableSet_singleton n).preimage hI).inter (hP n))

theorem measurable_firstIndex {X : Type*} [MeasurableSpace X]
    (P : X → ℕ → Prop) (hP : ∀ n, MeasurableSet {x | P x n}) (N : ℕ) :
    Measurable (fun x => @firstIndex (P x) (Classical.decPred _) N) := by
  induction N with
  | zero => exact measurable_const
  | succ N ih =>
    exact Measurable.ite (measurableSet_nat_choice P hP ih) ih measurable_const

/-- Only the supplied scalar response coordinates are compared. -/
def indexedBest {E : Type*} (initial : E × ℝ) (r : ℕ → E × ℝ) : ℕ → E × ℝ
  | 0 => initial
  | n + 1 => chooseLowerReply (r n) (indexedBest initial r n)

theorem measurable_indexedBest {E : Type*} [MeasurableSpace E] (N : ℕ) :
    Measurable (fun p : (E × ℝ) × (ℕ → E × ℝ) => indexedBest p.1 p.2 N) := by
  induction N with
  | zero => exact measurable_fst
  | succ N ih =>
    exact chooseLowerReply_measurable.comp
      (((measurable_pi_apply N).comp measurable_snd).prodMk ih)

theorem indexedBest_correct {E : Type*} (f : E → ℝ) (start : E) (x : ℕ → E) (N : ℕ) :
    indexedBest (start, f start) (fun j => (x j, f (x j))) N =
      (bestPoint f start ((List.range N).reverse.map x),
        f (bestPoint f start ((List.range N).reverse.map x))) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [indexedBest, ih, chooseLowerReply_correct]
    simp only [List.range_succ, List.reverse_append, List.reverse_singleton,
      List.singleton_append, List.map_cons, bestPoint]

end MatchingBounds1005.CUPG
