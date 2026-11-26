import SecondOrder.FiniteProductEntropy

open MeasureTheory
open scoped BigOperators Classical

namespace SecondOrder
noncomputable section

theorem fin_prod_prefix {M : Type*} [CommMonoid M] {k n : ℕ} (hk : k≤n) (a : Fin k → M) :
    (∏ i : Fin n, if hi : i.val<k then a ⟨i.val,hi⟩ else 1) = ∏ i, a i := by
  induction n with
  | zero =>
    have he : k=0 := by omega
    subst k
    simp
  | succ n ih =>
    by_cases he : k=n+1
    · subst k
      apply Finset.prod_congr rfl
      intro i _
      simp only [dif_pos i.isLt]
    · have hkn : k≤n := by omega
      rw [Fin.prod_univ_castSucc]
      simp only [Fin.val_last, dif_neg (by omega : ¬n<k), mul_one]
      exact ih hkn

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

def finPrefix {k n : ℕ} (hk : k≤n) (w : Fin n → α) (i : Fin k) : α :=
  w ⟨i.val,by omega⟩

/-- Exact joint marginal law of a prefix of independent finite arrays. -/
theorem finitePiPMF_prefix {k n : ℕ} (p : Fin n → PMF α) (hk : k≤n) :
    (finitePiPMF p).toMeasure.map (finPrefix hk) =
      (finitePiPMF (fun i : Fin k => p ⟨i.val,by omega⟩)).toMeasure := by
  apply Measure.ext_of_singleton
  intro v
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _),
    finitePiPMF_toMeasure]
  have he : finPrefix hk ⁻¹' ({v} : Set (Fin k → α)) =
      Set.univ.pi (fun i : Fin n => if hi : i.val<k then {v ⟨i.val,hi⟩} else Set.univ) := by
    ext w
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_pi, Set.mem_univ, forall_true_left]
    constructor
    · intro hw i
      split_ifs with hi
      · have hh := congrFun hw ⟨i.val,hi⟩
        exact hh
      · trivial
    · intro hw
      funext i
      have hh := hw (⟨i.val,by omega⟩ : Fin n)
      simpa only [dif_pos i.isLt, Set.mem_singleton_iff, finPrefix] using hh
  rw [he, Measure.pi_pi, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    finitePiPMF_apply]
  have hf (i : Fin n) : (p i).toMeasure (if hi : i.val<k then {v ⟨i.val,hi⟩} else Set.univ) =
      if hi : i.val<k then p i (v ⟨i.val,hi⟩) else 1 := by
    split_ifs
    · exact PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)
    · exact measure_univ
  simp only [hf]
  exact fin_prod_prefix hk (fun i => p ⟨i.val,by omega⟩ (v i))

theorem finitePiPMF_snoc_map {k : ℕ} (p : Fin (k+1) → PMF α) :
    (finitePiPMF p).toMeasure.map (fun w => ((fun i : Fin k => w i.castSucc), w (Fin.last k))) =
      (finitePiPMF (fun i : Fin k => p i.castSucc)).toMeasure.prod (p (Fin.last k)).toMeasure := by
  apply Measure.ext_of_singleton
  intro v
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
  have he : (fun w : Fin (k+1) → α => ((fun i : Fin k => w i.castSucc),w (Fin.last k))) ⁻¹' {v} =
      {Fin.snoc v.1 v.2} := by
    ext w
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq]
    constructor
    · rintro ⟨h1,h2⟩
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using h2
      · simpa using congrFun h1 j
    · intro h
      subst w
      simp
  rw [he, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), finitePiPMF_apply,
    Fin.prod_univ_castSucc]
  have hp : ({v} : Set ((Fin k → α) × α)) = ({v.1} : Set (Fin k → α)) ×ˢ ({v.2} : Set α) := by
    ext y
    simp [Prod.ext_iff]
  rw [hp, Measure.prod_prod, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), finitePiPMF_apply]
  simp

/-- Joint law of all past arrays and the next array, with unused later arrays
integrated out exactly. -/
theorem finitePiPMF_prefix_next {k n : ℕ} (p : Fin n → PMF α) (hk : k<n) :
    (finitePiPMF p).toMeasure.map
      (fun w => ((fun i : Fin k => w ⟨i.val,by omega⟩), w ⟨k,hk⟩)) =
      (finitePiPMF (fun i : Fin k => p ⟨i.val,by omega⟩)).toMeasure.prod (p ⟨k,hk⟩).toMeasure := by
  have hprefix := finitePiPMF_prefix p (show k+1≤n by omega)
  have hh := finitePiPMF_snoc_map (fun i : Fin (k+1) => p ⟨i.val,by omega⟩)
  rw [← hprefix, Measure.map_map (measurable_of_countable _) (measurable_of_countable _)] at hh
  exact hh

end
end SecondOrder
