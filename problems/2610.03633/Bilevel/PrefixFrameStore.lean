import Bilevel.PrefixGramMeasurable
import Bilevel.FramePrefixDisclosure

/-! A concrete finite observer store containing only disclosed columns.
The next revealed vector is inserted by a Borel update; the hidden tail is
zero. Correctness is proved against an actual orthonormal frame, without
giving its undisclosed columns to the update function. -/
noncomputable section
open MeasureTheory
namespace Bilevel.ChiPrefixEvaluation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

abbrev PrefixStore (n : ℕ) (E : Type*) := ℕ × (Fin (n+1) → E)

def initialStore (n : ℕ) : PrefixStore n E := (0,0)

def insertStore (n : ℕ) (s : PrefixStore n E) (y : E) : PrefixStore n E :=
  if h : s.1<n+1 then (s.1+1,Function.update s.2 ⟨s.1,h⟩ y) else s

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [BorelSpace E] [SecondCountableTopology E] in
theorem insertStore_measurable (n : ℕ) :
    Measurable (fun p : PrefixStore n E × E => insertStore n p.1 p.2) := by
  have hfixed (r : ℕ) : Measurable (fun p : (Fin (n+1) → E) × E => insertStore n (r,p.1) p.2) := by
    by_cases hr : r<n+1
    · simp only [insertStore,dif_pos hr]
      apply measurable_const.prodMk
      apply measurable_pi_lambda
      intro i
      by_cases hi : i=⟨r,hr⟩
      · subst i
        simpa only [Function.update_self] using (measurable_snd : Measurable (fun p : (Fin (n+1) → E) × E => p.2))
      · simpa only [Function.update_of_ne hi] using (measurable_pi_apply i).comp
          (measurable_fst : Measurable (fun p : (Fin (n+1) → E) × E => p.1))
    · simp only [insertStore,dif_neg hr]
      exact measurable_const.prodMk measurable_fst
  have hm : Measurable (fun p : ((Fin (n+1) → E) × E) × ℕ =>
      insertStore n (p.2,p.1.1) p.1.2) := measurable_from_prod_countable hfixed
  have ha : Measurable (fun p : PrefixStore n E × E => ((p.1.2,p.2),p.1.1)) :=
    (((measurable_snd.comp measurable_fst).prodMk measurable_snd).prodMk
      (measurable_fst.comp measurable_fst))
  exact hm.comp ha

def actualStore (n r : ℕ) (U : Fin (n+1) → E) : PrefixStore n E := (r,paddedPrefix n r U)

omit [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
theorem actualStore_zero (n : ℕ) (U : Fin (n+1) → E) : actualStore n 0 U=initialStore n := by
  refine Prod.ext rfl ?_
  funext i
  simp [actualStore,initialStore,paddedPrefix]

omit [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
theorem insert_actualStore (n r : ℕ) (U : Fin (n+1) → E) (hr : r<n+1) :
    insertStore n (actualStore n r U) (U ⟨r,hr⟩)=actualStore n (r+1) U := by
  simp only [insertStore,actualStore,dif_pos hr]
  refine Prod.ext rfl ?_
  funext i
  by_cases hi : i=⟨r,hr⟩
  · subst i
    simp [Function.update_self,paddedPrefix]
  · have hv : i.val≠r := by intro h;apply hi;exact Fin.ext h
    have he : i.val<r+1 ↔ i.val<r := by omega
    simp only [Function.update_of_ne hi,paddedPrefix,he]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
theorem insertStore_complete (n : ℕ) (s : PrefixStore n E) (y : E) (hr : n+1≤s.1) :
    insertStore n s y=s := dif_neg (by omega)

def ValidStore (n : ℕ) (s : PrefixStore n E) : Prop :=
  s.1≤n+1 ∧ PrefixGram n s.1 s.2 ∧ ∀ i : Fin (n+1),s.1 ≤ i.val → s.2 i=0

theorem validStore_measurable (n : ℕ) : MeasurableSet {s : PrefixStore n E | ValidStore n s} := by
  have hc : MeasurableSet {s : PrefixStore n E | s.1≤n+1} :=
    measurable_fst (Set.to_countable {r : ℕ | r≤n+1}).measurableSet
  have ht : MeasurableSet {s : PrefixStore n E | ∀ i : Fin (n+1),s.1 ≤ i.val → s.2 i=0} := by
    have hi (i : Fin (n+1)) : MeasurableSet {s : PrefixStore n E | ¬s.1 ≤ i.val ∨ s.2 i=0} :=
      (measurable_fst (Set.to_countable {r : ℕ | r ≤ i.val}).measurableSet).compl.union
        (((measurable_pi_apply i).comp measurable_snd) (measurableSet_singleton 0))
    convert MeasurableSet.iInter hi using 1
    ext s
    simp only [Set.mem_iInter,Set.mem_setOf_eq]
    exact forall_congr' (fun i => by tauto)
  exact hc.inter ((prefixGram_measurable n).inter ht)

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
theorem actualStore_valid (n r : ℕ) (U : Fin (n+1) → E) (hr : r≤n+1) (hU : Orthonormal ℝ U) :
    ValidStore n (actualStore n r U) := by
  refine ⟨hr,paddedPrefix_gram n r U hU,?_⟩
  intro i hi
  change r ≤ i.val at hi
  exact if_neg (by omega)

def advanceStore (n : ℕ) (s : PrefixStore n E) (next : ℕ) (y : E) : PrefixStore n E :=
  if s.1<next then insertStore n s y else s

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [BorelSpace E] [SecondCountableTopology E] in
theorem advanceStore_measurable (n : ℕ) :
    Measurable (fun p : PrefixStore n E × (ℕ × E) => advanceStore n p.1 p.2.1 p.2.2) := by
  have hi : MeasurableSet {p : PrefixStore n E × (ℕ × E) | p.1.1<p.2.1} :=
    ((measurable_fst.comp measurable_fst).prodMk (measurable_fst.comp measurable_snd))
      (Set.to_countable {q : ℕ × ℕ | q.1<q.2}).measurableSet
  exact ((insertStore_measurable n).comp
    (measurable_fst.prodMk (measurable_snd.comp measurable_snd))).ite hi measurable_fst

def actualNextColumn (n r : ℕ) (U : Fin (n+1) → E) : E :=
  if h : r<n+1 then U ⟨r,h⟩ else 0

omit [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
theorem advance_actualStore (n r s : ℕ) (U : Fin (n+1) → E)
    (hrs : r≤s) (hs : s≤r+1) (hsT : s≤n+1) :
    advanceStore n (actualStore n r U) s (actualNextColumn n r U)=actualStore n s U := by
  by_cases he : r=s
  · subst s
    simp [advanceStore,actualStore]
  · have hlt : r<s := by omega
    have hr : r<n+1 := by omega
    have hsucc : s=r+1 := by omega
    simp only [advanceStore,actualStore,if_pos hlt,actualNextColumn,dif_pos hr]
    rw [hsucc]
    exact insert_actualStore n r U hr

omit [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
theorem sourceStore_update (n : ℕ → ℕ) (J q j : ℕ) (I : List ℕ) (U : Fin (n (j+1)+1) → E) :
    advanceStore (n (j+1)) (actualStore (n (j+1)) (ChiTreeProgress.innerCounter n J q j I) U)
      (ChiTreeProgress.innerCounter n J (q+1) j I)
      (actualNextColumn (n (j+1)) (ChiTreeProgress.innerCounter n J q j I) U)=
      actualStore (n (j+1)) (ChiTreeProgress.innerCounter n J (q+1) j I) U :=
  advance_actualStore _ _ _ U (ChiTreeProgress.inner_counter_success_bounds n J q j I).1
    (ChiTreeProgress.inner_counter_success_bounds n J q j I).2
    (FramePrefixDisclosure.inner_le n J (q+1) j I)

end Bilevel.ChiPrefixEvaluation


