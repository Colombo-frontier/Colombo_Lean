import Bilevel.ChiCanonicalHierarchy

/-! An actual finite disclosed-column store. A successful live coin advances
the public counter once. The update receives only requested new vectors;
no hidden frame is an argument of the update function. -/
noncomputable section
open MeasureTheory
namespace Bilevel.ChiHierarchyIndex
open ChiPrefixEvaluation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

abbrev Store (counts : ℕ → ℕ) (J : ℕ) (E : Type*) := ℕ × FiniteColumns counts J E
abbrev Replies (counts : ℕ → ℕ) (J : ℕ) (E : Type*) := FrameIndex counts J → E

def initial (counts : ℕ → ℕ) (J : ℕ) : Store counts J E := (0,0)

def advanceColumns (counts : ℕ → ℕ) (J q : ℕ) (C : FiniteColumns counts J E)
    (y : Replies counts J E) : FiniteColumns counts J E := fun i =>
  (advanceStore (chainSize i) (retained counts J q i,C i)
    (retained counts J (q+1) i) (y i)).2

def update (counts : ℕ → ℕ) (J : ℕ) (s : Store counts J E) (success : Bool)
    (y : Replies counts J E) : Store counts J E :=
  if success then (s.1+1,advanceColumns counts J s.1 s.2 y) else s

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [BorelSpace E] [SecondCountableTopology E] in
theorem advanceColumns_measurable (counts : ℕ → ℕ) (J q : ℕ) :
    Measurable (fun p : FiniteColumns counts J E × Replies counts J E => advanceColumns counts J q p.1 p.2) := by
  apply measurable_pi_lambda
  intro i
  have ha : Measurable (fun p : FiniteColumns counts J E × Replies counts J E =>
      ((retained counts J q i,p.1 i),(retained counts J (q+1) i,p.2 i))) :=
    (measurable_const.prodMk ((measurable_pi_apply i).comp measurable_fst)).prodMk
      (measurable_const.prodMk ((measurable_pi_apply i).comp measurable_snd))
  exact measurable_snd.comp ((advanceStore_measurable (chainSize i)).comp ha)

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [BorelSpace E] [SecondCountableTopology E] in
theorem update_measurable (counts : ℕ → ℕ) (J : ℕ) :
    Measurable (fun p : Store counts J E × (Bool × Replies counts J E) => update counts J p.1 p.2.1 p.2.2) := by
  have hv : Measurable (fun p : (FiniteColumns counts J E × Replies counts J E) × ℕ =>
      advanceColumns counts J p.2 p.1.1 p.1.2) :=
    measurable_from_prod_countable (advanceColumns_measurable (E:=E) counts J)
  have ha : Measurable (fun p : Store counts J E × (Bool × Replies counts J E) =>
      ((p.1.2,p.2.2),p.1.1)) :=
    (((measurable_snd.comp measurable_fst).prodMk (measurable_snd.comp measurable_snd)).prodMk
      (measurable_fst.comp measurable_fst))
  have hs : MeasurableSet {p : Store counts J E × (Bool × Replies counts J E) | p.2.1=true} := by
    have hm : Measurable (fun p : Store counts J E × (Bool × Replies counts J E) => p.2.1) :=
      measurable_fst.comp measurable_snd
    exact hm (measurableSet_singleton true)
  exact (((measurable_fst.comp measurable_fst).add_const 1).prodMk (hv.comp ha)).ite hs measurable_fst

def actual (counts : ℕ → ℕ) (J q : ℕ) (U : FiniteColumns counts J E) : Store counts J E :=
  (q,fun i => paddedPrefix (chainSize i) (retained counts J q i) (U i))

def revealReply (counts : ℕ → ℕ) (J q : ℕ) (success : Bool) (U : FiniteColumns counts J E) : Replies counts J E :=
  fun i => if success=true ∧ retained counts J q i < retained counts J (q+1) i then
    actualNextColumn (chainSize i) (retained counts J q i) (U i) else 0

omit [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
theorem revealReply_zero (counts : ℕ → ℕ) (J q : ℕ) (success : Bool) (U : FiniteColumns counts J E)
    (i : FrameIndex counts J) (h : ¬(success=true ∧ retained counts J q i < retained counts J (q+1) i)) :
    revealReply counts J q success U i = 0 := if_neg h

omit [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
theorem actual_zero (counts : ℕ → ℕ) (J : ℕ) (U : FiniteColumns counts J E) :
    actual counts J 0 U = initial counts J := by
  refine Prod.ext rfl ?_
  funext i k
  simp [actual,initial,paddedPrefix,retained_zero]

omit [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
theorem update_actual (counts : ℕ → ℕ) (J q : ℕ) (success : Bool) (U : FiniteColumns counts J E) :
    update counts J (actual counts J q U) success (revealReply counts J q success U) =
      actual counts J (q + if success then 1 else 0) U := by
  cases success with
  | false => simp [update]
  | true =>
    refine Prod.ext rfl ?_
    funext i
    have hs := retained_success_bounds counts J q i
    by_cases hi : retained counts J q i < retained counts J (q+1) i
    · have hh := advance_actualStore (chainSize i) (retained counts J q i) (retained counts J (q+1) i)
        (U i) hs.1 hs.2 (retained_le counts J (q+1) i)
      simpa only [update,actual,if_true,advanceColumns,revealReply,true_and,if_pos hi,actualStore]
        using congrArg Prod.snd hh
    · have he : retained counts J q i = retained counts J (q+1) i := by omega
      simp only [update,actual,if_true,advanceColumns,advanceStore,he,lt_self_iff_false,if_false]

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
theorem actual_gram (counts : ℕ → ℕ) (J q : ℕ) (U : FiniteColumns counts J E)
    (hU : ∀ i, Orthonormal ℝ (U i)) (i : FrameIndex counts J) :
    PrefixGram (chainSize i) (retained counts J q i) ((actual counts J q U).2 i) :=
  paddedPrefix_gram _ _ _ (hU i)

end Bilevel.ChiHierarchyIndex
