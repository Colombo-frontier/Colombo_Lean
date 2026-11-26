import Bilevel.ChiSelectedFrameRun
import Bilevel.SourceFrameShadow

/-! The named-column set is exactly the retained prefix determined by the
actual live-success counter, including failed coins and halted programs. -/
noncomputable section
open MeasureTheory
universe u
namespace Bilevel.ChiHierarchyExecution
open ChiHierarchyIndex BorelAdaptive EuclideanGaussian ProjectionPosterior

def prefixSet {T : ℕ} (r : ℕ) : Set (Fin T) := {k | k.val<r}

theorem prefixSet_advance (counts : ℕ → ℕ) (J q : ℕ) (i : FrameIndex counts J) :
    (if requested counts J q i then
      insert (columnIndex counts J q i) (prefixSet (retained counts J q i))
    else prefixSet (retained counts J q i)) = prefixSet (retained counts J (q+1) i) := by
  classical
  have hb := retained_success_bounds counts J q i
  by_cases hr : requested counts J q i
  · rw [if_pos hr]
    have hk := columnIndex_of_requested counts J q i hr
    ext k
    simp only [Set.mem_insert_iff,prefixSet,Set.mem_setOf_eq,Fin.ext_iff,hk]
    change retained counts J q i < retained counts J (q+1) i at hr
    omega
  · rw [if_neg hr]
    change ¬retained counts J q i < retained counts J (q+1) i at hr
    have he : retained counts J (q+1) i=retained counts J q i := by omega
    rw [he]

variable {S : Type u} {Q O Y : Type*} [MeasurableSpace S] [MeasurableSpace Q]
  [MeasurableSpace O] [MeasurableSpace Y]
variable (counts : ℕ → ℕ) (J D : ℕ) (i : FrameIndex counts J) (A : Program S Q O Y)
  (evaluate : Q → Store counts J (Space D) → Store counts J (Space D) → Bool → O)
  (he : Measurable (fun p : Q × (Store counts J (Space D) × (Store counts J (Space D) × Bool)) =>
    evaluate p.1 p.2.1 p.2.2.1 p.2.2.2))
  (first second : Q × Store counts J (Space D) → Space D)
  (hf : Measurable first) (hs : Measurable second) (output : Y → Space D) (ho : Measurable output)

theorem frame_step_counter (t : ℕ) (h : FrameMemory counts J D S)
    (U : Frame D (chainSize i+1)) :
    (SourceFrameActions.step (frameRules counts J D i A evaluate he first second hf hs output ho) t h U).2.2.1 =
      if A.halt h.2.1 then h.2.2.1 else h.2.2.1 + if h.1.2 t then 1 else 0 := by
  cases hh : A.halt h.2.1 <;> cases hb : h.1.2 t <;>
    simp only [SourceFrameActions.step,frameRules,frameFinish,hh,hb,if_true,Bool.false_eq_true,if_false,
      partialResponse,ChiHierarchyIndex.update,Nat.add_zero]

theorem frame_named_step (t : ℕ)
    (s : SourceFrameActions.State (FrameMemory counts J D S) D (chainSize i+1))
    (U : Frame D (chainSize i+1))
    (hK : s.2.2=prefixSet (retained counts J s.1.2.2.1 i)) :
    (SourceFrameActions.observeStep
      (frameRules counts J D i A evaluate he first second hf hs output ho) t s U).2.2 =
      prefixSet (retained counts J (SourceFrameActions.observeStep
        (frameRules counts J D i A evaluate he first second hf hs output ho) t s U).1.2.2.1 i) := by
  rw [SourceFrameActions.observeStep_memory,frame_step_counter]
  cases hh : A.halt s.1.2.1 with
  | true =>
    simp only [SourceFrameActions.observeStep,frameRules,frameRequest,hh,Bool.true_eq_false,
      false_and,decide_false,Bool.false_eq_true,if_false,if_true,hK]
  | false =>
    cases hb : s.1.1.2 t with
    | false =>
      simp only [SourceFrameActions.observeStep,frameRules,frameRequest,hh,hb,Bool.false_eq_true,
        true_and,false_and,decide_false,if_false,Nat.add_zero,hK]
    | true =>
      have hp := prefixSet_advance counts J s.1.2.2.1 i
      by_cases hr : requested counts J s.1.2.2.1 i
      · simpa only [SourceFrameActions.observeStep,frameRules,frameRequest,hh,hb,true_and,
          decide_eq_true_eq,if_true,Bool.false_eq_true,if_false,hK,if_pos hr] using hp
      · simpa only [SourceFrameActions.observeStep,frameRules,frameRequest,hh,hb,true_and,
          decide_eq_true_eq,if_true,Bool.false_eq_true,if_false,hK,if_neg hr] using hp

theorem frame_named_run : ∀ n t
    (s : SourceFrameActions.State (FrameMemory counts J D S) D (chainSize i+1))
    (U : Frame D (chainSize i+1)),
    s.2.2=prefixSet (retained counts J s.1.2.2.1 i) →
    (SourceFrameActions.observeRun
      (frameRules counts J D i A evaluate he first second hf hs output ho) n t s U).2.2 =
      prefixSet (retained counts J (SourceFrameActions.observeRun
        (frameRules counts J D i A evaluate he first second hf hs output ho) n t s U).1.2.2.1 i) := by
  intro n
  induction n with
  | zero => intros; assumption
  | succ n ih =>
    intro t s U hK
    exact ih (t+1) _ U (frame_named_step counts J D i A evaluate he first second hf hs output ho t s U hK)

end Bilevel.ChiHierarchyExecution
