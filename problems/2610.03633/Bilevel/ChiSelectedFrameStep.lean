import Bilevel.ChiSelectedFrameRules

/-! Exact one-step identification of the selected-frame raw-genie source
machine with the full finite-store execution, including halted calls. -/
noncomputable section
open MeasureTheory
universe u
namespace Bilevel.ChiHierarchyExecution
open ChiHierarchyIndex BorelAdaptive EuclideanGaussian

variable {S : Type u} {Q O Y : Type*} [MeasurableSpace S] [MeasurableSpace Q]
  [MeasurableSpace O] [MeasurableSpace Y]

theorem frame_step_actual (counts : ℕ → ℕ) (J D : ℕ) (i : FrameIndex counts J)
    (A : Program S Q O Y)
    (evaluate : Q → Store counts J (Space D) → Store counts J (Space D) → Bool → O)
    (he : Measurable (fun p : Q × (Store counts J (Space D) × (Store counts J (Space D) × Bool)) =>
      evaluate p.1 p.2.1 p.2.2.1 p.2.2.2))
    (first second : Q × Store counts J (Space D) → Space D)
    (hf : Measurable first) (hs : Measurable second) (output : Y → Space D) (ho : Measurable output)
    (t : ℕ) (h : FrameMemory counts J D S) (U : FiniteColumns counts J (Space D))
    (hC : ∀ j, j ≠ i → h.1.1 j = U j) :
    SourceFrameActions.step (frameRules counts J D i A evaluate he first second hf hs output ho) t h (U i) =
      (h.1,BorelAdaptive.step (instrument counts J A) (response counts J evaluate) U (h.1.2 t) h.2) := by
  cases hh : A.halt h.2.1 with
  | true =>
    simp only [SourceFrameActions.step,frameRules,frameFinish,hh,if_true,
      BorelAdaptive.step,instrument]
  | false =>
    simp only [SourceFrameActions.step,frameRules,frameFinish,hh,Bool.false_eq_true,if_false,
      frameRequest,hh,true_and,decide_eq_true_eq]
    rw [← revealReply_eq counts J h.2.2.1 (h.1.2 t) U i]
    rw [partialResponse_actual counts J i evaluate h.1.1 U hC]
    simp only [BorelAdaptive.step,instrument,hh,Bool.false_eq_true,if_false]

end Bilevel.ChiHierarchyExecution
