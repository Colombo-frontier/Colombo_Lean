import Bilevel.ChiSelectedFrameStep
import Bilevel.BorelAdaptiveRunShift

/-! The selected-frame raw policy executes the same halted source program
and finite success-counter store, with arbitrary independent other-frame
context. This is an execution identity, before any concentration estimate. -/
noncomputable section
open MeasureTheory
universe u
namespace Bilevel.ChiHierarchyExecution
open ChiHierarchyIndex BorelAdaptive EuclideanGaussian

variable {S : Type u} {Q O Y : Type*} [MeasurableSpace S] [MeasurableSpace Q]
  [MeasurableSpace O] [MeasurableSpace Y]
variable (counts : ℕ → ℕ) (J D : ℕ) (i : FrameIndex counts J) (A : Program S Q O Y)
  (evaluate : Q → Store counts J (Space D) → Store counts J (Space D) → Bool → O)
  (he : Measurable (fun p : Q × (Store counts J (Space D) × (Store counts J (Space D) × Bool)) =>
    evaluate p.1 p.2.1 p.2.2.1 p.2.2.2))
  (first second : Q × Store counts J (Space D) → Space D)
  (hf : Measurable first) (hs : Measurable second) (output : Y → Space D) (ho : Measurable output)

theorem frame_run_actual : ∀ n t (h : FrameMemory counts J D S) (U : FiniteColumns counts J (Space D)),
    (∀ j, j ≠ i → h.1.1 j = U j) →
    SourceFrameActions.run (frameRules counts J D i A evaluate he first second hf hs output ho) n t h (U i) =
      (h.1,BorelAdaptive.run (instrument counts J A) (response counts J evaluate) U
        (fun k => h.1.2 (t+k)) h.2 n) := by
  intro n
  induction n with
  | zero => intros; rfl
  | succ n ih =>
    intro t h U hC
    rw [SourceFrameActions.run,frame_step_actual counts J D i A evaluate he first second hf hs output ho t h U hC]
    rw [ih (t+1) (h.1,BorelAdaptive.step (instrument counts J A) (response counts J evaluate) U (h.1.2 t) h.2) U hC]
    rw [BorelAdaptive.run_succ_first]
    have hd : (fun k => h.1.2 ((t+1)+k)) = (fun k => h.1.2 (t+(k+1))) := by
      funext k
      exact congrArg h.1.2 (by omega : (t+1)+k = t+(k+1))
    simp only [Nat.add_zero,hd]

theorem compiled_frame_run_actual (n R : ℕ) (hR : n ≤ R)
    (C U : FiniteColumns counts J (Space D)) (hC : ∀ j, j ≠ i → C j = U j)
    (s : S) (draws : ℕ → Bool) (V : Submodule ℝ (Space D)) (K : Set (Fin (chainSize i+1))) :
    let L := frameRules counts J D i A evaluate he first second hf hs output ho
    let h : FrameMemory counts J D S := ((C,draws),initialState counts J s)
    (OrdinaryFrame.run (SourceFrameActions.compileRules L) n R 0 ((h,false),(V,K)) (U i)).1 =
      (((C,draws),run counts J A evaluate U s draws n),false) := by
  dsimp only
  rw [SourceFrameActions.compiled_run_memory _ n R 0 _ V K (U i) hR]
  rw [frame_run_actual counts J D i A evaluate he first second hf hs output ho n 0 _ U hC]
  simp only [Nat.zero_add,run]

end Bilevel.ChiHierarchyExecution
