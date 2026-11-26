import Bilevel.ChiSelectedFrameBatch

/-! Exact original source execution after each finite frozen batch. The
larger observation horizon does not change the source call horizon. -/
noncomputable section
open MeasureTheory
universe u
namespace Bilevel.ChiHierarchyExecution
open ChiHierarchyIndex BorelAdaptive EuclideanGaussian

variable {S : Type u} {Q O Y : Type*} [MeasurableSpace S] [MeasurableSpace Q]
  [MeasurableSpace O] [MeasurableSpace Y]
variable (counts : ℕ → ℕ) (J D m : ℕ) (i : FrameIndex counts J) (A : Program S Q O Y)
  (evaluate : Q → Store counts J (Space D) → Store counts J (Space D) → Bool → O)
  (he : Measurable (fun p : Q × (Store counts J (Space D) × (Store counts J (Space D) × Bool)) =>
    evaluate p.1 p.2.1 p.2.2.1 p.2.2.2))
  (queries : Fin m → Q × Store counts J (Space D) → Space D) (hq : ∀ k, Measurable (queries k))
  (output : Y → Space D) (ho : Measurable output)

def batchedFrameRules :=
  SourceFrameActions.batchRules
    (frameRules counts J D i A evaluate he (fun _ => 0) (fun _ => 0)
      measurable_const measurable_const output ho)
    (batchSize_pos counts J m) (frozenQueries counts J D m i A queries)
    (frozenQueries_measurable counts J D m i A queries hq)

theorem compiled_batch_frame_run_actual (n R : ℕ) (hR : n*batchSize counts J m ≤ R)
    (C U : FiniteColumns counts J (Space D)) (hC : ∀ j, j ≠ i → C j = U j)
    (s : S) (draws : ℕ → Bool) (V : Submodule ℝ (Space D)) (K : Set (Fin (chainSize i+1))) :
    let L := batchedFrameRules counts J D m i A evaluate he queries hq output ho
    let h : FrameMemory counts J D S := ((C,draws),initialState counts J s)
    (OrdinaryFrame.run (SourceFrameActions.compileRules L) (n*batchSize counts J m) R 0
      ((h,false),(V,K)) (U i)).1 =
      (((C,draws),run counts J A evaluate U s draws n),false) := by
  dsimp only
  unfold batchedFrameRules
  have ht : 0 = 0*batchSize counts J m := by simp
  rw [ht,SourceFrameActions.compiled_batch_run_memory _ _ _ _ _ _ _ _ _ _ _ hR]
  rw [frame_run_actual counts J D i A evaluate he (fun _ => 0) (fun _ => 0)
    measurable_const measurable_const output ho n 0 _ U hC]
  simp only [Nat.zero_add,run]

end Bilevel.ChiHierarchyExecution
