import Bilevel.ChiSelectedFrameObserver

/-! Private initialization and complementary orientations are assembled
into the actual batched hierarchy execution. No selected-frame value is
read by the initializer. -/
noncomputable section
open MeasureTheory
universe u
namespace Bilevel.ChiHierarchyExecution
open ChiHierarchyIndex ChiHierarchyHaar BorelAdaptive EuclideanGaussian TransportControllerMachine

variable {C : Type*} {S : Type u} {Q O Y : Type*} [MeasurableSpace C] [MeasurableSpace S]
  [MeasurableSpace Q] [MeasurableSpace O] [MeasurableSpace Y]
variable {counts : ℕ → ℕ} {J D k : ℕ}

def observerInitial (e : FrameIndex counts J ≃ Fin (k+1))
    (hD : ∀ i : FrameIndex counts J, chainSize i+1≤D) (i : FrameIndex counts J)
    (initial : C → S) (draws : C → ℕ → Bool) (p : IndependentFrame.Context C D k) :
    SourceFrameActions.Marked (FrameMemory counts J D S) :=
  (((otherColumns e hD i p.2,draws p.1),initialState counts J (initial p.1)),false)

theorem observerInitial_measurable (e : FrameIndex counts J ≃ Fin (k+1))
    (hD : ∀ i : FrameIndex counts J, chainSize i+1≤D) (i : FrameIndex counts J)
    (initial : C → S) (hi : Measurable initial) (draws : C → ℕ → Bool) (hd : Measurable draws) :
    Measurable (observerInitial e hD i initial draws) :=
  (((otherColumns_measurable e hD i).comp measurable_snd).prodMk (hd.comp measurable_fst)).prodMk
    ((initialize_measurable counts J).comp (hi.comp measurable_fst)) |>.prodMk measurable_const

omit [MeasurableSpace C] in
theorem compiled_exposed_run_actual (e : FrameIndex counts J ≃ Fin (k+1))
    (hD : ∀ i : FrameIndex counts J, chainSize i+1≤D) (i : FrameIndex counts J)
    (A : Program S Q O Y)
    (evaluate : Q → Store counts J (Space D) → Store counts J (Space D) → Bool → O)
    (he : Measurable (fun p : Q × (Store counts J (Space D) × (Store counts J (Space D) × Bool)) =>
      evaluate p.1 p.2.1 p.2.2.1 p.2.2.2))
    (m : ℕ) (queries : Fin m → Q × Store counts J (Space D) → Space D) (hq : ∀ l, Measurable (queries l))
    (output : Y → Space D) (ho : Measurable output)
    (initial : C → S) (draws : C → ℕ → Bool) (n R : ℕ) (hR : n*batchSize counts J m≤R)
    (p : C × Orientations counts J D) :
    let L := batchedFrameRules counts J D m i A evaluate he queries hq output ho
    let a := sourceExpose e hD i p
    (OrdinaryFrame.run (SourceFrameActions.compileRules L) (n*batchSize counts J m) R 0
      (observerInitial e hD i initial draws a.1,(⊥,∅)) a.2).1.1.2 =
      run counts J A evaluate (columns hD p.2) (initial p.1) (draws p.1) n := by
  have h := compiled_batch_frame_run_actual counts J D m i A evaluate he queries hq output ho n R hR
    (otherColumns e hD i (fun l => p.2 (e.symm ((e i).succAbove l)))) (columns hD p.2)
    (otherColumns_agree e hD i p.2) (initial p.1) (draws p.1) ⊥ ∅
  exact congrArg (fun x => x.1.2) h

end Bilevel.ChiHierarchyExecution
