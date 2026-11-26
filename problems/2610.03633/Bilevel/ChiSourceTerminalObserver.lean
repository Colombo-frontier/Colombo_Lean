import Bilevel.ChiSourceCallObserver
import Bilevel.OrdinaryFrameOutput

/-! Arbitrary terminal output of the same actual source run. Its direction
is inserted after the output is fixed; no earlier query-span premise occurs. -/
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
universe u
namespace Bilevel.ChiHierarchyExecution
open ChiHierarchyIndex BorelAdaptive EuclideanGaussian ProjectionPosterior SourceFrameActions

variable {S : Type u} {Q O Y : Type*} [MeasurableSpace S] [MeasurableSpace Q]
  [MeasurableSpace O] [MeasurableSpace Y]
variable (counts : ℕ → ℕ) (J D m : ℕ) (i : FrameIndex counts J) (A : Program S Q O Y)
  (evaluate : Q → Store counts J (Space D) → Store counts J (Space D) → Bool → O)
  (he : Measurable (fun p : Q × (Store counts J (Space D) × (Store counts J (Space D) × Bool)) =>
    evaluate p.1 p.2.1 p.2.2.1 p.2.2.2))
  (queries : Fin m → Q × Store counts J (Space D) → Space D) (hq : ∀ k, Measurable (queries k))
  (output : Y → Space D) (ho : Measurable output)

theorem actual_terminal_bound (C U : FiniteColumns counts J (Space D))
    (hC : ∀ j, j≠i → C j=U j) (s : S) (draws : ℕ → Bool) (N R : ℕ)
    (hR : N*batchSize counts J m≤R) (cap : ℝ) (hcap : 0≤cap)
    (hgood : OrdinaryFrame.Observed
      (compileRules (batchedFrameRules counts J D m i A evaluate he queries hq output ho)) cap
      (N*batchSize counts J m) R 0 ((((C,draws),initialState counts J s),false),(⊥,∅)) (U i))
    (k : Fin (chainSize i+1)) (hk : retained counts J (run counts J A evaluate U s draws N).2.1 i≤k.val) :
    |⟪U i k,output (A.output (run counts J A evaluate U s draws N).1)⟫|≤
      Real.sqrt cap*‖output (A.output (run counts J A evaluate U s draws N).1)‖ := by
  let L := compileRules (batchedFrameRules counts J D m i A evaluate he queries hq output ho)
  let start : OrdinaryFrame.State (Marked (FrameMemory counts J D S)) D (chainSize i+1) :=
    ((((C,draws),initialState counts J s),false),(⊥,∅))
  let z := OrdinaryFrame.run L (N*batchSize counts J m) R 0 start (U i)
  have hmem : z.1=(((C,draws),run counts J A evaluate U s draws N),false) :=
    compiled_batch_frame_run_actual counts J D m i A evaluate he queries hq output ho N R hR C U hC s draws ⊥ ∅
  have hstart : (∅ : Set (Fin (chainSize i+1)))=prefixSet (retained counts J 0 i) := by
    simp [prefixSet,retained_zero]
  have hnamed : z.2.2=prefixSet (retained counts J z.1.1.2.2.1 i) :=
    compiled_batched_named counts J D m i A evaluate he queries hq output ho N R hR
      (((C,draws),initialState counts J s),(⊥,∅)) (U i) hstart
  have hnot : k∉z.2.2 := by
    rw [hnamed,hmem]
    change ¬k.val<retained counts J (run counts J A evaluate U s draws N).2.1 i
    omega
  have hE := OrdinaryFrame.observed_final L cap (N*batchSize counts J m) R 0 start (U i) hgood
  have hbound := OrdinaryFrame.boundedEnergy_inner z.2.1 z.2.2 (U i) cap hcap hE (L.output z.1)
    (OrdinaryFrame.run_output_mem L (N*batchSize counts J m) R 0 start (U i)) k hnot
  have hout : L.output z.1=output (A.output (run counts J A evaluate U s draws N).1) := by
    change output (A.output z.1.1.2.1)=_
    rw [hmem]
  simpa only [hout] using hbound

end Bilevel.ChiHierarchyExecution
