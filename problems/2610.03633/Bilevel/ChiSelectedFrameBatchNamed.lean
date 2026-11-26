import Bilevel.ChiSelectedFrameNamed
import Bilevel.ChiSelectedFrameBatchRun

/-! Exact named prefixes at every completed batch and terminal output,
for the same live-success store used by the original source execution. -/
noncomputable section
open MeasureTheory
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

theorem batched_named_run (n t : ℕ)
    (s : State (FrameMemory counts J D S) D (chainSize i+1)) (U : Frame D (chainSize i+1))
    (hK : s.2.2=prefixSet (retained counts J s.1.2.2.1 i)) :
    let z := observeRun (batchedFrameRules counts J D m i A evaluate he queries hq output ho)
      (n*batchSize counts J m) (t*batchSize counts J m) s U
    z.2.2=prefixSet (retained counts J z.1.2.2.1 i) := by
  let L := frameRules counts J D i A evaluate he (fun _ => 0) (fun _ => 0)
    measurable_const measurable_const output ho
  have hbase := frame_named_run counts J D i A evaluate he (fun _ => 0) (fun _ => 0)
    measurable_const measurable_const output ho n t s U hK
  have hshadow := batch_shadow_blocks L (batchSize_pos counts J m)
    (frozenQueries counts J D m i A queries) (frozenQueries_measurable counts J D m i A queries hq) n t s U
  let P : FrameMemory counts J D S × Set (Fin (chainSize i+1)) → Prop :=
    fun p => p.2=prefixSet (retained counts J p.1.2.2.1 i)
  have hb : P (shadow (observeRun L n t s U)) := hbase
  exact Eq.mp (congrArg P hshadow.symm) hb

theorem compiled_batched_named (n R : ℕ) (hR : n*batchSize counts J m≤R)
    (s : State (FrameMemory counts J D S) D (chainSize i+1)) (U : Frame D (chainSize i+1))
    (hK : s.2.2=prefixSet (retained counts J s.1.2.2.1 i)) :
    let z := OrdinaryFrame.run (compileRules (batchedFrameRules counts J D m i A evaluate he queries hq output ho))
      (n*batchSize counts J m) R 0 ((s.1,false),s.2) U
    z.2.2=prefixSet (retained counts J z.1.1.2.2.1 i) := by
  dsimp only
  rw [compiled_run_observation _ _ _ _ _ _ hR]
  simpa only [Nat.zero_mul,finishObservation] using
    batched_named_run counts J D m i A evaluate he queries hq output ho n 0 s U hK

end Bilevel.ChiHierarchyExecution
