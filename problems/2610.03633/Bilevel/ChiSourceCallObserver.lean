import Bilevel.ChiSourceSharedSpace
import Bilevel.ChiSelectedFrameBatchNamed

/-! Same-run energy of the fresh analytic known space at every original
source call. The fresh space contains current query vectors and retained
columns; the selected-frame genie keeps a larger cumulative space. -/
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

def callObservation (C U : FiniteColumns counts J (Space D)) (s : S) (draws : ℕ → Bool) (n : ℕ) :=
  observeRun (batchedFrameRules counts J D m i A evaluate he queries hq output ho)
    (n*batchSize counts J m) 0
    (((C,draws),initialState counts J s),(⊥,∅)) (U i)

theorem callObservation_memory (C U : FiniteColumns counts J (Space D))
    (hC : ∀ j, j≠i → C j=U j) (s : S) (draws : ℕ → Bool) (n : ℕ) :
    (callObservation counts J D m i A evaluate he queries hq output ho C U s draws n).1 =
      ((C,draws),run counts J A evaluate U s draws n) := by
  unfold callObservation batchedFrameRules
  rw [observeRun_memory]
  have h := batch_run_blocks
    (frameRules counts J D i A evaluate he (fun _ => 0) (fun _ => 0) measurable_const measurable_const output ho)
    (batchSize_pos counts J m) (frozenQueries counts J D m i A queries)
    (frozenQueries_measurable counts J D m i A queries hq) n 0
    ((C,draws),initialState counts J s) (U i)
  simp only [Nat.zero_mul] at h
  rw [h,frame_run_actual counts J D i A evaluate he (fun _ => 0) (fun _ => 0)
    measurable_const measurable_const output ho n 0 _ U hC]
  simp only [Nat.zero_add,run]

theorem callObservation_named (C U : FiniteColumns counts J (Space D))
    (s : S) (draws : ℕ → Bool) (n : ℕ) :
    let z := callObservation counts J D m i A evaluate he queries hq output ho C U s draws n
    z.2.2=prefixSet (retained counts J z.1.2.2.1 i) := by
  have hk : (∅ : Set (Fin (chainSize i+1)))=prefixSet (retained counts J 0 i) := by
    simp [retained_zero,prefixSet]
  simpa only [Nat.zero_mul,callObservation] using batched_named_run counts J D m i A evaluate he queries hq output ho
    n 0 (((C,draws),initialState counts J s),(⊥,∅)) (U i) hk

theorem callObservation_known (C U : FiniteColumns counts J (Space D))
    (s : S) (draws : ℕ → Bool) (n : ℕ) :
    KnownInSpace (callObservation counts J D m i A evaluate he queries hq output ho C U s draws n) (U i) :=
  known_observeRun _ _ _ _ _ (known_initial _ _)

theorem call_shared_energy (C U : FiniteColumns counts J (Space D))
    (hC : ∀ j, j≠i → C j=U j) (s : S) (draws : ℕ → Bool) (N t : ℕ) (ht : t<N) (cap : ℝ)
    (hgood : SourceObserved (batchedFrameRules counts J D m i A evaluate he queries hq output ho) cap
      (N*batchSize counts J m) 0 (((C,draws),initialState counts J s),(⊥,∅)) (U i)) :
    let z := run counts J A evaluate U s draws t
    GenieProtocol.BoundedEnergy
      (sharedKnown counts J D z.2.1 U (Submodule.span ℝ (Set.range (fun k => queries k (A.query z.1,z.2)))))
      (prefixSet (retained counts J z.2.1 i)) (U i) cap := by
  let a := callObservation counts J D m i A evaluate he queries hq output ho C U s draws t
  have hmem : a.1=((C,draws),run counts J A evaluate U s draws t) :=
    callObservation_memory counts J D m i A evaluate he queries hq output ho C U hC s draws t
  have hcontext : ∀ j, j≠i → a.1.1.1 j=U j := by
    intro j hj
    rw [hmem]
    exact hC j hj
  have hnamed : a.2.2=prefixSet (retained counts J a.1.2.2.1 i) :=
    callObservation_named counts J D m i A evaluate he queries hq output ho C U s draws t
  let L := frameRules counts J D i A evaluate he (fun _ => 0) (fun _ => 0)
    measurable_const measurable_const output ho
  have hE := batch_pre_energy_at_call L (batchSize_pos counts J m)
    (frozenQueries counts J D m i A queries) (frozenQueries_measurable counts J D m i A queries hq)
    N t ht (((C,draws),initialState counts J s),(⊥,∅)) (U i) cap hgood
  have hle := batch_sharedKnown_le counts J D m i A queries hq L t a.1.2.2.1 a U hcontext hnamed
    (callObservation_known counts J D m i A evaluate he queries hq output ho C U s draws t) ⊥ bot_le
  simp only [bot_sup_eq] at hle
  have hbound := boundedEnergy_subspace hle a.2.2 (U i) cap hE
  rw [hnamed] at hbound
  simpa only [hmem] using hbound

end Bilevel.ChiHierarchyExecution
