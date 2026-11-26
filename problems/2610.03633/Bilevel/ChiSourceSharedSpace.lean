import Bilevel.ChiSelectedFrameBatch
import Bilevel.ChiSelectedFrameNamed
import Bilevel.SourceFrameBatchPreEnergy
import Bilevel.SourceFrameKnownSpace

/-! Explicit inclusion of the source's shared known space in each selected
frame's enlarged observation space. All other frames may be fully exposed
only in that selected frame's independent context. -/
noncomputable section
open MeasureTheory
universe u
namespace Bilevel.ChiHierarchyExecution
open ChiHierarchyIndex BorelAdaptive EuclideanGaussian ProjectionPosterior ProjectionGeometry

def sharedKnown (counts : ℕ → ℕ) (J D q : ℕ) (U : FiniteColumns counts J (Space D))
    (V : Submodule ℝ (Space D)) : Submodule ℝ (Space D) :=
  V ⊔ Submodule.span ℝ {v | ∃ i k, k.val<retained counts J q i ∧ v=U i k}

theorem sharedKnown_le (counts : ℕ → ℕ) (J D q : ℕ) (U : FiniteColumns counts J (Space D))
    (i : FrameIndex counts J) (V W : Submodule ℝ (Space D)) (hV : V≤W)
    (hself : ∀ k, k.val<retained counts J q i → U i k∈W)
    (hother : ∀ j, j≠i → ∀ k, U j k∈W) : sharedKnown counts J D q U V≤W := by
  refine sup_le hV (Submodule.span_le.mpr ?_)
  rintro _ ⟨j,k,hk,rfl⟩
  by_cases hj : j=i
  · subst j; exact hself k hk
  · exact hother j hj k

variable {S : Type u} {Q O Y : Type*} [MeasurableSpace S] [MeasurableSpace Q]
  [MeasurableSpace O] [MeasurableSpace Y]

theorem batch_sharedKnown_le (counts : ℕ → ℕ) (J D m : ℕ) (i : FrameIndex counts J)
    (A : Program S Q O Y) (queries : Fin m → Q × Store counts J (Space D) → Space D)
    (hq : ∀ k, Measurable (queries k))
    (L : SourceFrameActions.Rules (FrameMemory counts J D S) D (chainSize i+1))
    (t q : ℕ) (s : SourceFrameActions.State (FrameMemory counts J D S) D (chainSize i+1))
    (U : FiniteColumns counts J (Space D)) (hC : ∀ j, j≠i → s.1.1.1 j=U j)
    (hK : s.2.2=prefixSet (retained counts J q i)) (hknown : SourceFrameActions.KnownInSpace s (U i))
    (V : Submodule ℝ (Space D)) (hV : V≤s.2.1) :
    sharedKnown counts J D q U (V ⊔ Submodule.span ℝ
      (Set.range (fun k => queries k (A.query s.1.2.1,s.1.2.2)))) ≤
      SourceFrameActions.batchPreSpace L (batchSize_pos counts J m)
        (frozenQueries counts J D m i A queries) (frozenQueries_measurable counts J D m i A queries hq)
        t s (U i) := by
  let W := SourceFrameActions.batchPreSpace L (batchSize_pos counts J m)
    (frozenQueries counts J D m i A queries) (frozenQueries_measurable counts J D m i A queries hq) t s (U i)
  have hmono : s.2.1≤W := SourceFrameActions.batch_pre_mono _ _ _ _ _ _ _
  have hbatch : ∀ k, frozenQueries counts J D m i A queries t s.1 k∈W :=
    SourceFrameActions.batch_pre_query_mem _ _ _ _ _ _ _
  apply sharedKnown_le counts J D q U i _ W
  · refine sup_le (hV.trans hmono) (Submodule.span_le.mpr ?_)
    rintro _ ⟨k,rfl⟩
    obtain ⟨l,hl⟩ := query_in_batch counts J D m i A queries t s.1 k
    change queries k (A.query s.1.2.1,s.1.2.2)∈W
    rw [←hl]
    exact hbatch l
  · intro k hk
    apply hmono
    apply hknown k
    rw [hK]
    exact hk
  · intro j hj k
    obtain ⟨l,hl⟩ := other_column_in_batch counts J D m i A queries t s.1 j hj k
    rw [hC j hj] at hl
    rw [←hl]
    exact hbatch l

end Bilevel.ChiHierarchyExecution
