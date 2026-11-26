import Bilevel.ChiSelectedFrameRun
import Bilevel.SourceFrameBatchActions

/-! A conservative selected-frame query batch. All complementary full-frame
columns are independent context and may be inserted by the stronger genie.
The selected frame itself occurs only through the named-column action.
These frame-specific enlarged spaces must not be identified with one
another or with the source's shared known space. -/
noncomputable section
open MeasureTheory
universe u
namespace Bilevel.ChiHierarchyExecution
open ChiHierarchyIndex BorelAdaptive EuclideanGaussian TransportControllerMachine

abbrev ColumnIndex (counts : ℕ → ℕ) (J : ℕ) :=
  Σ i : FrameIndex counts J, Fin (chainSize i+1)

abbrev BatchIndex (counts : ℕ → ℕ) (J m : ℕ) := Fin m ⊕ ColumnIndex counts J

def batchSize (counts : ℕ → ℕ) (J m : ℕ) : ℕ := Fintype.card (BatchIndex counts J m)

def batchEnumeration (counts : ℕ → ℕ) (J m : ℕ) :
    BatchIndex counts J m ≃ Fin (batchSize counts J m) := Fintype.equivFin _

theorem batchSize_pos (counts : ℕ → ℕ) (J m : ℕ) : 0 < batchSize counts J m := by
  let i : FrameIndex counts J := Sum.inl ()
  letI : Nonempty (BatchIndex counts J m) := ⟨Sum.inr ⟨i,⟨0,Nat.zero_lt_succ _⟩⟩⟩
  exact Fintype.card_pos

variable {S : Type u} {Q O Y : Type*} [MeasurableSpace S] [MeasurableSpace Q]
  [MeasurableSpace O] [MeasurableSpace Y]

def batchVector (counts : ℕ → ℕ) (J D m : ℕ) (selected : FrameIndex counts J)
    (A : Program S Q O Y) (queries : Fin m → Q × Store counts J (Space D) → Space D)
    (h : FrameMemory counts J D S) : BatchIndex counts J m → Space D
  | Sum.inl k => queries k (A.query h.2.1,h.2.2)
  | Sum.inr p => if p.1=selected then 0 else h.1.1 p.1 p.2

theorem batchVector_measurable (counts : ℕ → ℕ) (J D m : ℕ) (selected : FrameIndex counts J)
    (A : Program S Q O Y) (queries : Fin m → Q × Store counts J (Space D) → Space D)
    (hq : ∀ k, Measurable (queries k)) (k : BatchIndex counts J m) :
    Measurable (fun h => batchVector counts J D m selected A queries h k) := by
  cases k with
  | inl k =>
    exact (hq k).comp
      ((A.query_measurable.comp (measurable_fst.comp measurable_snd)).prodMk
        (measurable_snd.comp measurable_snd))
  | inr p =>
      by_cases hi : p.1=selected
      · simp only [batchVector,if_pos hi]; exact measurable_const
      · simp only [batchVector,if_neg hi]
        exact (measurable_pi_apply p.2).comp ((measurable_pi_apply p.1).comp
          (measurable_fst.comp measurable_fst))

def frozenQueries (counts : ℕ → ℕ) (J D m : ℕ) (selected : FrameIndex counts J)
    (A : Program S Q O Y) (queries : Fin m → Q × Store counts J (Space D) → Space D)
    (_t : ℕ) (h : FrameMemory counts J D S) (k : Fin (batchSize counts J m)) : Space D :=
  batchVector counts J D m selected A queries h ((batchEnumeration counts J m).symm k)

theorem frozenQueries_measurable (counts : ℕ → ℕ) (J D m : ℕ) (selected : FrameIndex counts J)
    (A : Program S Q O Y) (queries : Fin m → Q × Store counts J (Space D) → Space D)
    (hq : ∀ k, Measurable (queries k)) (t : ℕ) (k : Fin (batchSize counts J m)) :
    Measurable (fun h => frozenQueries counts J D m selected A queries t h k) :=
  batchVector_measurable counts J D m selected A queries hq _

theorem query_in_batch (counts : ℕ → ℕ) (J D m : ℕ) (selected : FrameIndex counts J)
    (A : Program S Q O Y) (queries : Fin m → Q × Store counts J (Space D) → Space D)
    (t : ℕ) (h : FrameMemory counts J D S) (k : Fin m) :
    ∃ l, frozenQueries counts J D m selected A queries t h l = queries k (A.query h.2.1,h.2.2) := by
  refine ⟨batchEnumeration counts J m (Sum.inl k),?_⟩
  simp only [frozenQueries,Equiv.symm_apply_apply,batchVector]

theorem other_column_in_batch (counts : ℕ → ℕ) (J D m : ℕ) (selected : FrameIndex counts J)
    (A : Program S Q O Y) (queries : Fin m → Q × Store counts J (Space D) → Space D)
    (t : ℕ) (h : FrameMemory counts J D S) (i : FrameIndex counts J) (hi : i≠selected)
    (k : Fin (chainSize i+1)) :
    ∃ l, frozenQueries counts J D m selected A queries t h l = h.1.1 i k := by
  refine ⟨batchEnumeration counts J m (Sum.inr ⟨i,k⟩),?_⟩
  simp only [frozenQueries,Equiv.symm_apply_apply,batchVector,if_neg hi]

end Bilevel.ChiHierarchyExecution
