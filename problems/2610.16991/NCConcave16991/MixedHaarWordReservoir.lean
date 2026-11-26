import NCConcave16991.MixedHaarGaussianSlices
import NCConcave16991.MixedHaarReservoirProjection
import NCConcave16991.BranchOracleSupport

/-! # One common actual Gaussian reservoir for every slot and word depth -/

noncomputable section

open Set MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace NCConcave16991.MixedHaar

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

abbrev WordSliceIndex (n H N : ℕ) :=
  Sigma (fun a : Fin N × Fin (H + 1) ↦ BranchOracle.Word (Fin n) a.2.val)

def wordSliceCount (n H N : ℕ) : ℕ := Fintype.card (WordSliceIndex n H N)

abbrev WordReservoir (n H N D : ℕ) :=
  ∀ a : Fin N × Fin (H + 1), BranchOracle.FormalLayer (ι := Fin n) (Space D) a.2.val

def wordReservoirLaw (n H N D : ℕ) : Measure (WordReservoir n H N D) :=
  Measure.pi (fun a ↦ stdGaussian (BranchOracle.FormalLayer (ι := Fin n) (Space D) a.2.val))

instance wordReservoirLaw_probability (n H N D : ℕ) : IsProbabilityMeasure (wordReservoirLaw n H N D) := by
  unfold wordReservoirLaw
  infer_instance

def wordReservoirFlatten {n H N D : ℕ} (f : WordReservoir n H N D) :
    Reservoir (wordSliceCount n H N) D :=
  fun a ↦ let ij := (Fintype.equivFin (WordSliceIndex n H N)).symm a
    f ij.1 ij.2

theorem wordReservoirFlatten_preserving (n H N D : ℕ) :
    MeasurePreserving (wordReservoirFlatten (n := n) (H := H) (N := N) (D := D))
      (wordReservoirLaw n H N D) (gaussianReservoirLaw (wordSliceCount n H N) D) :=
  gaussian_family_enumerated_preserving (Fintype.equivFin (WordSliceIndex n H N))

def wordReservoirSpan {n H N D : ℕ} (f : WordReservoir n H N D) : Submodule ℝ (Space D) :=
  Submodule.span ℝ (range (fun ij : WordSliceIndex n H N ↦ f ij.1 ij.2))

theorem wordReservoirSpan_eq {n H N D : ℕ} (f : WordReservoir n H N D) :
    wordReservoirSpan f = reservoirSpan (wordReservoirFlatten f) := by
  unfold wordReservoirSpan reservoirSpan
  congr 1
  ext x
  constructor
  · rintro ⟨ij,rfl⟩
    refine ⟨(Fintype.equivFin (WordSliceIndex n H N)) ij,?_⟩
    exact congrArg (fun x : WordSliceIndex n H N ↦ f x.1 x.2)
      ((Fintype.equivFin (WordSliceIndex n H N)).symm_apply_apply ij)
  · rintro ⟨a,rfl⟩
    exact ⟨(Fintype.equivFin (WordSliceIndex n H N)).symm a,rfl⟩

theorem word_slice_mem_reservoir {n H N D : ℕ} (f : WordReservoir n H N D)
    (a : Fin N × Fin (H + 1)) (w : BranchOracle.Word (Fin n) a.2.val) :
    f a w ∈ wordReservoirSpan f := Submodule.subset_span ⟨⟨a,w⟩,rfl⟩

theorem word_draw_mem_support {n H N D : ℕ} [NeZero n] (f : WordReservoir n H N D)
    (a : Fin N × Fin (H + 1)) (S : Finset (BranchOracle.Word (Fin n) a.2.val)) :
    f a ∈ BranchOracle.wordSupport a.2.val S (wordReservoirSpan f) := by
  intro w _
  exact word_slice_mem_reservoir f a w

theorem word_projection_score_eq {n H N D : ℕ} (f : WordReservoir n H N D) (i : Fin D) :
    ‖(wordReservoirSpan f).orthogonalProjectionOnto (Haar.basisVector i)‖ ^ 2 =
      coordinateScore (wordReservoirFlatten f) i := by
  rw [wordReservoirSpan_eq,coordinateScore_eq_projection_norm_sq]

theorem word_reservoir_projection_tail {n H N D : ℕ} (hD : 0 < D) (i : Fin D)
    {a : ℝ} (ha : 0 < a) :
    (wordReservoirLaw n H N D).real {f |
      a ≤ ‖(wordReservoirSpan f).orthogonalProjectionOnto (Haar.basisVector i)‖ ^ 2} ≤
        (wordSliceCount n H N : ℝ) / ((D : ℝ) * a) := by
  have hp := wordReservoirFlatten_preserving n H N D
  have hs : MeasurableSet {r : Reservoir (wordSliceCount n H N) D | a ≤ coordinateScore r i} :=
    measurableSet_le measurable_const (coordinateScore_measurable i)
  have he : (wordReservoirLaw n H N D).real {f | a ≤ coordinateScore (wordReservoirFlatten f) i} =
      (gaussianReservoirLaw (wordSliceCount n H N) D).real {r | a ≤ coordinateScore r i} := by
    unfold Measure.real
    rw [← hp.map_eq,Measure.map_apply hp.measurable hs]
    rfl
  simp_rw [word_projection_score_eq]
  rw [he]
  exact coordinateScore_tail hD i ha

end NCConcave16991.MixedHaar
