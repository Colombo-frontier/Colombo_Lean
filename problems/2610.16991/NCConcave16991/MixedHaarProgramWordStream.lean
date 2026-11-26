import NCConcave16991.MixedHaarProgramStream
import NCConcave16991.MixedHaarTapeWordReservoir

/-! # Every actual stream draw lies in the one common word reservoir -/

noncomputable section

namespace NCConcave16991.MixedHaar

variable {Z : Type} {n H N D : ℕ}

theorem stream_draw_coordinate_mem_reservoir
    (p : RevealTape (GaussianVertexBlock n H D) Z N) (g : GaussianVertexBlock n H D)
    (hg : g ∈ tapeFreshList N p) (d : Fin (H + 1)) (w : BranchOracle.Word (Fin n) d.val) :
    g d w ∈ wordReservoirSpan (pureTapeWordReservoir p) := by
  obtain ⟨i,hi⟩ := (mem_tapeFreshList_iff N p g).mp hg
  rw [← hi]
  exact word_slice_mem_reservoir (pureTapeWordReservoir p) (i,d) w

theorem stream_draw_mem_wordSupport [NeZero n]
    (p : RevealTape (GaussianVertexBlock n H D) Z N) (g : GaussianVertexBlock n H D)
    (hg : g ∈ tapeFreshList N p) (d : Fin (H + 1))
    (S : Finset (BranchOracle.Word (Fin n) d.val)) :
    g d ∈ BranchOracle.wordSupport d.val S (wordReservoirSpan (pureTapeWordReservoir p)) := by
  intro w _
  exact stream_draw_coordinate_mem_reservoir p g hg d w

end NCConcave16991.MixedHaar
