import SampleReuse.CurvatureFirstExecution

open SecondOrder
open scoped Classical

namespace SampleReuse
noncomputable section

theorem checkpointValue_packet_zero {Ω E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H d B : ℕ} (hB : 0 < B) (scale σ L : ℝ) (sample : Ω → Point d → E)
    (reserve : ℕ → Fin B → Fin H) (cache : TreeCache d E) (x : Point d) (tape : SampleTape H Ω) :
    checkpointValue 0 cache (checkpointPacket hB scale σ L sample reserve 0 cache x tape) =
      batchMeanTape (fun z => sample z x) (reserve 0) tape := rfl

theorem checkpointValue_packet_parent {Ω E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H d B : ℕ} (hB : 0 < B) (scale σ L : ℝ) (sample : Ω → Point d → E)
    (reserve : ℕ → Fin B → Fin H) {k : ℕ} (hk : 0 < k) (cache : TreeCache d E)
    (x y : Point d) (e : E) (tape : SampleTape H Ω) (hp : cache (ancestorParent k) = (y,e)) :
    checkpointValue k cache (checkpointPacket hB scale σ L sample reserve k cache x tape) =
      e + batchMeanTape (fun z => sample z x-sample z y)
        (fun i : Fin (chordBatchSize scale σ L x y) =>
          reserve k (prefixHandles hB (chordBatchSize scale σ L x y) i)) tape := by
  have hn : checkpointBatchSize (B := B) scale σ L k cache x = chordBatchSize scale σ L x y := by
    simp only [checkpointBatchSize,if_neg hk.ne',hp]
  unfold checkpointValue checkpointPacket
  rw [if_neg hk.ne',if_neg hk.ne',hn,hp]

end
end SampleReuse
