import SampleReuse.TreeProgram
import SampleReuse.TreeExecutionAccuracy

/-! The actual compiled run time equals the literal source root-plus-edges
query cost. In particular ceilings are charged once for the root and twice
per sampled same-handle edge, with no virtual unused-node costs. -/

open SecondOrder
open scoped BigOperators Classical

namespace SampleReuse
noncomputable section

variable {Ω E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {d M B : ℕ}
    (hB : 0 < B) (scale σ L : ℝ) (sample : Ω → Point d → E)
    (loc : ℕ → TreeCache d E → Point d) (tape : SampleTape ((M + 1) * B) Ω)

theorem sourceTreeCallTime_eq_sum (m k : ℕ) :
    sourceTreeCallTime hB scale σ L sample loc tape m k (treeCacheRun hB scale σ L sample loc tape k) =
      ∑ j ∈ Finset.range m, treePacketCalls (B := B) scale σ L loc (k + j)
        (treeCacheRun hB scale σ L sample loc tape (k + j)) := by
  induction m generalizing k with
  | zero => simp only [sourceTreeCallTime, Finset.range_zero, Finset.sum_empty]
  | succ m ih =>
    change treePacketCalls (B := B) scale σ L loc k (treeCacheRun hB scale σ L sample loc tape k) +
      sourceTreeCallTime hB scale σ L sample loc tape m (k + 1)
        (treeCacheRun hB scale σ L sample loc tape (k + 1)) = _
    rw [ih, Finset.sum_range_succ']
    simp only [Nat.add_zero]
    rw [Nat.add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    exact congrArg (fun q => treePacketCalls (B := B) scale σ L loc q
      (treeCacheRun hB scale σ L sample loc tape q)) (by omega : k + 1 + j = k + (j + 1))

theorem treePacketCalls_on_execution {k : ℕ} (hk : 0 < k) :
    treePacketCalls (B := B) scale σ L loc k (treeCacheRun hB scale σ L sample loc tape k) =
      2 * chordBatchSize scale σ L (treeGeneratedLocation hB scale σ L sample loc k tape)
        (treeGeneratedLocation hB scale σ L sample loc (ancestorParent k) tape) := by
  simp only [treePacketCalls, treeChosenBatch, if_neg hk.ne']
  rw [treeCacheRun_location_entry hB scale σ L sample loc tape (ancestorParent_lt hk)]
  rfl

theorem sourceTreeCallTime_eq_treeSamplerCost (hcap : B = batchSize scale (σ^2)) :
    sourceTreeCallTime hB scale σ L sample loc tape (M + 1) 0 (fun _ => (0, 0)) =
      treeSamplerCost scale σ L (treeGeneratedLocation hB scale σ L sample loc) tape := by
  change sourceTreeCallTime hB scale σ L sample loc tape (M + 1) 0
    (treeCacheRun hB scale σ L sample loc tape 0) = _
  rw [sourceTreeCallTime_eq_sum]
  simp only [Nat.zero_add]
  rw [← Finset.add_sum_erase (Finset.range (M + 1))
    (fun k => treePacketCalls (B := B) scale σ L loc k (treeCacheRun hB scale σ L sample loc tape k))
    (show 0 ∈ Finset.range (M + 1) by simp)]
  have hset : (Finset.range (M + 1)).erase 0 = Finset.Icc 1 M := by
    ext k
    simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_Icc]
    omega
  rw [hset]
  change B + (∑ k ∈ Finset.Icc 1 M,
    treePacketCalls (B := B) scale σ L loc k (treeCacheRun hB scale σ L sample loc tape k)) = _
  conv_lhs =>
    lhs
    rw [hcap]
  unfold treeSamplerCost
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  exact treePacketCalls_on_execution hB scale σ L sample loc tape (by
    have hp := (Finset.mem_Icc.mp hk).1
    omega)

end
end SampleReuse
