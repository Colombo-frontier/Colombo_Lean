import SampleReuse.TreePacketProgram

/-! Sequential compilation of the full finite tree cache. A continuation
sees only the preceding packet's numerical value. Actual run time is the
sum of the literal root/edge batch call counts along that execution. -/

open MeasureTheory ProbabilityTheory SecondOrder
open scoped BigOperators Classical

namespace SampleReuse
noncomputable section

def cacheAfterPacket {E : Type*} [Add E] {d : ℕ}
    (loc : ℕ → TreeCache d E → Point d) (k : ℕ) (cache : TreeCache d E) (packet : E) : TreeCache d E :=
  Function.update cache k (loc k cache, if k = 0 then packet else (cache (ancestorParent k)).2 + packet)

def sourceTreeProgram {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {d M B : ℕ}
    (hB : 0 < B) (scale σ L : ℝ) (flag : Bool) (project : PersistentReply d → E)
    (loc : ℕ → TreeCache d E → Point d) :
    ℕ → ℕ → TreeCache d E → OracleProgram (PersistentQuery ((M + 1) * B) d) (PersistentReply d) (TreeCache d E)
  | 0, _, cache => .done cache
  | m + 1, k, cache => OracleProgram.bind (treePacketProgram hB scale σ L flag project loc k cache)
      (fun packet => sourceTreeProgram hB scale σ L flag project loc m (k + 1) (cacheAfterPacket loc k cache packet))

def sourceTreeExecuteFrom {Ω E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {d M B : ℕ}
    (hB : 0 < B) (scale σ L : ℝ) (sample : Ω → Point d → E)
    (loc : ℕ → TreeCache d E → Point d) (tape : SampleTape ((M + 1) * B) Ω) :
    ℕ → ℕ → TreeCache d E → TreeCache d E
  | 0, _, cache => cache
  | m + 1, k, cache => sourceTreeExecuteFrom hB scale σ L sample loc tape m (k + 1)
      (treeCacheStep hB scale σ L sample loc k cache tape)

def sourceTreeCallTime {Ω E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {d M B : ℕ}
    (hB : 0 < B) (scale σ L : ℝ) (sample : Ω → Point d → E)
    (loc : ℕ → TreeCache d E → Point d) (tape : SampleTape ((M + 1) * B) Ω) :
    ℕ → ℕ → TreeCache d E → ℕ
  | 0, _, _ => 0
  | m + 1, k, cache => treePacketCalls (B := B) scale σ L loc k cache +
      sourceTreeCallTime hB scale σ L sample loc tape m (k + 1)
        (treeCacheStep hB scale σ L sample loc k cache tape)

theorem sourceTreeProgram_run {Ω E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {d M B : ℕ} (hB : 0 < B) (scale σ L : ℝ)
    (q₀ : PersistentQuery ((M + 1) * B) d) (F : Ω → Point d → ℝ) (sample : Ω → Point d → E)
    (flag : Bool) (project : PersistentReply d → E)
    (hfield : ∀ (tape : SampleTape ((M + 1) * B) Ω) (r : Fin ((M + 1) * B)) (x : Point d),
      project (persistentReply F tape (flag, r, x)) = sample (tape r) x)
    (loc : ℕ → TreeCache d E → Point d) (tape : SampleTape ((M + 1) * B) Ω)
    (m k : ℕ) (cache : TreeCache d E) :
    OracleProgram.run q₀ (fun q tape => persistentReply F tape q) (fun _ => tape)
      (sourceTreeProgram hB scale σ L flag project loc m k cache)
      (sourceTreeCallTime hB scale σ L sample loc tape m k cache) =
        .done (sourceTreeExecuteFrom hB scale σ L sample loc tape m k cache) := by
  induction m generalizing k cache with
  | zero => rfl
  | succ m ih =>
    rw [sourceTreeProgram, sourceTreeCallTime,
      OracleProgram.run_bind_of_exact q₀ (fun q tape => persistentReply F tape q) (fun _ => tape)
        (treePacketProgram_exact hB scale σ L flag project loc k cache) _
        (treePacketProgram_run hB scale σ L q₀ F sample flag project hfield loc k cache tape)]
    exact ih (k + 1) (treeCacheStep hB scale σ L sample loc k cache tape)

theorem sourceTreeExecuteFrom_eq_cacheRun {Ω E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {d M B : ℕ} (hB : 0 < B) (scale σ L : ℝ) (sample : Ω → Point d → E)
    (loc : ℕ → TreeCache d E → Point d) (tape : SampleTape ((M + 1) * B) Ω) (m k : ℕ) :
    sourceTreeExecuteFrom hB scale σ L sample loc tape m k (treeCacheRun hB scale σ L sample loc tape k) =
      treeCacheRun hB scale σ L sample loc tape (k + m) := by
  induction m generalizing k with
  | zero => rfl
  | succ m ih =>
    change sourceTreeExecuteFrom hB scale σ L sample loc tape m (k + 1)
      (treeCacheRun hB scale σ L sample loc tape (k + 1)) = _
    rw [ih]
    exact congrArg (treeCacheRun hB scale σ L sample loc tape) (by omega : k + 1 + m = k + (m + 1))

theorem sourceTreeProgram_compiled_output {Ω E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {d M B : ℕ} (hB : 0 < B) (scale σ L : ℝ)
    (q₀ : PersistentQuery ((M + 1) * B) d) (F : Ω → Point d → ℝ) (sample : Ω → Point d → E)
    (flag : Bool) (project : PersistentReply d → E)
    (hfield : ∀ (tape : SampleTape ((M + 1) * B) Ω) (r : Fin ((M + 1) * B)) (x : Point d),
      project (persistentReply F tape (flag, r, x)) = sample (tape r) x)
    (loc : ℕ → TreeCache d E → Point d) (tape : SampleTape ((M + 1) * B) Ω) :
    let cache₀ : TreeCache d E := fun _ => (0, 0)
    let alg := OracleProgram.algorithm q₀ (0, 0) cache₀
      (sourceTreeProgram hB scale σ L flag project loc (M + 1) 0 cache₀)
    let N := sourceTreeCallTime hB scale σ L sample loc tape (M + 1) 0 cache₀
    alg.output N (persistentRun alg.toQueryPolicy F tape N) = treeCacheRun hB scale σ L sample loc tape (M + 1) := by
  dsimp only
  rw [persistentRun_eq_queryPolicyRun]
  change oracleAlgorithmOutput _ _ _ _ = _
  rw [OracleProgram.algorithm_output, sourceTreeProgram_run hB scale σ L q₀ F sample flag project hfield]
  change sourceTreeExecuteFrom hB scale σ L sample loc tape (M + 1) 0
    (treeCacheRun hB scale σ L sample loc tape 0) = _
  simpa only [Nat.zero_add] using sourceTreeExecuteFrom_eq_cacheRun hB scale σ L sample loc tape (M + 1) 0

theorem treePacketCalls_le_capacity {E : Type*} {d B : ℕ}
    {scale σ L : ℝ} (hs : 0 ≤ scale) (hcap : B = batchSize scale (σ^2))
    (loc : ℕ → TreeCache d E → Point d) (k : ℕ) (cache : TreeCache d E) :
    treePacketCalls (B := B) scale σ L loc k cache ≤ 2 * B := by
  unfold treePacketCalls treeChosenBatch
  split_ifs
  · omega
  · apply Nat.mul_le_mul_left
    rw [hcap]
    exact chordBatchSize_le_capacity hs _ _ _ _

theorem sourceTreeProgram_usesAtMost {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {d M B : ℕ} (hB : 0 < B) {scale σ L : ℝ}
    (hs : 0 ≤ scale) (hcap : B = batchSize scale (σ^2))
    (flag : Bool) (project : PersistentReply d → E) (loc : ℕ → TreeCache d E → Point d)
    (m k : ℕ) (cache : TreeCache d E) :
    OracleProgram.UsesAtMost (m * (2 * B)) (sourceTreeProgram (M := M) hB scale σ L flag project loc m k cache) := by
  induction m generalizing k cache with
  | zero => simp only [sourceTreeProgram, OracleProgram.UsesAtMost]
  | succ m ih =>
    have hp := OracleProgram.usesAtMost_mono
      (treePacketProgram_exact (M := M) hB scale σ L flag project loc k cache).usesAtMost
      (treePacketCalls_le_capacity hs hcap loc k cache)
    have hb := OracleProgram.usesAtMost_bind hp
      (fun packet => sourceTreeProgram hB scale σ L flag project loc m (k + 1) (cacheAfterPacket loc k cache packet))
      (fun packet => ih (k + 1) (cacheAfterPacket loc k cache packet))
    simpa only [sourceTreeProgram, Nat.succ_mul, Nat.add_comm] using hb

end
end SampleReuse
