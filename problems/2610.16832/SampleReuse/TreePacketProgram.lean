import SampleReuse.TreeExecution
import SampleReuse.OracleProgramAccess

/-! Every packet in the cache execution is implemented by a reply-only
program. The scalar-loss tape is accessed through persistent derivative
queries, with the root charged once and each chord sample twice. -/

open MeasureTheory ProbabilityTheory SecondOrder
open scoped BigOperators Classical

namespace SampleReuse
noncomputable section

def fieldRootProgram {E : Type} [AddCommGroup E] [Module ℝ E] {H d b : ℕ}
    (flag : Bool) (project : PersistentReply d → E) (handles : Fin b → Fin H) (x : Point d) :
    OracleProgram (PersistentQuery H d) (PersistentReply d) E :=
  OracleProgram.batch b (fun i => (flag, handles i, x))
    (fun ys => (b : ℝ)⁻¹ • ∑ i : Fin b, project (ys i))

def fieldChordProgram {E : Type} [AddCommGroup E] [Module ℝ E] {H d b : ℕ}
    (flag : Bool) (project : PersistentReply d → E) (handles : Fin b → Fin H) (x y : Point d) :
    OracleProgram (PersistentQuery H d) (PersistentReply d) E :=
  OracleProgram.batch (b * 2) (chordBatchQueries flag handles x y)
    (fun ys => (b : ℝ)⁻¹ • ∑ i : Fin b,
      (project (ys (finProdFinEquiv (i, 0))) - project (ys (finProdFinEquiv (i, 1)))))

def treePacketCalls {E : Type*} {d B : ℕ} (scale σ L : ℝ)
    (loc : ℕ → TreeCache d E → Point d) (k : ℕ) (cache : TreeCache d E) : ℕ :=
  if k = 0 then B else 2 * treeChosenBatch (B := B) scale σ L loc k cache

def treePacketProgram {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {d M B : ℕ}
    (hB : 0 < B) (scale σ L : ℝ) (flag : Bool) (project : PersistentReply d → E)
    (loc : ℕ → TreeCache d E → Point d) (k : ℕ) (cache : TreeCache d E) :
    OracleProgram (PersistentQuery ((M + 1) * B) d) (PersistentReply d) E :=
  if k = 0 then fieldRootProgram flag project (treeBlockHandle M B k) (loc k cache) else
    fieldChordProgram flag project
      (fun i : Fin (treeChosenBatch (B := B) scale σ L loc k cache) =>
        treeBlockHandle M B k (prefixHandles hB _ i))
      (loc k cache) (cache (ancestorParent k)).1

theorem fieldRootProgram_exact {E : Type} [AddCommGroup E] [Module ℝ E] {H d b : ℕ}
    (flag : Bool) (project : PersistentReply d → E) (handles : Fin b → Fin H) (x : Point d) :
    OracleProgram.UsesExactly b (fieldRootProgram flag project handles x) :=
  OracleProgram.batch_usesExactly _ _ _

theorem fieldChordProgram_exact {E : Type} [AddCommGroup E] [Module ℝ E] {H d b : ℕ}
    (flag : Bool) (project : PersistentReply d → E) (handles : Fin b → Fin H) (x y : Point d) :
    OracleProgram.UsesExactly (2 * b) (fieldChordProgram flag project handles x y) := by
  simpa only [fieldChordProgram, Nat.mul_comm] using OracleProgram.batch_usesExactly
    (b * 2) (chordBatchQueries flag handles x y)
    (fun ys => (b : ℝ)⁻¹ • ∑ i : Fin b,
      (project (ys (finProdFinEquiv (i, 0))) - project (ys (finProdFinEquiv (i, 1)))))

theorem treePacketProgram_exact {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {d M B : ℕ} (hB : 0 < B) (scale σ L : ℝ) (flag : Bool) (project : PersistentReply d → E)
    (loc : ℕ → TreeCache d E → Point d) (k : ℕ) (cache : TreeCache d E) :
    OracleProgram.UsesExactly (treePacketCalls (B := B) scale σ L loc k cache)
      (treePacketProgram (M := M) hB scale σ L flag project loc k cache) := by
  unfold treePacketCalls treePacketProgram
  split_ifs
  · exact fieldRootProgram_exact _ _ _ _
  · exact fieldChordProgram_exact _ _ _ _ _

theorem treePacketProgram_access {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {d M B : ℕ} (hB : 0 < B) (scale σ L : ℝ) (flag : Bool) (project : PersistentReply d → E)
    (loc : ℕ → TreeCache d E → Point d) (k : ℕ) (cache : TreeCache d E) :
    QueriesSatisfy (fun q : PersistentQuery ((M + 1) * B) d =>
      q.1 = flag ∧ q.2.1 ∈ Set.range (treeBlockHandle M B k))
      (treePacketProgram hB scale σ L flag project loc k cache) := by
  unfold treePacketProgram
  split_ifs <;> apply batch_queriesSatisfy <;> intro i
  · exact ⟨rfl, ⟨i, rfl⟩⟩
  · exact ⟨rfl, ⟨_, rfl⟩⟩

theorem fieldRootProgram_run {Ω E : Type} [AddCommGroup E] [Module ℝ E] {H d b : ℕ}
    (q₀ : PersistentQuery H d) (F : Ω → Point d → ℝ) (sample : Ω → Point d → E)
    (flag : Bool) (project : PersistentReply d → E)
    (hfield : ∀ (tape : SampleTape H Ω) (r : Fin H) (x : Point d),
      project (persistentReply F tape (flag, r, x)) = sample (tape r) x)
    (handles : Fin b → Fin H) (x : Point d) (tape : SampleTape H Ω) :
    OracleProgram.run q₀ (fun q tape => persistentReply F tape q) (fun _ => tape)
      (fieldRootProgram flag project handles x) b =
        .done (batchMeanTape (fun z => sample z x) handles tape) := by
  rw [fieldRootProgram, persistentBatch_run]
  simp only [hfield, batchMeanTape]

theorem fieldChordProgram_run {Ω E : Type} [AddCommGroup E] [Module ℝ E] {H d b : ℕ}
    (q₀ : PersistentQuery H d) (F : Ω → Point d → ℝ) (sample : Ω → Point d → E)
    (flag : Bool) (project : PersistentReply d → E)
    (hfield : ∀ (tape : SampleTape H Ω) (r : Fin H) (x : Point d),
      project (persistentReply F tape (flag, r, x)) = sample (tape r) x)
    (handles : Fin b → Fin H) (x y : Point d) (tape : SampleTape H Ω) :
    OracleProgram.run q₀ (fun q tape => persistentReply F tape q) (fun _ => tape)
      (fieldChordProgram flag project handles x y) (2 * b) =
        .done (batchMeanTape (fun z => sample z x - sample z y) handles tape) := by
  rw [Nat.mul_comm 2 b, fieldChordProgram, persistentBatch_run]
  simp only [chordBatchQueries, Equiv.symm_apply_apply, if_true, Fin.zero_ne_one, if_false,
    hfield, batchMeanTape]
  norm_num

theorem treePacketProgram_run {Ω E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {d M B : ℕ} (hB : 0 < B) (scale σ L : ℝ)
    (q₀ : PersistentQuery ((M + 1) * B) d) (F : Ω → Point d → ℝ) (sample : Ω → Point d → E)
    (flag : Bool) (project : PersistentReply d → E)
    (hfield : ∀ (tape : SampleTape ((M + 1) * B) Ω) (r : Fin ((M + 1) * B)) (x : Point d),
      project (persistentReply F tape (flag, r, x)) = sample (tape r) x)
    (loc : ℕ → TreeCache d E → Point d) (k : ℕ) (cache : TreeCache d E)
    (tape : SampleTape ((M + 1) * B) Ω) :
    OracleProgram.run q₀ (fun q tape => persistentReply F tape q) (fun _ => tape)
      (treePacketProgram hB scale σ L flag project loc k cache)
      (treePacketCalls (B := B) scale σ L loc k cache) =
        .done (treeCachePacket hB scale σ L sample loc k cache tape) := by
  unfold treePacketProgram treePacketCalls treeCachePacket
  split_ifs
  · exact fieldRootProgram_run q₀ F sample flag project hfield _ _ tape
  · exact fieldChordProgram_run q₀ F sample flag project hfield _ _ _ tape

end
end SampleReuse
