import SampleReuse.TreeSamplingMeasurable

/-! An actual numerical cache execution of Algorithm 2. The location policy
reads only previous cached point/estimate pairs. The sampled loss tape is
accessible exclusively inside the batch packet routine. -/

open MeasureTheory ProbabilityTheory SecondOrder
open scoped BigOperators Classical

namespace SampleReuse
noncomputable section

abbrev TreeCache (d : ℕ) (E : Type*) := ℕ → (Point d × E)

def treeChosenBatch {E : Type*} {d B : ℕ} (scale σ L : ℝ)
    (loc : ℕ → TreeCache d E → Point d) (k : ℕ) (cache : TreeCache d E) : ℕ :=
  if k = 0 then B else chordBatchSize scale σ L (loc k cache) (cache (ancestorParent k)).1

def treeCachePacket {Ω E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {d M B : ℕ} (hB : 0 < B) (scale σ L : ℝ) (sample : Ω → Point d → E)
    (loc : ℕ → TreeCache d E → Point d) (k : ℕ) (cache : TreeCache d E)
    (tape : SampleTape ((M + 1) * B) Ω) : E :=
  if k = 0 then batchMeanTape (fun z => sample z (loc k cache)) (treeBlockHandle M B k) tape else
    batchMeanTape (fun z => sample z (loc k cache) - sample z (cache (ancestorParent k)).1)
      (fun i : Fin (treeChosenBatch (B := B) scale σ L loc k cache) =>
        treeBlockHandle M B k (prefixHandles hB _ i)) tape

def treeCacheStep {Ω E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {d M B : ℕ} (hB : 0 < B) (scale σ L : ℝ) (sample : Ω → Point d → E)
    (loc : ℕ → TreeCache d E → Point d) (k : ℕ) (cache : TreeCache d E)
    (tape : SampleTape ((M + 1) * B) Ω) : TreeCache d E :=
  Function.update cache k (loc k cache,
    if k = 0 then treeCachePacket hB scale σ L sample loc k cache tape else
      (cache (ancestorParent k)).2 + treeCachePacket hB scale σ L sample loc k cache tape)

def treeCacheRun {Ω E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {d M B : ℕ} (hB : 0 < B) (scale σ L : ℝ) (sample : Ω → Point d → E)
    (loc : ℕ → TreeCache d E → Point d) (tape : SampleTape ((M + 1) * B) Ω) : ℕ → TreeCache d E
  | 0 => fun _ => (0, 0)
  | k + 1 => treeCacheStep hB scale σ L sample loc k
      (treeCacheRun hB scale σ L sample loc tape k) tape

def treeGeneratedLocation {Ω E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {d M B : ℕ} (hB : 0 < B) (scale σ L : ℝ) (sample : Ω → Point d → E)
    (loc : ℕ → TreeCache d E → Point d) (k : ℕ) (tape : SampleTape ((M + 1) * B) Ω) : Point d :=
  loc k (treeCacheRun hB scale σ L sample loc tape k)

theorem batchMeanTape_congr_tape {Ω E : Type*} [AddCommGroup E] [Module ℝ E]
    {H b : ℕ} (A : Ω → E) (handles : Fin b → Fin H) (tape tape' : SampleTape H Ω)
    (heq : ∀ i, tape (handles i) = tape' (handles i)) :
    batchMeanTape A handles tape = batchMeanTape A handles tape' := by
  unfold batchMeanTape
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [heq i]

theorem treeCacheStep_congr_tape {Ω E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {d M B : ℕ} (hB : 0 < B) (scale σ L : ℝ) (sample : Ω → Point d → E)
    (loc : ℕ → TreeCache d E → Point d) (k : ℕ) (cache : TreeCache d E)
    (tape tape' : SampleTape ((M + 1) * B) Ω)
    (heq : ∀ i, tape (treeBlockHandle M B k i) = tape' (treeBlockHandle M B k i)) :
    treeCacheStep hB scale σ L sample loc k cache tape =
      treeCacheStep hB scale σ L sample loc k cache tape' := by
  have hpacket : treeCachePacket hB scale σ L sample loc k cache tape =
      treeCachePacket hB scale σ L sample loc k cache tape' := by
    unfold treeCachePacket
    split_ifs
    · exact batchMeanTape_congr_tape _ _ _ _ heq
    · exact batchMeanTape_congr_tape _ _ _ _ (fun i => heq (prefixHandles hB _ i))
  simp only [treeCacheStep, hpacket]

theorem treeCacheRun_depends_on_past {Ω E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {d M B : ℕ} (hB : 0 < B) (scale σ L : ℝ) (sample : Ω → Point d → E)
    (loc : ℕ → TreeCache d E → Point d) (k : ℕ) (hk : k ≤ M + 1)
    (tape tape' : SampleTape ((M + 1) * B) Ω)
    (heq : ∀ r ∈ treePastHandles M B k, tape r = tape' r) :
    treeCacheRun hB scale σ L sample loc tape k = treeCacheRun hB scale σ L sample loc tape' k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hprev := ih (by omega) (fun r hr => heq r (treePastHandles_mono (Nat.le_succ k) hr))
    simp only [treeCacheRun, hprev]
    apply treeCacheStep_congr_tape
    intro i
    exact heq _ (treeBlockHandle_in_past (by omega) (Nat.lt_succ_self k) i)

theorem treeChosenBatch_measurable {E : Type*} [MeasurableSpace E] {d B : ℕ}
    (scale σ L : ℝ) (loc : ℕ → TreeCache d E → Point d)
    (hloc : ∀ k, Measurable (loc k)) (k : ℕ) :
    Measurable (treeChosenBatch (B := B) scale σ L loc k) := by
  unfold treeChosenBatch
  split_ifs
  · exact measurable_const
  · exact chordBatchSize_measurable _ _ _ _ _ (hloc k) (measurable_pi_apply _).fst

theorem treeCachePacket_measurable {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] {d M B : ℕ} (hB : 0 < B) (scale σ L : ℝ)
    (sample : Ω → Point d → E) (hs : Measurable (fun w : Ω × Point d => sample w.1 w.2))
    (loc : ℕ → TreeCache d E → Point d) (hloc : ∀ k, Measurable (loc k)) (k : ℕ) :
    Measurable (fun w : TreeCache d E × SampleTape ((M + 1) * B) Ω =>
      treeCachePacket hB scale σ L sample loc k w.1 w.2) := by
  by_cases hk : k = 0
  · simp only [treeCachePacket, if_pos hk, batchMeanTape]
    have ht (i : Fin B) : Measurable (fun w : TreeCache d E × SampleTape ((M + 1) * B) Ω =>
        sample (w.2 (treeBlockHandle M B k i)) (loc k w.1)) := by
      have hr : Measurable (fun w : TreeCache d E × SampleTape ((M + 1) * B) Ω =>
          w.2 (treeBlockHandle M B k i)) :=
        (measurable_pi_apply (treeBlockHandle M B k i)).comp measurable_snd
      have hx : Measurable (fun w : TreeCache d E × SampleTape ((M + 1) * B) Ω => loc k w.1) :=
        (hloc k).comp measurable_fst
      exact hs.comp (hr.prodMk hx)
    exact (Finset.measurable_sum Finset.univ (fun i _ => ht i)).const_smul ((B : ℝ)⁻¹)
  · have hsample : Measurable (fun w : TreeCache d E × Ω =>
        sample w.2 (loc k w.1) - sample w.2 (w.1 (ancestorParent k)).1) :=
      (hs.comp (measurable_snd.prodMk ((hloc k).comp measurable_fst))).sub
        (hs.comp (measurable_snd.prodMk (((measurable_pi_apply _).comp measurable_fst).fst)))
    have hm := adaptiveBatchMean_measurable hB
      (fun cache z => sample z (loc k cache) - sample z (cache (ancestorParent k)).1) hsample
      (treeChosenBatch (B := B) scale σ L loc k) (treeChosenBatch_measurable scale σ L loc hloc k)
    have hblock : Measurable (fun w : TreeCache d E × SampleTape ((M + 1) * B) Ω =>
        fun i : Fin B => w.2 (treeBlockHandle M B k i)) :=
      measurable_pi_lambda _ (fun i => (measurable_pi_apply (treeBlockHandle M B k i)).comp measurable_snd)
    have ht := hm.comp (measurable_fst.prodMk hblock)
    simpa only [treeCachePacket, if_neg hk, adaptiveBatchMean, batchMeanTape] using ht

theorem treeCacheRun_measurable {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] {d M B : ℕ} (hB : 0 < B) (scale σ L : ℝ)
    (sample : Ω → Point d → E) (hs : Measurable (fun w : Ω × Point d => sample w.1 w.2))
    (loc : ℕ → TreeCache d E → Point d) (hloc : ∀ k, Measurable (loc k)) (k : ℕ) :
    Measurable (fun tape : SampleTape ((M + 1) * B) Ω => treeCacheRun hB scale σ L sample loc tape k) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
    have hp := (treeCachePacket_measurable hB scale σ L sample hs loc hloc k).comp
      (ih.prodMk measurable_id)
    apply measurable_pi_lambda
    intro j
    by_cases hj : j = k
    · subst j
      simp only [treeCacheRun, treeCacheStep, Function.update_self]
      apply ((hloc k).comp ih).prodMk
      by_cases hk : k = 0
      · simpa only [if_pos hk] using hp
      · simpa only [if_neg hk] using (((measurable_pi_apply _).comp ih).snd.add hp)
    · simpa only [treeCacheRun, treeCacheStep, Function.update_of_ne hj] using
        (measurable_pi_apply j).comp ih

theorem treeGeneratedLocation_predictable {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] {d M B : ℕ} (hB : 0 < B) (scale σ L : ℝ)
    (sample : Ω → Point d → E) (hs : Measurable (fun w : Ω × Point d => sample w.1 w.2))
    (loc : ℕ → TreeCache d E → Point d) (hloc : ∀ k, Measurable (loc k)) :
    PredictableLocations (treeGeneratedLocation (M := M) hB scale σ L sample loc) := by
  constructor
  · intro k _
    exact (hloc k).comp (treeCacheRun_measurable hB scale σ L sample hs loc hloc k)
  · intro k hk tape tape' heq
    exact congrArg (loc k) (treeCacheRun_depends_on_past hB scale σ L sample loc k
      (hk.trans (Nat.le_succ M)) tape tape' heq)

end
end SampleReuse
