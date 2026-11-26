import SampleReuse.TreeProgram

/-! Observable-prefix measurability of the full reply-only tree program,
including adaptive ceiling batch sizes and numerical cache continuations. -/

open MeasureTheory SecondOrder
open scoped BigOperators Classical

namespace SampleReuse
noncomputable section

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem fieldRootProgram_measurableFamily {H d b : ℕ}
    (q₀ : PersistentQuery H d) (flag : Bool) (project : PersistentReply d → E) (hp : Measurable project) :
    OracleProgram.MeasurableFamily q₀ 0
      (fun w : (Fin b → Fin H) × Point d => fieldRootProgram flag project w.1 w.2) := by
  apply OracleProgram.batch_measurable
  · intro i
    exact measurable_const.prodMk (((measurable_pi_apply i).comp measurable_fst).prodMk measurable_snd)
  · have ht (i : Fin b) : Measurable (fun w : ((Fin b → Fin H) × Point d) × (Fin b → PersistentReply d) =>
        project (w.2 i)) := hp.comp ((measurable_pi_apply i).comp measurable_snd)
    exact (Finset.measurable_sum Finset.univ (fun i _ => ht i)).const_smul ((b : ℝ)⁻¹)

theorem fieldChordProgram_measurableFamily {H d b : ℕ}
    (q₀ : PersistentQuery H d) (flag : Bool) (project : PersistentReply d → E) (hp : Measurable project) :
    OracleProgram.MeasurableFamily q₀ 0
      (fun w : (Fin b → Fin H) × (Point d × Point d) => fieldChordProgram flag project w.1 w.2.1 w.2.2) := by
  apply OracleProgram.batch_measurable
  · exact chordBatchQueries_measurable flag
  · have ht (i : Fin b) : Measurable
        (fun w : ((Fin b → Fin H) × (Point d × Point d)) × (Fin (b * 2) → PersistentReply d) =>
          project (w.2 (finProdFinEquiv (i, 0))) - project (w.2 (finProdFinEquiv (i, 1)))) :=
      (hp.comp ((measurable_pi_apply (finProdFinEquiv (i, 0))).comp measurable_snd)).sub
        (hp.comp ((measurable_pi_apply (finProdFinEquiv (i, 1))).comp measurable_snd))
    exact (Finset.measurable_sum Finset.univ (fun i _ => ht i)).const_smul ((b : ℝ)⁻¹)

theorem treePacketProgram_measurableFamily {d M B : ℕ} (hB : 0 < B) (scale σ L : ℝ)
    (q₀ : PersistentQuery ((M + 1) * B) d) (flag : Bool)
    (project : PersistentReply d → E) (hp : Measurable project)
    (loc : ℕ → TreeCache d E → Point d) (hloc : ∀ k, Measurable (loc k)) (k : ℕ) :
    OracleProgram.MeasurableFamily q₀ 0 (treePacketProgram hB scale σ L flag project loc k) := by
  unfold treePacketProgram
  by_cases hk : k = 0
  · simp only [if_pos hk]
    exact
      (fieldRootProgram_measurableFamily q₀ flag project hp).comp
        (fun cache => (treeBlockHandle M B k, loc k cache)) (measurable_const.prodMk (hloc k))
  · have hfixed (n : ℕ) : OracleProgram.MeasurableFamily q₀ 0
        (fun cache : TreeCache d E => fieldChordProgram flag project
          (fun i => treeBlockHandle M B k (prefixHandles hB n i))
          (loc k cache) (cache (ancestorParent k)).1) :=
      (fieldChordProgram_measurableFamily q₀ flag project hp).comp
        (fun cache => ((fun i => treeBlockHandle M B k (prefixHandles hB n i)),
          loc k cache, (cache (ancestorParent k)).1))
        (measurable_const.prodMk ((hloc k).prodMk (measurable_pi_apply _).fst))
    have hv := OracleProgram.MeasurableFamily.chooseNat
      (fun n cache => fieldChordProgram flag project
        (fun i => treeBlockHandle M B k (prefixHandles hB n i))
        (loc k cache) (cache (ancestorParent k)).1)
      hfixed (treeChosenBatch (B := B) scale σ L loc k)
      (treeChosenBatch_measurable scale σ L loc hloc k)
    simpa only [if_neg hk] using hv

omit [NormedSpace ℝ E] in
theorem cacheAfterPacket_measurable {d : ℕ} (loc : ℕ → TreeCache d E → Point d)
    (hloc : ∀ k, Measurable (loc k)) (k : ℕ) :
    Measurable (fun w : TreeCache d E × E => cacheAfterPacket loc k w.1 w.2) := by
  apply measurable_pi_lambda
  intro j
  by_cases hj : j = k
  · subst j
    simp only [cacheAfterPacket, Function.update_self]
    apply ((hloc k).comp measurable_fst).prodMk
    by_cases hk : k = 0
    · simpa only [if_pos hk] using (measurable_snd : Measurable (fun w : TreeCache d E × E => w.2))
    · simpa only [if_neg hk] using
        ((((measurable_pi_apply (ancestorParent k)).comp measurable_fst).snd).add
          (measurable_snd : Measurable (fun w : TreeCache d E × E => w.2)))
  · simpa only [cacheAfterPacket, Function.update_of_ne hj] using
      (measurable_pi_apply j).comp (measurable_fst : Measurable (fun w : TreeCache d E × E => w.1))

theorem sourceTreeProgram_measurableFamily {d M B : ℕ} (hB : 0 < B) (scale σ L : ℝ)
    (q₀ : PersistentQuery ((M + 1) * B) d) (flag : Bool)
    (project : PersistentReply d → E) (hp : Measurable project)
    (loc : ℕ → TreeCache d E → Point d) (hloc : ∀ k, Measurable (loc k)) (m k : ℕ) :
    OracleProgram.MeasurableFamily q₀ (fun _ => (0, 0))
      (sourceTreeProgram hB scale σ L flag project loc m k) := by
  induction m generalizing k with
  | zero => exact OracleProgram.measurableFamily_done q₀ _ id measurable_id
  | succ m ih =>
    exact (treePacketProgram_measurableFamily hB scale σ L q₀ flag project hp loc hloc k).bind
      ((ih (k + 1)).comp (fun w : TreeCache d E × E => cacheAfterPacket loc k w.1 w.2)
        (cacheAfterPacket_measurable loc hloc k))

end
end SampleReuse
