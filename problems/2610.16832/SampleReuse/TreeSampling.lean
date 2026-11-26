import SampleReuse.OracleAdaptiveSize
import SampleReuse.AncestorNodes

/-! A finite immutable sample tape for the literal binary-ancestor sampler.
One disjoint block is reserved per checkpoint. Every block's size is bounded
by the root batch; edge packets use only their adaptively chosen prefix. -/

open MeasureTheory ProbabilityTheory SecondOrder
open scoped BigOperators Classical

namespace SampleReuse
noncomputable section

def treeBlockHandle (M B k : ℕ) (i : Fin B) : Fin ((M + 1) * B) :=
  finProdFinEquiv (⟨k % (M + 1), Nat.mod_lt _ (Nat.succ_pos M)⟩, i)

def treePastHandles (M B k : ℕ) : Finset (Fin ((M + 1) * B)) :=
  Finset.univ.filter (fun r => r.val < k * B)

theorem treeBlockHandle_injective (M B k : ℕ) : Function.Injective (treeBlockHandle M B k) := by
  intro i j hij
  exact congrArg Prod.snd (finProdFinEquiv.injective hij)

theorem treeBlockHandle_val {M B k : ℕ} (hk : k ≤ M) (i : Fin B) :
    (treeBlockHandle M B k i).val = i.val + B * k := by
  simp only [treeBlockHandle, finProdFinEquiv_apply_val, Nat.mod_eq_of_lt (Nat.lt_succ_of_le hk)]

theorem treeBlockHandle_fresh {M B k : ℕ} (hk : k ≤ M) (i : Fin B) :
    treeBlockHandle M B k i ∉ treePastHandles M B k := by
  simp only [treePastHandles, Finset.mem_filter, Finset.mem_univ, true_and,
    treeBlockHandle_val hk]
  rw [Nat.mul_comm k B]
  omega

theorem treeBlockHandle_in_past {M B j k : ℕ} (hj : j ≤ M) (hjk : j < k) (i : Fin B) :
    treeBlockHandle M B j i ∈ treePastHandles M B k := by
  simp only [treePastHandles, Finset.mem_filter, Finset.mem_univ, true_and,
    treeBlockHandle_val hj]
  have hi := i.isLt
  nlinarith

theorem treePastHandles_mono {M B j k : ℕ} (hjk : j ≤ k) :
    treePastHandles M B j ⊆ treePastHandles M B k := by
  intro r hr
  simp only [treePastHandles, Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
  exact hr.trans_le (Nat.mul_le_mul_right B hjk)

/-- Locations are selected before their checkpoint's fresh sample block.
This is the usual predictable input condition on the estimator's caller. -/
structure PredictableLocations {Ω : Type*} [MeasurableSpace Ω] {d M B : ℕ}
    (y : ℕ → SampleTape ((M + 1) * B) Ω → Point d) : Prop where
  measurable : ∀ k ≤ M, Measurable (y k)
  depends : ∀ k ≤ M, ∀ tape tape',
    (∀ r ∈ treePastHandles M B k, tape r = tape' r) → y k tape = y k tape'

theorem PredictableLocations.pair_depends {Ω : Type*} [MeasurableSpace Ω] {d M B k : ℕ}
    {y : ℕ → SampleTape ((M + 1) * B) Ω → Point d}
    (hy : PredictableLocations y) (hk : k ≤ M) (hpos : 0 < k)
    (tape tape' : SampleTape ((M + 1) * B) Ω)
    (heq : ∀ r ∈ treePastHandles M B k, tape r = tape' r) :
    (y k tape, y (ancestorParent k) tape) = (y k tape', y (ancestorParent k) tape') := by
  apply Prod.ext (hy.depends k hk tape tape' heq)
  apply hy.depends (ancestorParent k) ((ancestorParent_lt hpos).le.trans hk)
  intro r hr
  exact heq r (treePastHandles_mono (ancestorParent_lt hpos).le hr)

theorem PredictableLocations.root_constant {Ω : Type*} [MeasurableSpace Ω] {d M B : ℕ}
    {y : ℕ → SampleTape ((M + 1) * B) Ω → Point d}
    (hy : PredictableLocations y) (z₀ : Ω) (tape : SampleTape ((M + 1) * B) Ω) :
    y 0 tape = y 0 (fun _ => z₀) := by
  apply hy.depends 0 (Nat.zero_le M)
  intro r hr
  simp [treePastHandles] at hr

def treeRootPacket {Ω E : Type*} [AddCommGroup E] [Module ℝ E] {d M B : ℕ}
    (sample : Ω → Point d → E) (y : ℕ → SampleTape ((M + 1) * B) Ω → Point d)
    (tape : SampleTape ((M + 1) * B) Ω) : E :=
  batchMeanTape (fun z => sample z (y 0 tape)) (treeBlockHandle M B 0) tape

def treeChordPacket {Ω E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {d M B : ℕ}
    (hB : 0 < B) (scale σ L : ℝ) (sample : Ω → Point d → E)
    (y : ℕ → SampleTape ((M + 1) * B) Ω → Point d) (k : ℕ)
    (tape : SampleTape ((M + 1) * B) Ω) : E :=
  adaptiveBatchMean hB (fun xy : Point d × Point d => fun z => sample z xy.1 - sample z xy.2)
    (fun xy => chordBatchSize scale σ L xy.1 xy.2)
    (y k tape, y (ancestorParent k) tape) (fun i => tape (treeBlockHandle M B k i))

def sampledAncestorEstimate {Ω E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {d M B : ℕ}
    (hB : 0 < B) (scale σ L : ℝ) (sample : Ω → Point d → E)
    (y : ℕ → SampleTape ((M + 1) * B) Ω → Point d)
    (tape : SampleTape ((M + 1) * B) Ω) (k : ℕ) : E :=
  ancestorEstimate (treeRootPacket sample y tape) (fun j => treeChordPacket hB scale σ L sample y j tape) k

def treeSamplerCost {Ω : Type*} {d M B : ℕ} (scale σ L : ℝ)
    (y : ℕ → SampleTape ((M + 1) * B) Ω → Point d) (tape : SampleTape ((M + 1) * B) Ω) : ℕ :=
  batchSize scale (σ^2) + 2 * ∑ k ∈ Finset.Icc 1 M,
    chordBatchSize scale σ L (y k tape) (y (ancestorParent k) tape)

theorem ancestorEstimate_error {E : Type*} [NormedAddCommGroup E]
    (M : ℕ) (A : ℕ → E) (anchor : E) (difference : ℕ → E)
    {η : ℝ} (hη : 0 ≤ η)
    (hroot : ‖anchor-A 0‖ ≤ η/(binaryDepth M + 1))
    (hedge : ∀ k, 0 < k → k ≤ M →
      ‖difference k - (A k - A (ancestorParent k))‖ ≤ η/(binaryDepth M + 1)) :
    ∀ k ≤ M, ‖ancestorEstimate anchor difference k - A k‖ ≤ η := by
  intro k hk
  rw [ancestorEstimate_eq_binaryTracker anchor difference k (binaryDepth_sufficient hk)]
  apply tree_estimate_error_useful M A anchor (fun _ i => difference (nodeRight i)) hη hroot _ k hk
  intro i hi hu
  have hr := (mem_completedNodes i).mp hi
  simpa only [usefulNode_parent i hu] using hedge (nodeRight i) (nodeRight_pos i) hr

theorem ancestorEstimate_uniform_probability {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (M : ℕ) (A : Ω → ℕ → E) (anchor : Ω → E) (difference : Ω → ℕ → E)
    {η δ : ℝ} (hη : 0 ≤ η)
    (hroot : μ.real {tape | η/(binaryDepth M + 1) ≤ ‖anchor tape - A tape 0‖} ≤ δ)
    (hedge : ∀ k, 0 < k → k ≤ M →
      μ.real {tape | η/(binaryDepth M + 1) ≤
        ‖difference tape k - (A tape k - A tape (ancestorParent k))‖} ≤ δ) :
    μ.real {tape | ∃ k ≤ M, η < ‖ancestorEstimate (anchor tape) (difference tape) k - A tape k‖} ≤
      (M + 1 : ℕ) * δ := by
  let bad : Fin (M + 1) → Set Ω := fun k => if k.val = 0 then
    {tape | η/(binaryDepth M + 1) ≤ ‖anchor tape - A tape 0‖} else
    {tape | η/(binaryDepth M + 1) ≤
      ‖difference tape k - (A tape k - A tape (ancestorParent k))‖}
  have hb (k : Fin (M + 1)) : μ.real (bad k) ≤ δ := by
    by_cases hk : k.val = 0
    · simpa only [bad, if_pos hk] using hroot
    · simpa only [bad, if_neg hk] using hedge k (Nat.pos_of_ne_zero hk) (by omega)
  have hsub : {tape | ∃ k ≤ M, η < ‖ancestorEstimate (anchor tape) (difference tape) k - A tape k‖} ⊆
      ⋃ k : Fin (M + 1), bad k := by
    intro tape ht
    by_contra hn
    have hnot : ∀ k : Fin (M + 1), tape ∉ bad k := by simpa only [Set.mem_iUnion, not_exists] using hn
    have hroot' : ‖anchor tape - A tape 0‖ ≤ η/(binaryDepth M + 1) := by
      have hn0 := hnot 0
      simp only [bad, Fin.val_zero, if_true, Set.mem_setOf_eq, not_le] at hn0
      exact hn0.le
    have hedge' (k : ℕ) (hkpos : 0 < k) (hk : k ≤ M) :
        ‖difference tape k - (A tape k - A tape (ancestorParent k))‖ ≤ η/(binaryDepth M + 1) := by
      have hn' := hnot ⟨k, by omega⟩
      simp only [bad, if_neg hkpos.ne', Set.mem_setOf_eq, not_le] at hn'
      exact hn'.le
    obtain ⟨k, hk, hfail⟩ := ht
    exact not_lt_of_ge (ancestorEstimate_error M (A tape) (anchor tape) (difference tape) hη hroot' hedge' k hk) hfail
  calc
    _ ≤ μ.real (⋃ k : Fin (M + 1), bad k) := measureReal_mono hsub
    _ ≤ ∑ k : Fin (M + 1), μ.real (bad k) := measureReal_iUnion_fintype_le bad
    _ ≤ ∑ _k : Fin (M + 1), δ := Finset.sum_le_sum (fun k _ => hb k)
    _ = _ := by simp

end
end SampleReuse
