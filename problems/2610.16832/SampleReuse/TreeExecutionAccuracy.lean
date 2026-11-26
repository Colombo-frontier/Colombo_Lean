import SampleReuse.TreeExecution

/-! The actual numerical cache is identified with the ancestor estimator.
Predictability, and hence uniform accuracy, is derived from the executable
cache recurrence rather than supplied as an estimator assumption. -/

open MeasureTheory ProbabilityTheory SecondOrder
open scoped BigOperators Classical

namespace SampleReuse
noncomputable section

variable {Ω E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {d M B : ℕ}
    (hB : 0 < B) (scale σ L : ℝ) (sample : Ω → Point d → E)
    (loc : ℕ → TreeCache d E → Point d) (tape : SampleTape ((M + 1) * B) Ω)

def treeGeneratedEstimate (k : ℕ) : E :=
  (treeCacheRun hB scale σ L sample loc tape (k + 1) k).2

theorem treeCacheRun_preserves {j k : ℕ} (hj : j < k) :
    treeCacheRun hB scale σ L sample loc tape (k + 1) j =
      treeCacheRun hB scale σ L sample loc tape k j := by
  simp only [treeCacheRun, treeCacheStep, Function.update_of_ne hj.ne]

theorem treeCacheRun_entry {j k : ℕ} (hj : j < k) :
    treeCacheRun hB scale σ L sample loc tape k j =
      treeCacheRun hB scale σ L sample loc tape (j + 1) j := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases heq : j = k
    · subst j; rfl
    · have hjk : j < k := by omega
      rw [treeCacheRun_preserves hB scale σ L sample loc tape hjk]
      exact ih hjk

theorem treeCacheRun_location_entry {j k : ℕ} (hj : j < k) :
    (treeCacheRun hB scale σ L sample loc tape k j).1 =
      treeGeneratedLocation hB scale σ L sample loc j tape := by
  rw [treeCacheRun_entry hB scale σ L sample loc tape hj]
  simp only [treeCacheRun, treeCacheStep, Function.update_self, treeGeneratedLocation]

theorem treeCachePacket_eq_sampledChord {k : ℕ} (hk : 0 < k) :
    treeCachePacket hB scale σ L sample loc k (treeCacheRun hB scale σ L sample loc tape k) tape =
      treeChordPacket hB scale σ L sample
        (treeGeneratedLocation hB scale σ L sample loc) k tape := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  unfold treeCachePacket
  simp only [treeChosenBatch, Nat.succ_ne_zero, if_false]
  rw [treeCacheRun_location_entry hB scale σ L sample loc tape (ancestorParent_lt hk)]
  rfl

theorem treeGeneratedEstimate_zero :
    treeGeneratedEstimate hB scale σ L sample loc tape 0 =
      treeRootPacket sample (treeGeneratedLocation hB scale σ L sample loc) tape := by
  simp only [treeGeneratedEstimate, treeCacheRun, treeCacheStep, Function.update_self,
    if_true, treeCachePacket, treeRootPacket, treeGeneratedLocation]

theorem treeGeneratedEstimate_succ (k : ℕ) :
    treeGeneratedEstimate hB scale σ L sample loc tape (k + 1) =
      treeGeneratedEstimate hB scale σ L sample loc tape (ancestorParent (k + 1)) +
        treeChordPacket hB scale σ L sample
          (treeGeneratedLocation hB scale σ L sample loc) (k + 1) tape := by
  change (treeCacheStep hB scale σ L sample loc (k + 1)
    (treeCacheRun hB scale σ L sample loc tape (k + 1)) tape (k + 1)).2 = _
  simp only [treeCacheStep, Function.update_self, if_neg (Nat.succ_ne_zero k)]
  rw [treeCacheRun_entry hB scale σ L sample loc tape (ancestorParent_lt (Nat.succ_pos k)),
    treeCachePacket_eq_sampledChord hB scale σ L sample loc tape (Nat.succ_pos k)]
  rfl

theorem treeGeneratedEstimate_eq_sampledAncestorEstimate (k : ℕ) :
    treeGeneratedEstimate hB scale σ L sample loc tape k =
      sampledAncestorEstimate hB scale σ L sample
        (treeGeneratedLocation hB scale σ L sample loc) tape k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    cases k with
    | zero =>
      simpa only [sampledAncestorEstimate, ancestorEstimate] using
        treeGeneratedEstimate_zero hB scale σ L sample loc tape
    | succ k =>
      rw [treeGeneratedEstimate_succ,
        ih _ (ancestorParent_lt (Nat.succ_pos k))]
      simp only [sampledAncestorEstimate, ancestorEstimate]

variable [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Parameters}
    {f : Point d → ℝ} {F : Ω → Point d → ℝ} {x₀ : Point d}

theorem Admissible.gradient_cache_execution_success (h : Admissible μ P f F x₀)
    (z₀ : Ω) {η δ scale : ℝ} (hη : 0 < η) (hδ : 0 < δ)
    (hscale : scale = confidenceBatchScale d (η / (binaryDepth M + 1)) (δ / (M + 1)))
    (hcap : B = batchSize scale (P.gradientNoise^2)) (hB : 0 < B)
    (loc : ℕ → TreeCache d (Point d) → Point d) (hloc : ∀ k, Measurable (loc k)) :
    1 - δ ≤ (sampleTapeLaw ((M + 1) * B) μ).real {tape | ∀ k ≤ M,
      ‖treeGeneratedEstimate hB scale P.gradientNoise P.gradientLip (fun z => gradient (F z)) loc tape k -
        gradient f (treeGeneratedLocation hB scale P.gradientNoise P.gradientLip
          (fun z => gradient (F z)) loc k tape)‖ ≤ η} := by
  simp_rw [treeGeneratedEstimate_eq_sampledAncestorEstimate]
  exact h.gradient_tree_success z₀ hη hδ hscale hcap hB _
    (treeGeneratedLocation_predictable hB scale P.gradientNoise P.gradientLip
      _ h.gradient_measurable loc hloc)

theorem Admissible.hessian_cache_execution_success (h : Admissible μ P f F x₀)
    (z₀ : Ω) {η δ scale : ℝ} (hη : 0 < η) (hδ : 0 < δ)
    (hscale : scale = confidenceBatchScale d (η / (binaryDepth M + 1)) (δ / (M + 1)))
    (hcap : B = batchSize scale (P.hessianNoise^2)) (hB : 0 < B)
    (loc : ℕ → TreeCache d (Point d →L[ℝ] Point d) → Point d) (hloc : ∀ k, Measurable (loc k)) :
    1 - δ ≤ (sampleTapeLaw ((M + 1) * B) μ).real {tape | ∀ k ≤ M,
      ‖treeGeneratedEstimate hB scale P.hessianNoise P.hessianLip (fun z => hessian (F z)) loc tape k -
        hessian f (treeGeneratedLocation hB scale P.hessianNoise P.hessianLip
          (fun z => hessian (F z)) loc k tape)‖ ≤ η} := by
  simp_rw [treeGeneratedEstimate_eq_sampledAncestorEstimate]
  exact h.hessian_tree_success z₀ hη hδ hscale hcap hB _
    (treeGeneratedLocation_predictable hB scale P.hessianNoise P.hessianLip
      _ h.hessian_measurable loc hloc)

end
end SampleReuse
