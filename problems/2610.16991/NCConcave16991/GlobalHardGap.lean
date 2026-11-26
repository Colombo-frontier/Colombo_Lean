import NCConcave16991.GlobalHardConstruction
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Compact

/-! # Initial gap of the literal global maximum on its public dual ball -/

namespace NCConcave16991.GlobalHard

noncomputable section

open Set
open scoped BigOperators InnerProductSpace
open BranchGeometry

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {M N : ℕ} (V : Fin M → Fin (N + 1) → Type*)
  [∀ j k, NormedAddCommGroup (V j k)] [∀ j k, InnerProductSpace ℝ (V j k)]
  [∀ j k, CompleteSpace (V j k)]
variable (B : ∀ j : Fin M, ∀ t : Fin N,
  BranchFamily (ι := ι) (V j t.castSucc) (V j t.succ))
  (u : ∀ j, V j 0) (v : ∀ j, V j (Fin.last N))

def atDual (x : Primal V) (w : Dual V) : Joint V := WithLp.toLp 2 (x, w)

def stageAverage (d r μ : ℝ) (j : Fin M) (z : Joint V) : ℝ :=
  (1 / (Fintype.card ι : ℝ)) * ∑ i, PipeSmoothness.component (B j) d r μ i (pipeProj V j z) +
    outerStage (u j) (v j) (precedingScore V v j z) (stateProj V j z) (aProj V j z) (bProj V j z)

theorem average_eq_sum (d r μ : ℝ) (z : Joint V) :
    average V B u v d r μ z = ∑ j, stageAverage V B u v d r μ j z := by
  unfold average component stageAverage
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_add_distrib, mul_add]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hn := ne_of_gt (cardReal_pos ι)
  field_simp

theorem stageAverage_at_zeroDual_lower (d r μ : ℝ) (hd : 0 ≤ d)
    (hu : ∀ j, ‖u j‖ = 1) (hv : ∀ j, ‖v j‖ = 1) (j : Fin M) (x : Primal V) :
    -31000 ≤ stageAverage V B u v d r μ j (atDual V x 0) := by
  have hpipe : (1 / (Fintype.card ι : ℝ)) *
      ∑ i, PipeSmoothness.component (B j) d r μ i (pipeProj V j (atDual V x 0)) =
      d * (‖aProj V j (atDual V x 0)‖ ^ 2 + ‖bProj V j (atDual V x 0)‖ ^ 2) := by
    change (1 / (Fintype.card ι : ℝ)) * ∑ i,
      fullPipeComponent (B j) d r μ (aProj V j (atDual V x 0)) (bProj V j (atDual V x 0))
        (fun k ↦ PipeSmoothness.wProj k (pipeProj V j (atDual V x 0))) i = _
    rw [fullPipe_average]
    have hw (k : Fin (N + 1)) : PipeSmoothness.wProj k (pipeProj V j (atDual V x 0)) = 0 := rfl
    simp [hw]
  have hout := outerStage_lower (u j) (hu j) (v j) (hv j)
    (precedingScore V v j (atDual V x 0)) (stateProj V j (atDual V x 0))
    (aProj V j (atDual V x 0)) (bProj V j (atDual V x 0))
  unfold stageAverage
  rw [hpipe]
  linarith [mul_nonneg hd (add_nonneg (sq_nonneg ‖aProj V j (atDual V x 0)‖)
    (sq_nonneg ‖bProj V j (atDual V x 0)‖))]

theorem average_at_zeroDual_lower (d r μ : ℝ) (hd : 0 ≤ d)
    (hu : ∀ j, ‖u j‖ = 1) (hv : ∀ j, ‖v j‖ = 1) (x : Primal V) :
    -31000 * M ≤ average V B u v d r μ (atDual V x 0) := by
  rw [average_eq_sum]
  have hh := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin M))) ↦
    stageAverage_at_zeroDual_lower V B u v d r μ hd hu hv j x)
  simpa [mul_comm] using hh

theorem stageAverage_at_primal_zero_nonpos (d r μ : ℝ) (hμ : 0 ≤ μ)
    (j : Fin M) (w : Dual V) : stageAverage V B u v d r μ j (atDual V 0 w) ≤ 0 := by
  have hs : stateProj V j (atDual V 0 w) = 0 := rfl
  have ha : aProj V j (atDual V 0 w) = 0 := rfl
  have hb : bProj V j (atDual V 0 w) = 0 := rfl
  unfold stageAverage
  rw [hs, ha, hb, outerStage_zero, add_zero]
  change (1 / (Fintype.card ι : ℝ)) * ∑ i,
    fullPipeComponent (B j) d r μ 0 0 (fun k ↦ PipeSmoothness.wProj k (pipeProj V j (atDual V 0 w))) i ≤ 0
  rw [fullPipe_average]
  simp only [norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero, mul_zero,
    inner_zero_left, sub_self, zero_add, zero_sub]
  exact neg_nonpos.mpr (mul_nonneg (div_nonneg (beta_pos ι).le (by norm_num))
    (add_nonneg (mul_nonneg hμ (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _))
      (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)))

theorem average_at_primal_zero_nonpos (d r μ : ℝ) (hμ : 0 ≤ μ) (w : Dual V) :
    average V B u v d r μ (atDual V 0 w) ≤ 0 := by
  rw [average_eq_sum]
  exact Finset.sum_nonpos fun j _ ↦ stageAverage_at_primal_zero_nonpos V B u v d r μ hμ j w

theorem average_at_origin (d r μ : ℝ) : average V B u v d r μ (atDual V 0 0) = 0 := by
  simp [average, component, atDual, PipeSmoothness.component, fullPipeComponent, pipeComponent,
    stateProj, aProj, bProj, pipeProj, connectorProj, dualProj, outerStage_zero,
    PipeSmoothness.aProj, PipeSmoothness.bProj, PipeSmoothness.wProj]

/-- The actual value is the supremum of the actual finite-sum average over
the single public Euclidean dual ball. Compactness proves it is attained. -/
def value (d r μ R : ℝ) (x : Primal V) : ℝ :=
  sSup ((fun w ↦ average V B u v d r μ (atDual V x w)) '' Metric.closedBall 0 R)

variable [∀ j k, FiniteDimensional ℝ (V j k)]

theorem value_attained (d r μ R : ℝ) (hR : 0 ≤ R) (x : Primal V) :
    ∃ w ∈ Metric.closedBall (0 : Dual V) R,
      ∀ w' ∈ Metric.closedBall (0 : Dual V) R,
        average V B u v d r μ (atDual V x w') ≤ average V B u v d r μ (atDual V x w) := by
  have hc : ContinuousOn (fun w ↦ average V B u v d r μ (atDual V x w))
      (Metric.closedBall (0 : Dual V) R) := ((average_contDiff V B u v d r μ).continuous.comp
    ((WithLp.prodContinuousLinearEquiv 2 ℝ _ _).symm.continuous.comp
      (continuous_const.prodMk continuous_id))).continuousOn
  obtain ⟨w, hw, hmax⟩ := (isCompact_closedBall (0 : Dual V) R).exists_isMaxOn
    ⟨0, Metric.mem_closedBall_self hR⟩ hc
  exact ⟨w, hw, fun w' hw' ↦ hmax hw'⟩

theorem value_bddAbove (d r μ R : ℝ) (hR : 0 ≤ R) (x : Primal V) :
    BddAbove ((fun w ↦ average V B u v d r μ (atDual V x w)) '' Metric.closedBall 0 R) := by
  obtain ⟨w, hw, hmax⟩ := value_attained V B u v d r μ R hR x
  exact ⟨average V B u v d r μ (atDual V x w), by rintro _ ⟨w', hw', rfl⟩; exact hmax w' hw'⟩

theorem value_lower (d r μ R : ℝ) (hd : 0 ≤ d) (hR : 0 ≤ R)
    (hu : ∀ j, ‖u j‖ = 1) (hv : ∀ j, ‖v j‖ = 1) (x : Primal V) :
    -31000 * M ≤ value V B u v d r μ R x := by
  exact (average_at_zeroDual_lower V B u v d r μ hd hu hv x).trans
    (le_csSup (value_bddAbove V B u v d r μ R hR x)
      ⟨0, Metric.mem_closedBall_self hR, rfl⟩)

theorem value_origin (d r μ R : ℝ) (hμ : 0 ≤ μ) (hR : 0 ≤ R) :
    value V B u v d r μ R 0 = 0 := by
  unfold value
  apply le_antisymm
  · refine csSup_le ?_ ?_
    · exact ⟨average V B u v d r μ (atDual V 0 0), ⟨0, Metric.mem_closedBall_self hR, rfl⟩⟩
    · rintro _ ⟨w, hw, rfl⟩
      exact average_at_primal_zero_nonpos V B u v d r μ hμ w
  · calc
      0 = average V B u v d r μ (atDual V 0 0) := (average_at_origin V B u v d r μ).symm
      _ ≤ _ := le_csSup (value_bddAbove V B u v d r μ R hR 0)
        ⟨0, Metric.mem_closedBall_self hR, rfl⟩

theorem initial_gap (d r μ R : ℝ) (hd : 0 ≤ d) (hμ : 0 ≤ μ) (hR : 0 ≤ R)
    (hu : ∀ j, ‖u j‖ = 1) (hv : ∀ j, ‖v j‖ = 1) :
    value V B u v d r μ R 0 - sInf (Set.range (value V B u v d r μ R)) ≤ 31000 * M := by
  rw [value_origin V B u v d r μ R hμ hR]
  have hlow : -31000 * M ≤ sInf (Set.range (value V B u v d r μ R)) := by
    apply le_csInf (Set.range_nonempty _)
    rintro _ ⟨x, rfl⟩
    exact value_lower V B u v d r μ R hd hR hu hv x
  linarith

end

end NCConcave16991.GlobalHard
