import NCConcave16991.GlobalHardGap
import Mathlib.Analysis.Convex.Strong
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Normed.Module.Convex

/-! # Global strong dual concavity of the literal Appendix E average -/

noncomputable section

open Set
open scoped BigOperators InnerProductSpace

namespace NCConcave16991.GlobalHard

set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {M N : ℕ} (V : Fin M → Fin (N + 1) → Type*)
  [∀ j k, NormedAddCommGroup (V j k)] [∀ j k, InnerProductSpace ℝ (V j k)]
  [∀ j k, CompleteSpace (V j k)]
variable (B : ∀ j : Fin M, ∀ t : Fin N,
  BranchGeometry.BranchFamily (ι := ι) (V j t.castSucc) (V j t.succ))
  (u : ∀ j, V j 0) (v : ∀ j, V j (Fin.last N))

def dualLayer (j : Fin M) (k : Fin (N + 1)) : Dual V →L[ℝ] V j k :=
  (PiLp.proj 2 (V j) k).comp (PiLp.proj 2 _ j)

def dualEdge (j : Fin M) (t : Fin N) : Dual V →L[ℝ] V j t.succ :=
  dualLayer V j t.succ -
    ((B j t).normalizedIsometry.toContinuousLinearMap.comp (dualLayer V j t.castSucc))

def dualLinear (r : ℝ) (x : Primal V) : Dual V →L[ℝ] ℝ :=
  ∑ j, r •
    ((innerSL ℝ (aProj V j (atDual V x 0))).comp (dualLayer V j 0) -
      (innerSL ℝ (bProj V j (atDual V x 0))).comp (dualLayer V j (Fin.last N)))

def dualEdgeEnergy (w : Dual V) : ℝ := ∑ j, ∑ t, ‖dualEdge V B j t w‖ ^ 2

theorem stageAverage_dual_normal_form (d r μ : ℝ) (j : Fin M) (x : Primal V) (w : Dual V) :
    stageAverage V B u v d r μ j (atDual V x w) =
      stageAverage V B u v d r μ j (atDual V x 0) +
        r * (⟪aProj V j (atDual V x 0), dualLayer V j 0 w⟫_ℝ -
          ⟪bProj V j (atDual V x 0), dualLayer V j (Fin.last N) w⟫_ℝ) -
        BranchGeometry.beta ι / 2 * (μ * (∑ k, ‖dualLayer V j k w‖ ^ 2) +
          ∑ t, ‖dualEdge V B j t w‖ ^ 2) := by
  have hpipe (w : Dual V) :
      (1 / (Fintype.card ι : ℝ)) * ∑ i,
        PipeSmoothness.component (B j) d r μ i (pipeProj V j (atDual V x w)) =
      d * (‖aProj V j (atDual V x 0)‖ ^ 2 + ‖bProj V j (atDual V x 0)‖ ^ 2) +
        r * (⟪aProj V j (atDual V x 0), dualLayer V j 0 w⟫_ℝ -
          ⟪bProj V j (atDual V x 0), dualLayer V j (Fin.last N) w⟫_ℝ) -
        BranchGeometry.beta ι / 2 * (μ * (∑ k, ‖dualLayer V j k w‖ ^ 2) +
          ∑ t, ‖dualEdge V B j t w‖ ^ 2) := by
    convert BranchGeometry.fullPipe_average (B j) d r μ
      (aProj V j (atDual V x 0)) (bProj V j (atDual V x 0))
      (fun k ↦ dualLayer V j k w) using 1
    · rfl
    · simp only [dualEdge, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply]
      rfl
  unfold stageAverage
  rw [hpipe w, hpipe 0]
  have hout : outerStage (u j) (v j) (precedingScore V v j (atDual V x w))
      (stateProj V j (atDual V x w)) (aProj V j (atDual V x w)) (bProj V j (atDual V x w)) =
      outerStage (u j) (v j) (precedingScore V v j (atDual V x 0))
      (stateProj V j (atDual V x 0)) (aProj V j (atDual V x 0)) (bProj V j (atDual V x 0)) := rfl
  rw [hout]
  simp only [map_zero, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    Finset.sum_const_zero, inner_zero_right, sub_zero, mul_zero, zero_add, add_zero]
  ring

theorem dualLayer_norm_sum (w : Dual V) :
    (∑ j, ∑ k, ‖dualLayer V j k w‖ ^ 2) = ‖w‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_congr rfl
  intro j _
  rw [PiLp.norm_sq_eq_of_L2]
  rfl

theorem average_dual_normal_form (d r μ : ℝ) (x : Primal V) (w : Dual V) :
    average V B u v d r μ (atDual V x w) =
      average V B u v d r μ (atDual V x 0) + dualLinear V r x w -
        BranchGeometry.beta ι * μ / 2 * ‖w‖ ^ 2 -
        BranchGeometry.beta ι / 2 * dualEdgeEnergy V B w := by
  rw [average_eq_sum, average_eq_sum]
  have hsum := Finset.sum_congr rfl
    (fun j (_ : j ∈ (Finset.univ : Finset (Fin M))) ↦
      stageAverage_dual_normal_form V B u v d r μ j x w)
  rw [hsum]
  have hlinear : (∑ j, r * (⟪aProj V j (atDual V x 0), dualLayer V j 0 w⟫_ℝ -
      ⟪bProj V j (atDual V x 0), dualLayer V j (Fin.last N) w⟫_ℝ)) = dualLinear V r x w := by
    simp only [dualLinear, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply, smul_eq_mul]
  have hmass : (∑ j, BranchGeometry.beta ι / 2 *
      (μ * (∑ k, ‖dualLayer V j k w‖ ^ 2) + ∑ t, ‖dualEdge V B j t w‖ ^ 2)) =
      BranchGeometry.beta ι * μ / 2 * ‖w‖ ^ 2 +
        BranchGeometry.beta ι / 2 * dualEdgeEnergy V B w := by
    simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [dualLayer_norm_sum]
    unfold dualEdgeEnergy
    ring
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hlinear, hmass]
  ring

private theorem convex_norm_sq_clm {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (A : E →L[ℝ] F) :
    ConvexOn ℝ univ (fun x ↦ ‖A x‖ ^ 2) := by
  have h : ConvexOn ℝ univ (fun y : F ↦ ‖y‖ ^ 2) :=
    convexOn_univ_norm.pow (fun y _ ↦ norm_nonneg y) 2
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  change ‖A (a • x + b • y)‖ ^ 2 ≤ a • ‖A x‖ ^ 2 + b • ‖A y‖ ^ 2
  rw [map_add, map_smul, map_smul]
  exact h.2 (mem_univ _) (mem_univ _) ha hb hab

private theorem convex_sum_univ {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fintype I] (f : I → E → ℝ) (hf : ∀ i, ConvexOn ℝ univ (f i)) :
    ConvexOn ℝ univ (fun x ↦ ∑ i, f i x) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  simpa only [smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib] using
    (Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset I)) ↦ (hf i).2 hx hy ha hb hab))

theorem dualEdgeEnergy_convex : ConvexOn ℝ univ (dualEdgeEnergy V B) :=
  convex_sum_univ _ (fun j ↦ convex_sum_univ _ (fun t ↦ convex_norm_sq_clm (dualEdge V B j t)))

theorem average_dual_stronglyConcave (d r μ : ℝ) (x : Primal V) :
    StrongConcaveOn univ (BranchGeometry.beta ι * μ)
      (fun w : Dual V ↦ average V B u v d r μ (atDual V x w)) := by
  rw [strongConcaveOn_iff_convex]
  have hlin : ConcaveOn ℝ univ (fun w : Dual V ↦ dualLinear V r x w) := by
    refine ⟨convex_univ, ?_⟩
    intro w hw w' hw' a b ha hb hab
    simp only [map_add, map_smul, smul_eq_mul]
    exact le_rfl
  have he := (dualEdgeEnergy_convex V B).neg.smul
    (div_nonneg (BranchGeometry.beta_pos ι).le (by norm_num : (0 : ℝ) ≤ 2))
  have hh := (hlin.add_const (average V B u v d r μ (atDual V x 0))).add he
  convert hh using 1
  funext w
  rw [average_dual_normal_form]
  simp only [Pi.add_apply, Pi.neg_apply, smul_eq_mul]
  ring

theorem average_dual_concave (d r μ : ℝ) (hμ : 0 ≤ μ) (x : Primal V) :
    ConcaveOn ℝ univ (fun w : Dual V ↦ average V B u v d r μ (atDual V x w)) := by
  have h := StrongConcaveOn.mono (mul_nonneg (BranchGeometry.beta_pos ι).le hμ)
    (average_dual_stronglyConcave V B u v d r μ x)
  exact strongConcaveOn_zero.mp h

end NCConcave16991.GlobalHard
