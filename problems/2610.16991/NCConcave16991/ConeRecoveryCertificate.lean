import NCConcave16991.ConeRecoveryResidual
import NCConcave16991.ConeRecoveryClock
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-! # Concrete dual-maximizer source recovery

The hypotheses refer to a literal maximizing unit-ball dual multiplier and
the explicit source-block vectors. A companion derivative interface connects
these blocks to the actual finite-sum branch; no Clarke representation is
assumed here.
-/

noncomputable section

namespace NCConcave16991.ConeRecovery

open ConePrimitives ConeRadial ConeClockGap ConeValue Set Metric
open scoped InnerProductSpace BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {M : ℕ}

def nextCoefficient (v : Fin (M + 1) → E) (z a : Blocks E M) (j : Fin (M + 1)) : ℝ :=
  if h : j.val + 1 < M + 1 then
    ⟪zeta (z ⟨j.val + 1, h⟩) - v ⟨j.val + 1, h⟩, a ⟨j.val + 1, h⟩⟫_ℝ else 0

def multiplierZBlock (q : ℝ) (v : Fin (M + 1) → E) (z u a : Blocks E M) : Blocks E M :=
  WithLp.toLp 2 (fun j ↦ gradient (ConeRadial.guard 3000) (z j) +
    clockZGradient (v j) (z j) (u j) +
      sourceZGradient (previousGate q v (fun j ↦ u j) j) (z j) (a j))

def multiplierUBlock (q : ℝ) (v : Fin (M + 1) → E) (z u a : Blocks E M) : Blocks E M :=
  WithLp.toLp 2 (fun j ↦ clockUGradient q (v j) (z j) (u j) +
    nextCoefficient v z a j • gateUGradient q (v j) (u j))

theorem previousGate_bounds (q : ℝ) (v u : Fin (M + 1) → E) (j : Fin (M + 1)) :
    0 ≤ previousGate q v u j ∧ previousGate q v u j ≤ 1 := by
  unfold previousGate
  split
  · norm_num
  · exact exitGate_bounds _ _ _

theorem nextCoefficient_bound (v : Fin (M + 1) → E) (z a : Blocks E M)
    (hv : ∀ j, ‖v j‖ = 1) (ha : ‖a‖ ≤ 1) (j : Fin (M + 1)) :
    |nextCoefficient v z a j| ≤ 4 := by
  unfold nextCoefficient
  split
  · exact adjacent_source_coefficient_bound _ _ _ (hv _)
      ((PiLp.norm_apply_le (p := 2) a _).trans ha)
  · norm_num

theorem localized_binary_of_small_blocks {q : ℝ} (hq : 16 ≤ q)
    (v : Fin (M + 1) → E) (z u a : Blocks E M) (hv : ∀ j, ‖v j‖ = 1) (ha : ‖a‖ ≤ 1)
    (hzsmall : ‖multiplierZBlock q v z u a‖ ≤ 1 / 1000)
    (husmall : ‖multiplierUBlock q v z u a‖ ≤ 1 / 1000) :
    (∀ j, ‖z j‖ < 2) ∧ (∀ j, exitGate q (v j) (u j) = 0 ∨ exitGate q (v j) (u j) = 1) := by
  constructor
  · intro j
    apply guard_of_small_concrete_block (v j) (z j) (u j) (a j) (hv j)
      (previousGate_bounds q v (fun j ↦ u j) j) ((PiLp.norm_apply_le (p := 2) a j).trans ha)
    exact (PiLp.norm_apply_le (p := 2) (multiplierZBlock q v z u a) j).trans hzsmall
  · intro j
    apply binary_gate_of_small_concrete_block hq (v j) (z j) (u j) (hv j)
      (nextCoefficient v z a j) (nextCoefficient_bound v z a hv ha j)
    exact (PiLp.norm_apply_le (p := 2) (multiplierUBlock q v z u a) j).trans husmall

theorem gate_gradient_zero_of_binary {q : ℝ} (hq : 0 < q) (v u : E) (hv : ‖v‖ = 1)
    (hg : exitGate q v u = 0 ∨ exitGate q v u = 1) : gateUGradient q v u = 0 := by
  have hd := exitGate_hasFDerivAt hq v u hv
  have hzero : innerSL ℝ (gateUGradient q v u) = 0 := by
    rcases hg with hg | hg
    · have hm : IsLocalMin (exitGate q v) u :=
        Filter.Eventually.of_forall (fun x ↦ by rw [hg]; exact (exitGate_bounds q v x).1)
      exact hm.hasFDerivAt_eq_zero hd
    · have hm : IsLocalMax (exitGate q v) u :=
        Filter.Eventually.of_forall (fun x ↦ by rw [hg]; exact (exitGate_bounds q v x).2)
      exact hm.hasFDerivAt_eq_zero hd
  have hi : ⟪gateUGradient q v u, gateUGradient q v u⟫_ℝ = 0 := by
    exact congrArg (fun A : E →L[ℝ] ℝ ↦ A (gateUGradient q v u)) hzero
  exact inner_self_eq_zero.mp hi

theorem previousGate_succ (q : ℝ) (v u : Fin (M + 1) → E) (j : Fin M) :
    previousGate q v u j.succ = exitGate q (v j.castSucc) (u j.castSucc) := by
  unfold previousGate
  simp
  rfl

theorem all_sources_of_zero_residual {q : ℝ} (hq : 1 ≤ q)
    (v : Fin (M + 1) → E) (z u a : Blocks E M) (hv : ∀ j, ‖v j‖ = 1)
    (hz : ∀ j, ‖z j‖ < 2)
    (hg : ∀ j, exitGate q (v j) (u j) = 0 ∨ exitGate q (v j) (u j) = 1)
    (hr : ConeValue.residual q v z u = 0)
    (husmall : ‖multiplierUBlock q v z u a‖ ≤ 1 / 1000) :
    ∀ j, z j = v j ∧ latch ⟪zeta (z j), v j⟫_ℝ = 1 ∧ exitGate q (v j) (u j) = 1 := by
  have hq0 : 0 < q := by linarith
  have finish (j : Fin (M + 1)) (hprev : previousGate q v (fun j ↦ u j) j = 1) :
      z j = v j ∧ latch ⟪zeta (z j), v j⟫_ℝ = 1 ∧ exitGate q (v j) (u j) = 1 := by
    have hrj := congrArg (fun b : Blocks E M ↦ b j) hr
    change previousGate q v (fun j ↦ u j) j • (zeta (z j) - v j) = 0 at hrj
    rw [hprev, one_smul, zeta_identity (hz j).le] at hrj
    have hzj : z j = v j := sub_eq_zero.mp hrj
    have hH : latch ⟪zeta (z j), v j⟫_ℝ = 1 := by
      rw [zeta_identity (hz j).le, hzj, real_inner_self_eq_norm_sq, hv j]
      exact latch_one (by norm_num)
    refine ⟨hzj, hH, ?_⟩
    apply clock_completed hq (v j) (z j) (u j) (hv j) hH
    have hs := (PiLp.norm_apply_le (p := 2) (multiplierUBlock q v z u a) j).trans husmall
    change ‖clockUGradient q (v j) (z j) (u j) + nextCoefficient v z a j •
      gateUGradient q (v j) (u j)‖ ≤ 1 / 1000 at hs
    rw [gate_gradient_zero_of_binary hq0 (v j) (u j) (hv j) (hg j), smul_zero, add_zero] at hs
    linarith
  intro j
  induction j using Fin.induction with
  | zero => exact finish 0 (by simp [previousGate])
  | succ j ih =>
      apply finish j.succ
      rw [previousGate_succ]
      exact ih.2.2

theorem maximizer_support (q : ℝ) (v : Fin (M + 1) → E) (z u a : Blocks E M)
    (ha : ‖a‖ ≤ 1)
    (hmax : ∀ b ∈ closedBall (0 : Blocks E M) 1, branch q v z u b ≤ branch q v z u a) :
    ConeValue.residual q v z u ≠ 0 → a = normalizedResidual q v z u := by
  intro hr
  apply unit_multiplier_eq_normalized hr ha
  obtain ⟨b, hb, he⟩ := ball_affine_attains (by norm_num : (0 : ℝ) < 1)
    (clockGuard q v z u) (ConeValue.residual q v z u)
  have hh := hmax b hb
  simp only [inv_one, one_mul] at he
  rw [branch, branch, he] at hh
  have hu := ball_affine_upper (by norm_num : (0 : ℝ) < 1) (clockGuard q v z u)
    (ConeValue.residual q v z u) a (by simpa only [mem_closedBall, dist_zero_right] using ha)
  simp only [inv_one, one_mul] at hu
  linarith

/-- Every actual maximizing unit-ball branch with small explicit primal
blocks recovers every source exactly. The max condition is literal constrained
optimization, not a Clarke-subgradient representation premise. -/
theorem source_recovery_from_maximizing_branch {q : ℝ} (hq : 16 ≤ q)
    (v : Fin (M + 1) → E) (z u a : Blocks E M) (hv : ∀ j, ‖v j‖ = 1)
    (ha : ‖a‖ ≤ 1)
    (hmax : ∀ b ∈ closedBall (0 : Blocks E M) 1, branch q v z u b ≤ branch q v z u a)
    (hzsmall : ‖multiplierZBlock q v z u a‖ ≤ 1 / 1000)
    (husmall : ‖multiplierUBlock q v z u a‖ ≤ 1 / 1000) :
    ConeValue.residual q v z u = 0 ∧
      ∀ j, z j = v j ∧ latch ⟪zeta (z j), v j⟫_ℝ = 1 ∧ exitGate q (v j) (u j) = 1 := by
  obtain ⟨hz, hg⟩ := localized_binary_of_small_blocks hq v z u a hv ha hzsmall husmall
  have hprev : ∀ j, previousGate q v (fun j ↦ u j) j = 0 ∨
      previousGate q v (fun j ↦ u j) j = 1 := by
    intro j
    unfold previousGate
    split
    · exact Or.inr rfl
    · exact hg _
  have hr : ConeValue.residual q v z u = 0 := by
    by_contra hr
    have he := maximizer_support q v z u a ha hmax hr
    have hblock : multiplierZBlock q v z u a = canonicalZBlock q v z u := by rw [he]; rfl
    rw [hblock] at hzsmall
    have hl := canonicalZBlock_norm_ge_one hv hz hprev hr
    linarith
  exact ⟨hr, all_sources_of_zero_residual (by linarith) v z u a hv hz hg hr husmall⟩

end NCConcave16991.ConeRecovery
