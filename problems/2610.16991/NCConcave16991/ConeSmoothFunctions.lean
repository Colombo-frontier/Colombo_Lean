import NCConcave16991.ConeValueComponents
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-! # Smoothness of the literal cone component functions

This file proves actual infinite differentiability. The quantitative uniform
Hessian bound needed for individual smoothness is a separate theorem.
-/

noncomputable section

namespace NCConcave16991.ConeSmooth

open ConePrimitives ConeRadial ConeClockGap ConeValue
open scoped ContDiff InnerProductSpace BigOperators Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem zeta_contDiff : ContDiff ℝ ∞ (zeta : E → E) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst x
    apply contDiffAt_id.congr_of_eventuallyEq
    filter_upwards [Metric.ball_mem_nhds (0 : E) (by norm_num : (0 : ℝ) < 2)] with z hz
    apply zeta_identity
    exact le_of_lt (by simpa using hz)
  · have hn : ContDiffAt ℝ ∞ (fun z : E ↦ ‖z‖) x := contDiffAt_norm ℝ hx
    exact ((capLength_contDiff.contDiffAt.comp x hn).div hn
      (norm_ne_zero_iff.mpr hx)).smul contDiffAt_id

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem perpendicular_contDiff (v : E) : ContDiff ℝ ∞ (perpendicular v) := by
  have hi : ContDiff ℝ ∞ (fun u : E ↦ ⟪u, v⟫_ℝ) := contDiff_id.inner ℝ contDiff_const
  exact contDiff_id.sub (hi.smul contDiff_const)

theorem clock_contDiff {q : ℝ} (v : E) {Z U : F → E}
    (hZ : ContDiff ℝ ∞ Z) (hU : ContDiff ℝ ∞ U) :
    ContDiff ℝ ∞ (fun x ↦ clock q v (Z x) (U x)) := by
  have hu := hU.norm_sq ℝ
  have hs := (contDiff_const.add hu).sqrt (fun x ↦ by positivity : ∀ x, (1 : ℝ) + ‖U x‖ ^ 2 ≠ 0)
  have hp := ((perpendicular_contDiff v).comp hU).norm_sq ℝ
  have hsp := (contDiff_const.add hp).sqrt
    (fun x ↦ by positivity : ∀ x, (1 : ℝ) + ‖perpendicular v (U x)‖ ^ 2 ≠ 0)
  have ht := hU.inner ℝ (contDiff_const (c := v))
  have hzi := (zeta_contDiff.comp hZ).inner ℝ (contDiff_const (c := v))
  have hH : ContDiff ℝ ∞ (fun x ↦ latch ⟪zeta (Z x), v⟫_ℝ) :=
    omega_contDiff.comp ((contDiff_const.mul hzi).sub contDiff_const)
  have ha : ContDiff ℝ ∞ (fun x ↦ ⟪U x, v⟫_ℝ - Real.sqrt (1 + ‖perpendicular v (U x)‖ ^ 2) +
      4 * latch ⟪zeta (Z x), v⟫_ℝ) := (ht.sub hsp).add (contDiff_const.mul hH)
  exact ((hs.sub contDiff_const).add (hu.div_const (2 * q))).sub
    (contDiff_const.mul (theta_contDiff.comp ha))

theorem exitGate_contDiff {q : ℝ} (hq : q ≠ 0) (v : E) :
    ContDiff ℝ ∞ (exitGate q v) := by
  have hp := (perpendicular_contDiff v).norm_sq ℝ
  have hs := (contDiff_const.add hp).sqrt
    (fun x ↦ by have hh := sq_pos_of_ne_zero hq; positivity : ∀ x, q ^ 2 + ‖perpendicular v x‖ ^ 2 ≠ 0)
  have ht : ContDiff ℝ ∞ (fun x : E ↦ ⟪x, v⟫_ℝ) := contDiff_id.inner ℝ (contDiff_const (c := v))
  exact omega_contDiff.comp (((ht.sub hs).div_const q).sub contDiff_const)

variable {n M : ℕ}

theorem component_contDiff {q : ℝ} (hq : q ≠ 0) (R : ℝ)
    (w : Fin n → Fin (M + 1) → E) (i : Fin n) :
    ContDiff ℝ ∞ (jointComponent (M := M) R q w i) := by
  have hz (j : Fin (M + 1)) : ContDiff ℝ ∞ (fun x : JointBlocks E M ↦ x.fst.fst j) :=
    ((PiLp.proj 2 (fun _ : Fin (M + 1) ↦ E) j).comp
      ((WithLp.fstL 2 ℝ (Blocks E M) (Blocks E M)).comp
        (WithLp.fstL 2 ℝ (PrimalBlocks E M) (Blocks E M)))).contDiff
  have hu (j : Fin (M + 1)) : ContDiff ℝ ∞ (fun x : JointBlocks E M ↦ x.fst.snd j) :=
    ((PiLp.proj 2 (fun _ : Fin (M + 1) ↦ E) j).comp
      ((WithLp.sndL 2 ℝ (Blocks E M) (Blocks E M)).comp
        (WithLp.fstL 2 ℝ (PrimalBlocks E M) (Blocks E M)))).contDiff
  have hy (j : Fin (M + 1)) : ContDiff ℝ ∞ (fun x : JointBlocks E M ↦ x.snd j) :=
    ((PiLp.proj 2 (fun _ : Fin (M + 1) ↦ E) j).comp
      (WithLp.sndL 2 ℝ (PrimalBlocks E M) (Blocks E M))).contDiff
  have hgate (j : Fin (M + 1)) :
      ContDiff ℝ ∞ (fun x : JointBlocks E M ↦ previousGate q (sourceMean w) (fun j ↦ x.fst.snd j) j) := by
    unfold previousGate
    split
    · exact contDiff_const
    · exact (exitGate_contDiff hq _).comp (hu _)
  have hc : ContDiff ℝ ∞ (fun x : JointBlocks E M ↦ clockGuard q (sourceMean w) x.fst.fst x.fst.snd) := by
    exact ContDiff.sum (fun j _ ↦ (clock_contDiff (sourceMean w j) (hz j) (hu j)).add
      ((guard_contDiff 3000).comp (hz j)))
  have hs : ContDiff ℝ ∞ (fun x : JointBlocks E M ↦ ∑ j,
      previousGate q (sourceMean w) (fun j ↦ x.fst.snd j) j *
        ⟪zeta (x.fst.fst j) - Real.sqrt (n : ℝ) • w i j, x.snd j⟫_ℝ) :=
    ContDiff.sum (fun j _ ↦ (hgate j).mul
      (((zeta_contDiff.comp (hz j)).sub contDiff_const).inner ℝ (hy j)))
  exact hc.add (contDiff_const.mul hs)

end NCConcave16991.ConeSmooth
