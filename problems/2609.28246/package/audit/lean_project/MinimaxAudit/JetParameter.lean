import MinimaxAudit.Deterministic
import MinimaxAudit.CriterionFull

/-!
# Concrete randomized scalar-jet information bridge

This module uses the actual smooth scalar potential and the canonical Borel
policy model. The parameter-derivative theorem is general calculus, followed
by the actual paired-coordinate and integral-gate specialization.
-/

open Set MeasureTheory
open scoped ContDiff RealInnerProductSpace ENNReal
namespace MinimaxAudit.Randomized

set_option maxHeartbeats 1600000

noncomputable section

section ParameterCalculus
variable {P E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A jointly smooth family has jointly smooth partial iterated derivatives
in the query variable, of every finite order. -/
theorem joint_contDiff_partial_iteratedFDeriv
    (f : P → E → F) (hf : ContDiff ℝ ∞ (Function.uncurry f)) (n : ℕ) :
    ContDiff ℝ ∞ (fun z : P × E => iteratedFDeriv ℝ n (f z.1) z.2) := by
  induction n with
  | zero =>
    simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_def, Function.uncurry_def] using
      ((continuousMultilinearCurryFin0 ℝ E F).symm.contDiff.comp hf)
  | succ n ih =>
    have hg : ContDiff ℝ ∞ (fun z : (P × E) × E =>
        iteratedFDeriv ℝ n (f z.1.1) z.2) :=
      ih.comp ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd)
    have hd : ContDiff ℝ ∞ (fun z : P × E =>
        fderiv ℝ (iteratedFDeriv ℝ n (f z.1)) z.2) :=
      hg.fderiv contDiff_snd (by simp)
    simpa only [iteratedFDeriv_succ_eq_comp_left, Function.comp_def, Function.uncurry_def] using
      ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) F).symm.contDiff.comp hd)
end ParameterCalculus

open Deterministic

abbrev FrameParameters (N dx dy : ℕ) :=
  (Fin (N + 1) → Primal dx) × (Fin (N + 1) → Dual dy)

section ScalarFamily
variable {N dx dy : ℕ}

theorem joint_plusForm_contDiff (i : Fin (N + 1)) :
    ContDiff ℝ ∞ (fun z : FrameParameters N dx dy × SaddleSpace dx dy =>
      plusForm z.1.1 z.1.2 i z.2) := by
  have hU : ContDiff ℝ ∞ (fun z : FrameParameters N dx dy × SaddleSpace dx dy => z.1.1 i) := by
    fun_prop
  have hV : ContDiff ℝ ∞ (fun z : FrameParameters N dx dy × SaddleSpace dx dy => z.1.2 i) := by
    fun_prop
  have hx : ContDiff ℝ ∞ (fun z : FrameParameters N dx dy × SaddleSpace dx dy => primalBlock z.2) := by
    simpa only [Function.comp_def, primal_projection_apply] using
      ((primalProjection dx dy).contDiff.comp (contDiff_snd :
        ContDiff ℝ ∞ (Prod.snd : FrameParameters N dx dy × SaddleSpace dx dy → SaddleSpace dx dy)))
  have hy : ContDiff ℝ ∞ (fun z : FrameParameters N dx dy × SaddleSpace dx dy => dualBlock z.2) := by
    simpa only [Function.comp_def, dual_projection_apply] using
      ((dualProjection dx dy).contDiff.comp (contDiff_snd :
        ContDiff ℝ ∞ (Prod.snd : FrameParameters N dx dy × SaddleSpace dx dy → SaddleSpace dx dy)))
  have heq : (fun z : FrameParameters N dx dy × SaddleSpace dx dy =>
      plusForm z.1.1 z.1.2 i z.2) = fun z =>
      (inner ℝ (z.1.1 i) (primalBlock z.2) + inner ℝ (z.1.2 i) (dualBlock z.2)) / Real.sqrt 2 := by
    funext z
    change inner ℝ (pairedPlus z.1.1 z.1.2 i) z.2 = _
    conv_lhs => rw [← join_blocks z.2, paired_plus_coordinate]
  rw [heq]
  exact ((hU.inner ℝ hx).add (hV.inner ℝ hy)).div_const _

theorem joint_minusForm_contDiff (i : Fin (N + 1)) :
    ContDiff ℝ ∞ (fun z : FrameParameters N dx dy × SaddleSpace dx dy =>
      minusForm z.1.1 z.1.2 i z.2) := by
  have hU : ContDiff ℝ ∞ (fun z : FrameParameters N dx dy × SaddleSpace dx dy => z.1.1 i) := by
    fun_prop
  have hV : ContDiff ℝ ∞ (fun z : FrameParameters N dx dy × SaddleSpace dx dy => z.1.2 i) := by
    fun_prop
  have hx : ContDiff ℝ ∞ (fun z : FrameParameters N dx dy × SaddleSpace dx dy => primalBlock z.2) := by
    simpa only [Function.comp_def, primal_projection_apply] using
      ((primalProjection dx dy).contDiff.comp (contDiff_snd :
        ContDiff ℝ ∞ (Prod.snd : FrameParameters N dx dy × SaddleSpace dx dy → SaddleSpace dx dy)))
  have hy : ContDiff ℝ ∞ (fun z : FrameParameters N dx dy × SaddleSpace dx dy => dualBlock z.2) := by
    simpa only [Function.comp_def, dual_projection_apply] using
      ((dualProjection dx dy).contDiff.comp (contDiff_snd :
        ContDiff ℝ ∞ (Prod.snd : FrameParameters N dx dy × SaddleSpace dx dy → SaddleSpace dx dy)))
  have heq : (fun z : FrameParameters N dx dy × SaddleSpace dx dy =>
      minusForm z.1.1 z.1.2 i z.2) = fun z =>
      (inner ℝ (z.1.1 i) (primalBlock z.2) - inner ℝ (z.1.2 i) (dualBlock z.2)) / Real.sqrt 2 := by
    funext z
    change inner ℝ (pairedMinus z.1.1 z.1.2 i) z.2 = _
    conv_lhs => rw [← join_blocks z.2, paired_minus_coordinate]
  rw [heq]
  exact ((hU.inner ℝ hx).sub (hV.inner ℝ hy)).div_const _

theorem joint_publicQuadratic_contDiff :
    ContDiff ℝ ∞ (fun z : FrameParameters N dx dy × SaddleSpace dx dy => publicQuadratic z.2) := by
  have hx : ContDiff ℝ ∞ (fun z : FrameParameters N dx dy × SaddleSpace dx dy => primalBlock z.2) := by
    simpa only [Function.comp_def, primal_projection_apply] using
      ((primalProjection dx dy).contDiff.comp (contDiff_snd :
        ContDiff ℝ ∞ (Prod.snd : FrameParameters N dx dy × SaddleSpace dx dy → SaddleSpace dx dy)))
  have hy : ContDiff ℝ ∞ (fun z : FrameParameters N dx dy × SaddleSpace dx dy => dualBlock z.2) := by
    simpa only [Function.comp_def, dual_projection_apply] using
      ((dualProjection dx dy).contDiff.comp (contDiff_snd :
        ContDiff ℝ ∞ (Prod.snd : FrameParameters N dx dy × SaddleSpace dx dy → SaddleSpace dx dy)))
  exact (((contDiff_norm_sq ℝ).comp hx).div_const 2).sub
    (((contDiff_norm_sq ℝ).comp hy).div_const 2)

/-- Smoothness in arbitrary frame entries and the query point, before imposing
orthonormality or sampling Haar matrices. -/
theorem truncatedPotential_joint_contDiff
    (profile : GateProfile) {tau : ℝ} (htau : tau ≠ 0) (lam c q : ℝ) (t : ℕ) :
    ContDiff ℝ ∞ (fun z : FrameParameters N dx dy × SaddleSpace dx dy =>
      truncatedPotential profile tau lam c q t z.1.1 z.1.2 z.2) := by
  have hsum : ContDiff ℝ ∞ (fun z : FrameParameters N dx dy × SaddleSpace dx dy =>
      ∑ i ∈ revealedLinks N t, scalarGate profile tau
        (plusForm z.1.1 z.1.2 i.castSucc z.2) (minusForm z.1.1 z.1.2 i.succ z.2)) := by
    apply ContDiff.sum
    intro i hi
    exact (scalarGate_contDiff profile htau).comp
      ((joint_plusForm_contDiff (N := N) (dx := dx) (dy := dy) i.castSucc).prodMk (joint_minusForm_contDiff (N := N) (dx := dx) (dy := dy) i.succ))
  have hseed : ContDiff ℝ ∞ (fun z : FrameParameters N dx dy × SaddleSpace dx dy =>
      c * minusForm z.1.1 z.1.2 0 z.2) := contDiff_const.mul
        (joint_minusForm_contDiff (N := N) (dx := dx) (dy := dy) 0)
  have hscaledSum : ContDiff ℝ ∞ (fun z : FrameParameters N dx dy × SaddleSpace dx dy =>
      q * ∑ i ∈ revealedLinks N t, scalarGate profile tau
        (plusForm z.1.1 z.1.2 i.castSucc z.2) (minusForm z.1.1 z.1.2 i.succ z.2)) :=
    contDiff_const.mul hsum
  exact contDiff_const.mul
    (((joint_publicQuadratic_contDiff (N := N) (dx := dx) (dy := dy)).sub hseed).sub hscaledSum)

/-- Actual full scalar jet is continuous jointly in frame parameters and point. -/
theorem truncatedScalarJet_jointlyContinuous
    (profile : GateProfile) {tau : ℝ} (htau : tau ≠ 0) (lam c q : ℝ) (t p : ℕ) :
    Continuous (fun z : FrameParameters N dx dy × SaddleSpace dx dy =>
      exactScalarJet p (truncatedPotential profile tau lam c q t z.1.1 z.1.2) z.2) := by
  apply continuous_pi
  intro k
  exact (joint_contDiff_partial_iteratedFDeriv
    (P := FrameParameters N dx dy) (E := SaddleSpace dx dy) (F := ℝ)
    (fun params : FrameParameters N dx dy =>
      truncatedPotential profile tau lam c q t params.1 params.2)
    (truncatedPotential_joint_contDiff (N := N) (dx := dx) (dy := dy)
      profile htau lam c q t) k.1).continuous

/-- Canonical Borel joint measurability, including the objective value at order0. -/
theorem truncatedScalarJet_jointlyMeasurable
    (profile : GateProfile) {tau : ℝ} (htau : tau ≠ 0) (lam c q : ℝ) (t p : ℕ) :
    Measurable (fun z : FrameParameters N dx dy × SaddleSpace dx dy =>
      exactScalarJet p (truncatedPotential profile tau lam c q t z.1.1 z.1.2) z.2) := by
  letI : BorelSpace (ScalarJet p (SaddleSpace dx dy)) := ⟨rfl⟩
  exact (truncatedScalarJet_jointlyContinuous profile htau lam c q t p).measurable

end ScalarFamily

end
end MinimaxAudit.Randomized
