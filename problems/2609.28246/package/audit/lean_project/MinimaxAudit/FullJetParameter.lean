import MinimaxAudit.JetParameter

/-! Joint measurability of every derivative of the actual full scalar
potential, including the terminal module, before sampling its frames. -/
open Set MeasureTheory
open scoped ContDiff
namespace MinimaxAudit.Randomized
open Deterministic
noncomputable section
variable {N dx dy : ℕ}
set_option maxHeartbeats 600000

theorem hardPotential_joint_contDiff
    (profile : GateProfile) {tau : ℝ} (htau : tau ≠ 0) (lam c q : ℝ) :
    ContDiff ℝ ∞ (fun z : FrameParameters N dx dy × SaddleSpace dx dy =>
      hardPotential profile tau lam c q z.1.1 z.1.2 z.2) := by
  have hsum : ContDiff ℝ ∞ (fun z : FrameParameters N dx dy × SaddleSpace dx dy =>
      ∑ i : Fin N, scalarGate profile tau
        (plusForm z.1.1 z.1.2 i.castSucc z.2) (minusForm z.1.1 z.1.2 i.succ z.2)) := by
    apply ContDiff.sum
    intro i hi
    exact (scalarGate_contDiff profile htau).comp
      ((joint_plusForm_contDiff (N := N) (dx := dx) (dy := dy) i.castSucc).prodMk
        (joint_minusForm_contDiff (N := N) (dx := dx) (dy := dy) i.succ))
  have hterminal : ContDiff ℝ ∞ (fun z : FrameParameters N dx dy × SaddleSpace dx dy =>
      doubleGate profile tau (plusForm z.1.1 z.1.2 (Fin.last N) z.2)) :=
    (doubleGate_contDiff profile htau).comp
      (joint_plusForm_contDiff (N := N) (dx := dx) (dy := dy) (Fin.last N))
  have hseed : ContDiff ℝ ∞ (fun z : FrameParameters N dx dy × SaddleSpace dx dy =>
      c * minusForm z.1.1 z.1.2 0 z.2) := contDiff_const.mul
        (joint_minusForm_contDiff (N := N) (dx := dx) (dy := dy) 0)
  have hscaledSum : ContDiff ℝ ∞ (fun z : FrameParameters N dx dy × SaddleSpace dx dy =>
      q * ∑ i : Fin N, scalarGate profile tau
        (plusForm z.1.1 z.1.2 i.castSucc z.2) (minusForm z.1.1 z.1.2 i.succ z.2)) :=
    contDiff_const.mul hsum
  have hscaledTerminal : ContDiff ℝ ∞ (fun z : FrameParameters N dx dy × SaddleSpace dx dy =>
      q * doubleGate profile tau (plusForm z.1.1 z.1.2 (Fin.last N) z.2)) :=
    contDiff_const.mul hterminal
  exact contDiff_const.mul
    ((((joint_publicQuadratic_contDiff (N := N) (dx := dx) (dy := dy)).sub hseed).sub
      hscaledSum).sub hscaledTerminal)

theorem fullScalarJet_jointlyContinuous
    (profile : GateProfile) {tau : ℝ} (htau : tau ≠ 0) (lam c q : ℝ) (p : ℕ) :
    Continuous (fun z : FrameParameters N dx dy × SaddleSpace dx dy =>
      exactScalarJet p (hardPotential profile tau lam c q z.1.1 z.1.2) z.2) := by
  apply continuous_pi
  intro k
  exact (joint_contDiff_partial_iteratedFDeriv
    (P := FrameParameters N dx dy) (E := SaddleSpace dx dy) (F := ℝ)
    (fun params : FrameParameters N dx dy => hardPotential profile tau lam c q params.1 params.2)
    (hardPotential_joint_contDiff (N := N) (dx := dx) (dy := dy) profile htau lam c q) k.1).continuous

theorem fullScalarJet_jointlyMeasurable
    (profile : GateProfile) {tau : ℝ} (htau : tau ≠ 0) (lam c q : ℝ) (p : ℕ) :
    Measurable (fun z : FrameParameters N dx dy × SaddleSpace dx dy =>
      exactScalarJet p (hardPotential profile tau lam c q z.1.1 z.1.2) z.2) := by
  letI : BorelSpace (ScalarJet p (SaddleSpace dx dy)) := ⟨rfl⟩
  exact (fullScalarJet_jointlyContinuous profile htau lam c q p).measurable

end
end MinimaxAudit.Randomized
