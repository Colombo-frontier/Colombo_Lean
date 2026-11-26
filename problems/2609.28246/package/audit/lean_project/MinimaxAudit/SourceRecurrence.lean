import MinimaxAudit.SourcePotential

/-! The actual signed scalar gradient transports gate-block derivatives along
the directed a-chain and reversed b-chain. No recurrence field is postulated. -/
open scoped RealInnerProductSpace
namespace MinimaxAudit

theorem saddleSign_involutive_source (dx dy : ℕ) :
    Function.Involutive (euclideanSaddleSign dx dy) := by
  intro z
  ext i
  cases i <;> simp [euclideanSaddleSign]

theorem inner_euclideanSaddleSign_swap {dx dy : ℕ} (x y : SaddleSpace dx dy) :
    inner ℝ x (euclideanSaddleSign dx dy y) =
      inner ℝ (euclideanSaddleSign dx dy x) y := by
  have h := (euclideanSaddleSign dx dy).inner_map_map x (euclideanSaddleSign dx dy y)
  simpa [saddleSign_involutive_source dx dy y] using h.symm

section Recurrence
variable {n dx dy : ℕ} {U : Fin (n+1) → Primal dx} {V : Fin (n+1) → Dual dy}
variable (hU : Orthonormal ℝ U) (hV : Orthonormal ℝ V)

/-- First block components are a_i, second components are b_(i+1),
with the terminal second component equal to the seed coordinate b_1. -/
theorem pairedA_signed_synthesis (r : EuclideanSpace ℝ (Fin (n+1) × Fin 2))
    (i : Fin (n+1)) :
    pairedA U V i (euclideanSaddleSign dx dy
      (frameSynthesis (blockPairedFrame_orthonormal hU hV) r)) =
      r ((finRotate (n+1)).symm i, 1) := by
  unfold pairedA
  rw [innerSL_apply_apply, inner_euclideanSaddleSign_swap, saddle_sign_paired_plus]
  have heq : pairedMinus U V i =
      blockPairedFrame U V ((finRotate (n+1)).symm i,1) := by
    rw [blockPairedFrame_second, Equiv.apply_symm_apply]
  rw [heq]
  exact (blockPairedFrame_orthonormal hU hV).inner_right_fintype
    (fun j => r j) ((finRotate (n+1)).symm i,1)

theorem pairedB_signed_synthesis (r : EuclideanSpace ℝ (Fin (n+1) × Fin 2))
    (i : Fin (n+1)) :
    pairedB U V i (euclideanSaddleSign dx dy
      (frameSynthesis (blockPairedFrame_orthonormal hU hV) r)) = r (i,0) := by
  unfold pairedB
  rw [innerSL_apply_apply, inner_euclideanSaddleSign_swap, saddle_sign_paired_minus]
  rw [← blockPairedFrame_first U V i]
  exact (blockPairedFrame_orthonormal hU hV).inner_right_fintype (fun j => r j) (i,0)

theorem inverse_finRotate_zero_source : (finRotate (n+1)).symm (0 : Fin (n+1)) = Fin.last n := by
  apply (finRotate (n+1)).injective
  rw [Equiv.apply_symm_apply, finRotate_last]

theorem inverse_finRotate_succ_source (i : Fin n) :
    (finRotate (n+1)).symm i.succ = i.castSucc := by
  apply (finRotate (n+1)).injective
  rw [Equiv.apply_symm_apply, finRotate_castSucc_source]

noncomputable def sourceTransport (profile : GateProfile) (tau q c : ℝ)
    (z : SaddleSpace dx dy) : SaddleSpace dx dy :=
  euclideanSaddleSign dx dy (frameSynthesis (blockPairedFrame_orthonormal hU hV)
    (chainBlockGradient profile tau q c (Fin.last n)
      (frameAnalysis (blockPairedFrame_orthonormal hU hV) z)))

theorem sourceTransport_a_seed (profile : GateProfile) (tau q c : ℝ)
    (z : SaddleSpace dx dy) : pairedA U V 0 (sourceTransport hU hV profile tau q c z) = c := by
  rw [sourceTransport, pairedA_signed_synthesis hU hV, inverse_finRotate_zero_source]
  simp [chainBlockGradient, chainUnscaledGradient, chainModuleGradient, terminalGateGradient]

theorem sourceTransport_a_step (profile : GateProfile) {tau : ℝ} (htau : tau ≠ 0)
    (q c : ℝ) (z : SaddleSpace dx dy) (i : Fin n) :
    pairedA U V i.succ (sourceTransport hU hV profile tau q c z) =
      q * deriv (fun b => scalarGate profile tau (pairedA U V i.castSucc z) b)
        (pairedB U V i.succ z) := by
  rw [sourceTransport, pairedA_signed_synthesis hU hV, inverse_finRotate_succ_source]
  rw [(scalarGate_partial_b profile htau _ _).deriv]
  have hi : i.castSucc ≠ Fin.last n := by
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  simp [chainBlockGradient, chainUnscaledGradient, chainModuleGradient, hi,
    scalarGateGradient, gateBlockVector, pairedA, pairedB, innerSL_apply_apply,
    finRotate_castSucc_source]

theorem sourceTransport_b_step (profile : GateProfile) {tau : ℝ} (htau : tau ≠ 0)
    (q c : ℝ) (z : SaddleSpace dx dy) (i : Fin n) :
    pairedB U V i.castSucc (sourceTransport hU hV profile tau q c z) =
      q * deriv (fun a => scalarGate profile tau a (pairedB U V i.succ z))
        (pairedA U V i.castSucc z) := by
  rw [sourceTransport, pairedB_signed_synthesis hU hV]
  rw [(scalarGate_partial_a profile htau _ _).deriv]
  have hi : i.castSucc ≠ Fin.last n := by
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  simp [chainBlockGradient, chainUnscaledGradient, chainModuleGradient, hi,
    scalarGateGradient, gateBlockVector, pairedA, pairedB, innerSL_apply_apply,
    finRotate_castSucc_source]

theorem sourceTransport_b_terminal (profile : GateProfile) (tau q c : ℝ)
    (z : SaddleSpace dx dy) :
    pairedB U V (Fin.last n) (sourceTransport hU hV profile tau q c z) =
      q * gate profile tau (pairedA U V (Fin.last n) z) := by
  rw [sourceTransport, pairedB_signed_synthesis hU hV]
  simp [chainBlockGradient, chainUnscaledGradient, chainModuleGradient,
    terminalGateGradient, gateBlockVector, pairedA, innerSL_apply_apply]

end Recurrence
end MinimaxAudit

namespace MinimaxAudit
section Approximation
variable {n dx dy : ℕ} {U : Fin (n+1) → Primal dx} {V : Fin (n+1) → Dual dy}
variable (hU : Orthonormal ℝ U) (hV : Orthonormal ℝ V)

theorem sourceTransport_a_step_error (profile : GateProfile) {tau q : ℝ}
    (htau : 0 < tau) (hq : 0 ≤ q) (c : ℝ) (z : SaddleSpace dx dy) (i : Fin n) :
    |pairedA U V i.succ (sourceTransport hU hV profile tau q c z) -
      q * pairedA U V i.castSucc z| ≤ q * tau := by
  rw [sourceTransport_a_step hU hV profile htau.ne' q c z i, ← mul_sub,
    abs_mul, abs_of_nonneg hq]
  exact mul_le_mul_of_nonneg_left
    (scalarGate_partial_b_error profile htau (pairedA U V i.castSucc z) (pairedB U V i.succ z)) hq

theorem sourceTransport_b_step_error (profile : GateProfile) {tau q : ℝ}
    (htau : 0 < tau) (hq : 0 ≤ q) (c : ℝ) (z : SaddleSpace dx dy) (i : Fin n) :
    |pairedB U V i.castSucc (sourceTransport hU hV profile tau q c z) -
      q * pairedB U V i.succ z| ≤ q * tau := by
  rw [sourceTransport_b_step hU hV profile htau.ne' q c z i, ← mul_sub,
    abs_mul, abs_of_nonneg hq]
  exact mul_le_mul_of_nonneg_left
    (scalarGate_partial_a_error profile htau (pairedA U V i.castSucc z) (pairedB U V i.succ z)) hq

theorem sourceTransport_b_terminal_error (profile : GateProfile) {tau q : ℝ}
    (htau : 0 < tau) (hq : 0 ≤ q) (c : ℝ) (z : SaddleSpace dx dy) :
    |pairedB U V (Fin.last n) (sourceTransport hU hV profile tau q c z) -
      q * pairedA U V (Fin.last n) z| ≤ q * tau := by
  rw [sourceTransport_b_terminal hU hV profile tau q c z, ← mul_sub,
    abs_mul, abs_of_nonneg hq]
  have h := (gate_basic_bounds profile htau (pairedA U V (Fin.last n) z)).2.2.2.1
  rw [abs_sub_comm] at h
  exact mul_le_mul_of_nonneg_left h hq

end Approximation
end MinimaxAudit
