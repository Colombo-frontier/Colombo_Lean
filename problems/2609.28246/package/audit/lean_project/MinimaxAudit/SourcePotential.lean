import MinimaxAudit.FrameOperators
import MinimaxAudit.ChainGradient
import MinimaxAudit.ScalarJet

/-! Exact equality of the original scalar chain and the orthogonal block ordering. -/
namespace MinimaxAudit

noncomputable def pairedA {n dx dy : ℕ} (U : Fin n → Primal dx) (V : Fin n → Dual dy)
    (i : Fin n) : SaddleSpace dx dy →L[ℝ] ℝ := innerSL ℝ (pairedPlus U V i)
noncomputable def pairedB {n dx dy : ℕ} (U : Fin n → Primal dx) (V : Fin n → Dual dy)
    (i : Fin n) : SaddleSpace dx dy →L[ℝ] ℝ := innerSL ℝ (pairedMinus U V i)

theorem finRotate_castSucc_source {n : ℕ} (i : Fin n) :
    finRotate (n+1) i.castSucc = i.succ := by
  apply Fin.ext
  rw [coe_finRotate_of_ne_last]
  · rfl
  · intro he
    have := congrArg Fin.val he
    simp at this
    omega

theorem framed_block_potential_eq_source {n dx dy : ℕ}
    (profile : GateProfile) (tau q c : ℝ)
    {U : Fin (n+1) → Primal dx} {V : Fin (n+1) → Dual dy}
    (hU : Orthonormal ℝ U) (hV : Orthonormal ℝ V) (z : SaddleSpace dx dy) :
    chainBlockPotential profile tau q c (Fin.last n)
      (frameAnalysis (blockPairedFrame_orthonormal hU hV) z) =
    c * pairedB U V 0 z + q *
      (∑ i : Fin n, scalarGate profile tau (pairedA U V i.castSucc z) (pairedB U V i.succ z)) +
      q * doubleGate profile tau (pairedA U V (Fin.last n) z) := by
  let w := frameAnalysis (blockPairedFrame_orthonormal hU hV) z
  have hw0 (i : Fin (n+1)) : gateBlockVector w i 0 = pairedA U V i z := by
    simp [w, gateBlockVector, pairedA, innerSL_apply_apply]
  have hw1 (i : Fin (n+1)) : gateBlockVector w i 1 = pairedB U V (finRotate (n+1) i) z := by
    simp [w, gateBlockVector, pairedB, innerSL_apply_apply]
  have ht : w (Fin.last n, 1) = pairedB U V 0 z := by
    simp [w, pairedB, innerSL_apply_apply]
  change q * (∑ j : Fin (n+1), chainModulePotential profile tau (Fin.last n) j
    (gateBlockVector w j)) + c * w (Fin.last n,1) = _
  rw [Fin.sum_univ_castSucc]
  have hi (i : Fin n) : i.castSucc ≠ Fin.last n := by
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  simp only [chainModulePotential, if_true]
  simp_rw [if_neg (hi _), hw0, hw1, finRotate_castSucc_source]
  rw [ht]
  ring

/-- The exact scalar potential used for jet hiding is the same scalar
potential used for the block derivative, smoothness and fixed-point proofs. -/
theorem source_chainPotential_eq_block {n dx dy : ℕ}
    (profile : GateProfile) (tau lam q c : ℝ) (base : SaddleSpace dx dy → ℝ)
    {U : Fin (n+1) → Primal dx} {V : Fin (n+1) → Dual dy}
    (hU : Orthonormal ℝ U) (hV : Orthonormal ℝ V) :
    chainPotential profile tau lam c q base (pairedA U V) (pairedB U V) =
      fun z => lam * (base z - chainBlockPotential profile tau q c (Fin.last n)
        (frameAnalysis (blockPairedFrame_orthonormal hU hV) z)) := by
  funext z
  rw [framed_block_potential_eq_source profile tau q c hU hV z]
  simp only [chainPotential]
  ring

end MinimaxAudit
