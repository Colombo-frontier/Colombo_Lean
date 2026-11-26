import MinimaxAudit.PotentialApproximation

/-! Both conclusions of the source uniform potential approximation lemma. -/
namespace MinimaxAudit
noncomputable def sourceIdealPsi {n dx dy : ℕ} (q c : ℝ)
    (U : Fin (n+1) → Primal dx) (V : Fin (n+1) → Dual dy) (z : SaddleSpace dx dy) : ℝ :=
  c * pairedB U V 0 z + q * (∑ i : Fin n, pairedA U V i.castSucc z * pairedB U V i.succ z) +
    q / 2 * (pairedA U V (Fin.last n) z) ^ 2

theorem uniform_approximation_source {n dx dy : ℕ} (profile : GateProfile)
    {tau lam q R : ℝ} (htau : 0 < tau) (hlam : 0 ≤ lam)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (hR : 0 ≤ R) (c : ℝ)
    {U : Fin (n+1) → Primal dx} {V : Fin (n+1) → Dual dy}
    (hU : Orthonormal ℝ U) (hV : Orthonormal ℝ V)
    (x : Primal dx) (y : Dual dy) (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) :
    |chainBlockPotential profile tau q c (Fin.last n)
      (frameAnalysis (blockPairedFrame_orthonormal hU hV) (joinBlocks x y)) -
      sourceIdealPsi q c U V (joinBlocks x y)| ≤ 3 * tau * R * Real.sqrt (n+1) ∧
    |minimaxHardPotential profile tau lam q c hU hV (joinBlocks x y) -
      idealHardPotential lam q c U V (joinBlocks x y)| ≤
      3 * lam * tau * R * Real.sqrt (n+1) := by
  refine ⟨?_, uniform_product_potential_approximation profile htau hlam hq hq1 hR c hU hV x y hx hy⟩
  have h := uniform_product_potential_approximation profile htau (by norm_num : (0 : ℝ) ≤ 1)
    hq hq1 hR c hU hV x y hx hy
  have he : minimaxHardPotential profile tau 1 q c hU hV (joinBlocks x y) -
      idealHardPotential 1 q c U V (joinBlocks x y) =
      -(chainBlockPotential profile tau q c (Fin.last n)
        (frameAnalysis (blockPairedFrame_orthonormal hU hV) (joinBlocks x y)) -
        sourceIdealPsi q c U V (joinBlocks x y)) := by
    simp only [minimaxHardPotential, framedHardPotential, idealHardPotential, idealScalarValue,
      signedQuadratic_eq_witnessBase, sourceIdealPsi, one_mul]
    ring
  rw [he, abs_neg] at h
  simpa only [mul_one, one_mul] using h
end MinimaxAudit
