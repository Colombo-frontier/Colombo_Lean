import SecondOrder.MinimaxComplexity

open scoped ENNReal

namespace SecondOrder
noncomputable section

theorem HvpBudgetFeasible.to_rich {P : Parameters} {d N : ℕ} {ε γ : ℝ}
    (h : HvpBudgetFeasible P 1 d ε γ N) (σ₀ : ℝ) : RichBudgetFeasible P σ₀ d ε γ N := by
  obtain ⟨Ξ,S,mΞ,mS,μ,hμ,alg,hm,hs⟩ := h
  exact ⟨Ξ,S,mΞ,mS,μ,hμ,(fun ξ => hvpAlgorithmRich (alg ξ)),
    hvpAlgorithmRich_measurable alg hm,hvpSolves_to_rich μ alg P σ₀ ε γ N hs⟩

/-- Full rich responses can simulate every fresh gradient/HVP algorithm
without changing its deterministic budget or success probability. -/
theorem richMinimaxComplexity_le_hvp (P : Parameters) (σ₀ : ℝ) (d : ℕ) (ε γ : ℝ) :
    richMinimaxComplexity P σ₀ d ε γ≤hvpMinimaxComplexity P 1 d ε γ := by
  apply le_iInf
  intro N
  apply le_iInf
  intro hN
  exact richMinimaxComplexity_le_budget P σ₀ d ε γ N (hN.to_rich σ₀)

theorem richEnvelopeComplexity_le_hvp (P : Parameters) (σ₀ κ ε γ : ℝ) :
    richEnvelopeComplexity P σ₀ κ ε γ≤hvpEnvelopeComplexity P 1 κ ε γ := by
  apply iSup_le
  intro d
  apply iSup_le
  intro hd
  exact (richMinimaxComplexity_le_hvp P σ₀ d ε γ).trans
    (hvpMinimaxComplexity_le_envelope P 1 κ ε γ d hd.1 hd.2)

end
end SecondOrder
