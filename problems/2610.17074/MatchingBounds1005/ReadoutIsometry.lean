import MatchingBounds1005.ReadoutPrefixEvent

/-! Stopped readout geometry is invariant under a common orthogonal change
of coordinates for the complete retained query/candidate trace. -/
noncomputable section
open scoped InnerProductSpace BigOperators
namespace MatchingBounds1005.ScheduledPrefix
variable {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] {ι : Type*} {n : ℕ}

theorem synthesis_isometry (I : E ≃ₗᵢ[ℝ] F) (xs : Fin n → E) (t : ℕ) (c : Fin n → ℝ) :
    synthesis (fun i => I (xs i)) t c = I (synthesis xs t c) := by
  simp only [synthesis, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro i _
  simp only [maskedPrefix]
  split_ifs <;> simp

theorem readoutEvent_isometry (I : E ≃ₗᵢ[ℝ] F) (b : ι → E) (ell : ι → ℕ) (θ : ℝ)
    (xs : Fin n → E) :
    (fun i => I (xs i)) ∈ readoutEvent (fun s => I (b s)) ell θ ↔ xs ∈ readoutEvent b ell θ := by
  simp only [readoutEvent, Set.mem_setOf_eq, synthesis_isometry, I.inner_map_map, I.norm_map]

end MatchingBounds1005.ScheduledPrefix
