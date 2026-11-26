import SecondOrder.RayleighValidation
import SecondOrder.ChordQueries

open scoped Classical BigOperators InnerProductSpace

namespace SecondOrder
noncomputable section

abbrev RayleighSlot (P : Parameters) (ρ δ : ℝ) :=
  Fin (confidenceRepeats δ) × Fin (localBatchSize (P.hessianBound^2) ρ)

def rayleighSampleCall {Ω : Type*} {d : ℕ} (P : Parameters) (x v : Point d) (ρ δ : ℝ)
    (w : LocalDraws Ω (P.hessianBound^2) ρ δ) (i : RayleighSlot P ρ δ) : Ω × HvpQuery d :=
  (drawsVector id (localBatchSize (P.hessianBound^2) ρ)
    (drawsVector id (confidenceRepeats δ) w i.1) i.2,.hvp x v)

theorem rayleighSampleCall_count (P : Parameters) (ρ δ : ℝ) :
    Fintype.card (RayleighSlot P ρ δ) = localQueryCount (P.hessianBound^2) ρ δ := by
  simp [RayleighSlot, localQueryCount, Nat.mul_comm]

/-- Every observation used in the scalar robust estimate is a permitted
HVP at the candidate point and direction. No full Hessian reply is used. -/
theorem rayleighEstimate_eq_query_average {Ω : Type*} {d : ℕ} (P : Parameters)
    (f : Ω → Point d → ℝ) (x v : Point d) (ρ δ : ℝ) (w : LocalDraws Ω (P.hessianBound^2) ρ δ) :
    rayleighEstimate P f x v ρ δ w = robustCenter (confidenceRepeats_pos δ)
      (fun j => ((localBatchSize (P.hessianBound^2) ρ : ℕ) : ℝ)⁻¹ •
        ∑ i : Fin (localBatchSize (P.hessianBound^2) ρ),
          ⟪hvpReply f (rayleighSampleCall P x v ρ δ w (j,i)).1
            (rayleighSampleCall P x v ρ δ w (j,i)).2,v⟫_ℝ) (ρ/3) := by
  change robustBatch (hessianRayleigh f x v) (localBatchSize (P.hessianBound^2) ρ)
    (confidenceRepeats_pos δ) ρ w = _
  rw [robustBatch_eq_sample_average]
  rfl

theorem rayleighEstimate_query_bound (P : Parameters) {ρ δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (localQueryCount (P.hessianBound^2) ρ δ : ℝ) ≤
      (36*P.hessianBound^2/ρ^2+2)*(8*Real.log (1/δ)+2) :=
  robustBatch_query_count (sq_nonneg _) hδ hδ1

theorem rayleighValidation_query_bound (P : Parameters) (γ : ℝ) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (localQueryCount (P.hessianBound^2) (γ/8) δ : ℝ) ≤
      (2304*P.hessianBound^2/γ^2+2)*(8*Real.log (1/δ)+2) := by
  have hb := rayleighEstimate_query_bound (ρ := γ/8) P hδ hδ1
  convert hb using 1 <;> ring

end
end SecondOrder
