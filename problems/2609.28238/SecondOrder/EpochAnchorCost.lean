import SecondOrder.IdealEpochs
import SecondOrder.ChordQueries

open MeasureTheory
open scoped Classical BigOperators

namespace SecondOrder
noncomputable section

abbrev AnchorSlot (P : Parameters) (ρ δ : ℝ) :=
  Fin (confidenceRepeats δ) × Fin (localBatchSize (P.gradientNoise^2) ρ)

def anchorSampleCall {Ω : Type*} {d : ℕ} (P : Parameters) (x : Point d) (ρ δ : ℝ)
    (w : LocalDraws Ω (P.gradientNoise^2) ρ δ) (i : AnchorSlot P ρ δ) : Ω × HvpQuery d :=
  (drawsVector id (localBatchSize (P.gradientNoise^2) ρ)
    (drawsVector id (confidenceRepeats δ) w i.1) i.2,.grad x)

theorem anchorSampleCall_count (P : Parameters) (ρ δ : ℝ) :
    Fintype.card (AnchorSlot P ρ δ) = localQueryCount (P.gradientNoise^2) ρ δ := by
  simp [AnchorSlot,localQueryCount,Nat.mul_comm]

theorem gradientAnchor_eq_query_average {Ω : Type*} {d : ℕ} (P : Parameters)
    (f : Ω → Point d → ℝ) (x : Point d) (ρ δ : ℝ) (w : LocalDraws Ω (P.gradientNoise^2) ρ δ) :
    gradientAnchor P f x ρ δ w = robustCenter (confidenceRepeats_pos δ)
      (fun j => ((localBatchSize (P.gradientNoise^2) ρ : ℕ) : ℝ)⁻¹ •
        ∑ i : Fin (localBatchSize (P.gradientNoise^2) ρ),
          hvpReply f (anchorSampleCall P x ρ δ w (j,i)).1 (anchorSampleCall P x ρ δ w (j,i)).2) (ρ/3) := by
  change robustBatch (fun z => gradient (f z) x) (localBatchSize (P.gradientNoise^2) ρ)
    (confidenceRepeats_pos δ) ρ w = _
  rw [robustBatch_eq_sample_average]
  rfl

def idealAnchorQueryCount {d M : ℕ} (P : Parameters) (q : ℕ) (L s ρ δ : ℝ)
    (policy : IdealPolicy d) (w : Fin M → Bool) : ℕ :=
  idealAnchorCount q L s policy w*localQueryCount (P.gradientNoise^2) ρ δ

variable {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ] {d : ℕ}
  {μ : Measure Ω} {η : Measure Ξ} [IsProbabilityMeasure μ] [IsProbabilityMeasure η]
  {P : Parameters} {ν : ℝ} {F : Point d → ℝ} {f : Ω → Point d → ℝ}

/-- Initial plus refresh anchor work along an actual valid execution.
The frequency depends on gradient moves, so it introduces no curvature
move factor into the leading stochastic-gradient sampling term. -/
theorem CommonLoss.idealAnchorQueryCount_integral (h : CommonLoss μ P ν F f)
    {q : ℕ} (hq : 0 < q) {τ γ ρ δ : ℝ} (hτ : 0 < τ) (hγ : 0 < γ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {policy : Ξ → IdealPolicy d} (hm : MeasurableIdealPolicy policy)
    (hv : ∀ ξ, ValidIdealPolicy F P.gradientLip (curvatureRadius P.hessianHolder ν γ) τ γ (policy ξ))
    (M : ℕ) :
    let cost := fun w : Ξ × (Fin M → Bool) =>
      (idealAnchorQueryCount P q P.gradientLip (curvatureRadius P.hessianHolder ν γ) ρ δ (policy w.1) w.2 : ℝ)
    Integrable cost (η.prod (signLaw M)) ∧
      (∫ w, cost w ∂η.prod (signLaw M)) ≤
        (1+(P.gap*P.gradientLip/τ^2)/(q : ℝ))*
          ((36*P.gradientNoise^2/ρ^2+2)*(8*Real.log (1/δ)+2)) := by
  dsimp only
  have hc := h.idealAnchorCount_integral (η := η) hq hτ hγ hm hv M
  have hi := hc.1.mul_const (localQueryCount (P.gradientNoise^2) ρ δ : ℝ)
  refine ⟨?_, ?_⟩
  · simpa only [idealAnchorQueryCount,Nat.cast_mul] using hi
  · simp only [idealAnchorQueryCount,Nat.cast_mul]
    rw [integral_mul_const]
    apply (mul_le_mul_of_nonneg_right hc.2 (Nat.cast_nonneg _)).trans
    apply mul_le_mul_of_nonneg_left (anchor_query_count P hδ hδ1)
    have hΔ := P.gap_pos
    have hL := P.gradientLip_pos
    positivity

end
end SecondOrder
