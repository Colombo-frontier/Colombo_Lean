import SecondOrder.OracleSuccessProbability

open MeasureTheory

namespace SecondOrder
noncomputable section

/-- One algorithm, with no instance-dependent seed or transition maps,
succeeds on every admissible d-dimensional common-loss instance. -/
def HvpSolves {Ξ S : Type*} [MeasurableSpace Ξ] {d : ℕ}
    (μ : Measure Ξ) (alg : Ξ → HvpAlgorithm d S) (P : Parameters) (ν ε γ : ℝ) (N : ℕ) : Prop :=
  ∀ (Ω : Type) (mΩ : MeasurableSpace Ω) (η : Measure Ω) (_ : IsProbabilityMeasure η)
    (F : Point d → ℝ) (f : Ω → Point d → ℝ),
    CommonLoss η P ν F f → 2/3≤hvpAlgorithmSospProbability μ η alg F f ε γ N

def RichSolves {Ξ S : Type*} [MeasurableSpace Ξ] {d : ℕ}
    (μ : Measure Ξ) (alg : Ξ → RichAlgorithm d S) (P : Parameters) (σ₀ ε γ : ℝ) (N : ℕ) : Prop :=
  ∀ (Ω : Type) (mΩ : MeasurableSpace Ω) (η : Measure Ω) (_ : IsProbabilityMeasure η)
    (F : Point d → ℝ) (f : Ω → Point d → ℝ),
    RichCommonLoss η P σ₀ F f → 2/3≤richAlgorithmSospProbability μ η alg F f ε γ N

theorem hvpSolves_to_rich {Ξ S : Type*} [MeasurableSpace Ξ] {d : ℕ}
    (μ : Measure Ξ) (alg : Ξ → HvpAlgorithm d S) (P : Parameters) (σ₀ ε γ : ℝ) (N : ℕ)
    (h : HvpSolves μ alg P 1 ε γ N) :
    RichSolves μ (fun ξ => hvpAlgorithmRich (alg ξ)) P σ₀ ε γ N := by
  intro Ω mΩ η hη F f hm
  rw [hvpAlgorithmSospProbability_simulation]
  exact h Ω mΩ η hη F f hm.toCommonLoss

end
end SecondOrder
