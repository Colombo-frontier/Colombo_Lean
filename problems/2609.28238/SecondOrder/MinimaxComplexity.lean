import SecondOrder.FirstOrderAlgorithmLower
import SecondOrder.CurvatureAlgorithmLower

open MeasureTheory
open scoped ENNReal

namespace SecondOrder
noncomputable section

/-- A fixed deterministic call budget is feasible if one measurable private-
seed algorithm succeeds on every instance; the algorithm is chosen first. -/
def HvpBudgetFeasible (P : Parameters) (ν : ℝ) (d : ℕ) (ε γ : ℝ) (N : ℕ) : Prop :=
  ∃ (Ξ S : Type) (mΞ : MeasurableSpace Ξ) (mS : MeasurableSpace S)
    (μ : Measure Ξ) (_ : IsProbabilityMeasure μ) (alg : Ξ → HvpAlgorithm d S),
    MeasurableOracleAlgorithmFamily alg ∧ HvpSolves μ alg P ν ε γ N

def RichBudgetFeasible (P : Parameters) (σ₀ : ℝ) (d : ℕ) (ε γ : ℝ) (N : ℕ) : Prop :=
  ∃ (Ξ S : Type) (mΞ : MeasurableSpace Ξ) (mS : MeasurableSpace S)
    (μ : Measure Ξ) (_ : IsProbabilityMeasure μ) (alg : Ξ → RichAlgorithm d S),
    MeasurableOracleAlgorithmFamily alg ∧ RichSolves μ alg P σ₀ ε γ N

/-- The infimum of actual integer budgets; it is infinity when none is feasible. -/
def hvpMinimaxComplexity (P : Parameters) (ν : ℝ) (d : ℕ) (ε γ : ℝ) : ℝ≥0∞ :=
  ⨅ (N : ℕ) (_ : HvpBudgetFeasible P ν d ε γ N), (N:ℝ≥0∞)

def richMinimaxComplexity (P : Parameters) (σ₀ : ℝ) (d : ℕ) (ε γ : ℝ) : ℝ≥0∞ :=
  ⨅ (N : ℕ) (_ : RichBudgetFeasible P σ₀ d ε γ N), (N:ℝ≥0∞)

theorem hvpMinimaxComplexity_le_budget (P : Parameters) (ν : ℝ) (d : ℕ) (ε γ : ℝ)
    (N : ℕ) (h : HvpBudgetFeasible P ν d ε γ N) :
    hvpMinimaxComplexity P ν d ε γ≤(N:ℝ≥0∞) :=
  iInf_le_of_le N (iInf_le_of_le h le_rfl)

theorem richMinimaxComplexity_le_budget (P : Parameters) (σ₀ : ℝ) (d : ℕ) (ε γ : ℝ)
    (N : ℕ) (h : RichBudgetFeasible P σ₀ d ε γ N) :
    richMinimaxComplexity P σ₀ d ε γ≤(N:ℝ≥0∞) :=
  iInf_le_of_le N (iInf_le_of_le h le_rfl)

theorem hvpMinimaxComplexity_lower (P : Parameters) (ν : ℝ) (d : ℕ) (ε γ L : ℝ)
    (h : ∀ N, HvpBudgetFeasible P ν d ε γ N → L≤(N:ℝ)) :
    ENNReal.ofReal L≤hvpMinimaxComplexity P ν d ε γ := by
  apply le_iInf
  intro N
  apply le_iInf
  intro hN
  simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal (h N hN)

theorem richMinimaxComplexity_lower (P : Parameters) (σ₀ : ℝ) (d : ℕ) (ε γ L : ℝ)
    (h : ∀ N, RichBudgetFeasible P σ₀ d ε γ N → L≤(N:ℝ)) :
    ENNReal.ofReal L≤richMinimaxComplexity P σ₀ d ε γ := by
  apply le_iInf
  intro N
  apply le_iInf
  intro hN
  simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal (h N hN)

theorem hvpMinimaxComplexity_eq_least (P : Parameters) (ν : ℝ) (d : ℕ) (ε γ : ℝ)
    (N : ℕ) (hN : HvpBudgetFeasible P ν d ε γ N)
    (hmin : ∀ K, HvpBudgetFeasible P ν d ε γ K → N≤K) :
    hvpMinimaxComplexity P ν d ε γ=(N:ℝ≥0∞) := by
  apply le_antisymm (hvpMinimaxComplexity_le_budget P ν d ε γ N hN)
  simpa only [ENNReal.ofReal_natCast] using hvpMinimaxComplexity_lower P ν d ε γ (N:ℝ)
    (fun K hK => by exact_mod_cast hmin K hK)

theorem richMinimaxComplexity_eq_least (P : Parameters) (σ₀ : ℝ) (d : ℕ) (ε γ : ℝ)
    (N : ℕ) (hN : RichBudgetFeasible P σ₀ d ε γ N)
    (hmin : ∀ K, RichBudgetFeasible P σ₀ d ε γ K → N≤K) :
    richMinimaxComplexity P σ₀ d ε γ=(N:ℝ≥0∞) := by
  apply le_antisymm (richMinimaxComplexity_le_budget P σ₀ d ε γ N hN)
  simpa only [ENNReal.ofReal_natCast] using richMinimaxComplexity_lower P σ₀ d ε γ (N:ℝ)
    (fun K hK => by exact_mod_cast hmin K hK)

def toleranceDimensionEnvelope (κ ε γ : ℝ) : ℕ := ⌈(ε*γ)^(-κ)⌉₊

def hvpEnvelopeComplexity (P : Parameters) (ν κ ε γ : ℝ) : ℝ≥0∞ :=
  ⨆ (d : ℕ) (_ : 1≤d ∧ d≤toleranceDimensionEnvelope κ ε γ), hvpMinimaxComplexity P ν d ε γ

def richEnvelopeComplexity (P : Parameters) (σ₀ κ ε γ : ℝ) : ℝ≥0∞ :=
  ⨆ (d : ℕ) (_ : 1≤d ∧ d≤toleranceDimensionEnvelope κ ε γ), richMinimaxComplexity P σ₀ d ε γ

theorem hvpMinimaxComplexity_le_envelope (P : Parameters) (ν κ ε γ : ℝ) (d : ℕ)
    (hd : 1≤d) (hD : d≤toleranceDimensionEnvelope κ ε γ) :
    hvpMinimaxComplexity P ν d ε γ≤hvpEnvelopeComplexity P ν κ ε γ :=
  le_iSup_of_le d (le_iSup_of_le ⟨hd,hD⟩ le_rfl)

theorem richMinimaxComplexity_le_envelope (P : Parameters) (σ₀ κ ε γ : ℝ) (d : ℕ)
    (hd : 1≤d) (hD : d≤toleranceDimensionEnvelope κ ε γ) :
    richMinimaxComplexity P σ₀ d ε γ≤richEnvelopeComplexity P σ₀ κ ε γ :=
  le_iSup_of_le d (le_iSup_of_le ⟨hd,hD⟩ le_rfl)

end
end SecondOrder
