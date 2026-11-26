import Smoothness2601.ExactUpperModel
import Smoothness2601.HardLower
import Smoothness2601.HardHorizon
import Smoothness2601.UpperMinimax

/-! The actual hard family remains hard when every upper gradient is exact.
The stronger oracle restriction is established for the witness before using
the restricted-class success guarantee. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Smoothness2601.ExactUpper
open HardProfiles

theorem hard_oracle_exact {b : Budgets} {M Λ β : ℝ} (W : WidthConstants b M Λ β)
    {p : WithTop ℕ} (hp : 1 ≤ p) (hβ : 0 ≤ β) {s : ℝ} (hs : 0 < s) (hsδ : s ≤ W.threshold)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {n : ℕ} (U : ExtensiveChain.Space n →ₗᵢ[ℝ] E) :
    IsExact (population W hp hβ hs hsδ U) (oracle W hp hβ hs hsδ U) := by
  unfold oracle SineGeometry.Profiles.oracle
  exact freshBernoulli _ _ _ _ _ _

theorem hard_budget_obstruction {b : Budgets} {M Λ β : ℝ}
    (W : WidthConstants b M Λ β) (hM : 0 < M) (hΛ : 0 < Λ)
    {p : WithTop ℕ} (hp : 1 ≤ p) (hβ : 0 ≤ β) {ε : ℝ} (hε : 0 < ε)
    (hεs : 16*ε ≤ W.chainThreshold) (N : ℕ)
    (hN : (N:ℝ) ≤ W.finalRateConstant*ε^(-4:ℝ)*orderTradeoff p β ε ^ 2) :
    ¬BudgetWorks b p (derivativeEnvelope b M Λ β) ε N := by
  have hs : 0 < 16*ε := by positivity
  have hsδ := (W.chainThreshold_conditions hs hεs).1
  obtain ⟨n,hlo,_hhi,hgap⟩ := W.choose_chain hs hεs
  have hbudget := W.budget_reveal hp hβ hs hεs hlo (W.scaled_budget hp hβ hε hεs hN)
  intro hworks
  obtain ⟨A,hA⟩ := budgetWorks_scalar hworks (hardDimension N n)
  obtain ⟨U,hU,hfail⟩ := fixed_frame_expected_norm_chosen_dimension W hp hβ hs hsδ n N hbudget A
  let I := FrameTruncation.frameIsometry U hU
  have hsuccess := hA (population W hp hβ hs hsδ I) (regularity W hp hβ hs hsδ I hM hΛ)
    0 0 (initialized W hp hβ hs hsδ I hgap) Unit inferInstance (oracle W hp hβ hs hsδ I)
    (hard_oracle_exact W hp hβ hs hsδ I) ()
  have hbad := hfail.trans hsuccess
  have hreal := (ENNReal.ofReal_le_ofReal_iff hε.le).mp hbad
  linarith

theorem uniform_minimax_lower (b : Budgets) {M Λ β : ℝ}
    (hgap : b.μ < b.L₁) (hM : 0 < M) (hΛ : 0 < Λ) (hβ : 0 ≤ β) :
    ∃ c ε₀ : ℝ, 0 < c ∧ 0 < ε₀ ∧
      ∀ p : WithTop ℕ, 1 ≤ p → ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        ENNReal.ofReal (c*ε^(-4:ℝ)*orderTradeoff p β ε ^ 2) ≤
          minimaxComplexity b p (derivativeEnvelope b M Λ β) ε := by
  obtain ⟨W⟩ := widthConstants_nonempty (β := β) b hgap hM hΛ
  refine ⟨W.finalRateConstant,W.chainThreshold/16,W.finalRateConstant_pos,
    div_pos W.chainThreshold_pos (by norm_num),?_⟩
  intro p hp ε hε hs
  have hεs : 16*ε ≤ W.chainThreshold := by linarith
  apply minimax_lower_of_budget_obstruction
  intro N hN
  exact hard_budget_obstruction W hM hΛ hp hβ hε hεs N hN.le

theorem uniform_minimax (b : Budgets) {M Λ β : ℝ}
    (hgap : b.μ < b.L₁) (hM : 0 < M) (hΛ : 0 < Λ) (hβ : 0 ≤ β) :
    ∃ c C ε₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < ε₀ ∧
      ∀ p : WithTop ℕ, 1 ≤ p → ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        ENNReal.ofReal (c*ε^(-4:ℝ)*orderTradeoff p β ε ^ 2) ≤
          minimaxComplexity b p (derivativeEnvelope b M Λ β) ε ∧
        minimaxComplexity b p (derivativeEnvelope b M Λ β) ε ≤
          ENNReal.ofReal (C*ε^(-4:ℝ)*orderTradeoff p β ε ^ 2) := by
  obtain ⟨c,δ,hc,hδ,hl⟩ := uniform_minimax_lower b hgap hM hΛ hβ
  obtain ⟨C,η,hC,hη,hu⟩ := Smoothness2601.uniform_minimax_upper b hgap hM hΛ hβ
  refine ⟨c,C,min δ η,hc,hC,lt_min hδ hη,?_⟩
  intro p hp ε hε hs
  exact ⟨hl p hp ε hε (hs.trans_le (min_le_left _ _)),
    (minimax_le_full b p _ ε).trans (hu p hp ε hε (hs.trans_le (min_le_right _ _)))⟩

end Smoothness2601.ExactUpper
