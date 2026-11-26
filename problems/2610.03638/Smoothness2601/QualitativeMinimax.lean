import Smoothness2601.QualitativeModel
import Smoothness2601.HardLower
import Smoothness2601.HardHorizon
import Smoothness2601.UpperMinimax

/-! Source cor:bare for actual jointly smooth and optionally lower-analytic
population classes. The hard witnesses also have entire lower extensions. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Smoothness2601
open HardProfiles

theorem qualitative_budget_obstruction {b : Budgets}
    (W : WidthConstants b 1 1 0) (analytic : Bool) {ε : ℝ} (hε : 0 < ε)
    (hεs : 16*ε ≤ W.chainThreshold) (N : ℕ)
    (hN : (N:ℝ) ≤ W.finalRateConstant*ε^(-6:ℝ)) :
    ¬QualitativeBudgetWorks b analytic ε N := by
  have hs : 0 < 16*ε := by positivity
  have hsδ := (W.chainThreshold_conditions hs hεs).1
  have hs1 := (W.threshold_conditions hsδ).2.1
  have hε1 : ε ≤ 1 := by linarith
  have hr : ε^(-4:ℝ)*orderTradeoff (1:WithTop ℕ) 0 ε ^ 2 = ε^(-6:ℝ) := by
    have hh := orderTradeoff_finite_zero_rate (p := 1) (by norm_num) hε hε1
    norm_num at hh
    exact hh
  have hN' : (N:ℝ) ≤ W.finalRateConstant*ε^(-4:ℝ)*orderTradeoff (1:WithTop ℕ) 0 ε ^ 2 := by
    rwa [mul_assoc,hr]
  obtain ⟨n,hlo,_hhi,hgap⟩ := W.choose_chain hs hεs
  have hbudget := W.budget_reveal (p := 1) (by norm_num) (le_refl (0:ℝ)) hs hεs hlo
    (W.scaled_budget (p := 1) (by norm_num) (le_refl (0:ℝ)) hε hεs hN')
  intro hworks
  obtain ⟨A,hA⟩ := qualitative_budgetWorks_scalar hworks (hardDimension N n)
  obtain ⟨U,hU,hfail⟩ := fixed_frame_expected_norm_chosen_dimension W
    (p := 1) (by norm_num) (le_refl (0:ℝ)) hs hsδ n N hbudget A
  let I := FrameTruncation.frameIsometry U hU
  have hsuccess := hA (population W (p := 1) (by norm_num) (le_refl (0:ℝ)) hs hsδ I)
    (jointlySmooth W (p := 1) (by norm_num) (le_refl (0:ℝ)) hs hsδ I)
    (fun _ => lowerAnalytic W (p := 1) (by norm_num) (le_refl (0:ℝ)) hs hsδ I)
    0 0 (initialized W (p := 1) (by norm_num) (le_refl (0:ℝ)) hs hsδ I hgap)
    Unit inferInstance (oracle W (p := 1) (by norm_num) (le_refl (0:ℝ)) hs hsδ I) ()
  have hbad := hfail.trans hsuccess
  have hreal := (ENNReal.ofReal_le_ofReal_iff hε.le).mp hbad
  linarith

theorem qualitative_minimax (b : Budgets) (hgap : b.μ < b.L₁) :
    ∃ c C δ : ℝ, 0 < c ∧ 0 < C ∧ 0 < δ ∧ ∀ analytic : Bool,
      ∀ ε : ℝ, 0 < ε → ε < δ →
        ENNReal.ofReal (c*ε^(-6:ℝ)) ≤ qualitativeMinimaxComplexity b analytic ε ∧
        qualitativeMinimaxComplexity b analytic ε ≤ ENNReal.ofReal (C*ε^(-6:ℝ)) := by
  obtain ⟨W⟩ := widthConstants_nonempty (M := 1) (Λ := 1) (β := 0) b hgap
    (by norm_num) (by norm_num)
  obtain ⟨C,η,hC,hη,hu⟩ := uniform_minimax_upper (M := 1) (Λ := 1) (β := 0) b hgap
    (by norm_num) (by norm_num) (le_refl (0:ℝ))
  refine ⟨W.finalRateConstant,C,min (W.chainThreshold/16) (min η 1),W.finalRateConstant_pos,hC,
    lt_min (div_pos W.chainThreshold_pos (by norm_num)) (lt_min hη zero_lt_one),?_⟩
  intro analytic ε hε hεδ
  have hεs : 16*ε ≤ W.chainThreshold := by
    have hh := hεδ.le.trans (min_le_left _ _)
    linarith
  have hεη := hεδ.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hε1 := hεδ.le.trans ((min_le_right _ _).trans (min_le_right _ _))
  constructor
  · apply qualitative_lower_of_obstruction
    intro N hN
    exact qualitative_budget_obstruction W analytic hε hεs N hN.le
  · have hh := (qualitative_minimax_le_baseline b (derivativeEnvelope b 1 1 0) analytic ε).trans
      (hu 1 (by norm_num) ε hε hεη)
    have hr : ε^(-4:ℝ)*orderTradeoff (1:WithTop ℕ) 0 ε ^ 2 = ε^(-6:ℝ) := by
      have hh' := orderTradeoff_finite_zero_rate (p := 1) (by norm_num) hε hε1
      norm_num at hh'
      exact hh'
    simpa only [mul_assoc,hr] using hh

end Smoothness2601
