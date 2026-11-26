import Smoothness2601.PublicOuterSource


/-! The actual upper minimax bound. The algorithm is constructed from public
parameters before the population, initialized point, and adaptive oracle are
quantified. Its exact execution law is proved equal to the analyzed law. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Smoothness2601

theorem fixed_order_budgetWorks (b : Budgets) {p : WithTop ℕ} {M Λ β cₐ ε : ℝ}
    (hgap : b.μ < b.L₁) (hM : 0 < M) (hΛ : 0 < Λ) (hβ : 0 ≤ β)
    (hcₐ : 0 < cₐ) (hsmall : cₐ ≤ b.μ/(256*b.L₁)) (hε : 0 < ε)
    (r : ℕ) (hr : 1 ≤ r) (hrp : (r : WithTop ℕ) ≤ p) :
    BudgetWorks b p (derivativeEnvelope b M Λ β) ε
      (OuterSource.callCount b M Λ β cₐ r ε) := by
  intro dx dy
  refine ⟨PublicOuter.sourceAlgorithm b M Λ β cₐ r hε, ?_⟩
  intro P hreg x₀ y₀ hinit H inst O history
  have hs := OuterSource.expected_stationarity P O hgap hM hΛ hβ hcₐ hsmall hε
    hreg r hr hrp (x₀,y₀) history hinit
  have hLip : LipschitzWith
      ⟨HypergradientGeometry.outerSmoothness b, (HypergradientGeometry.outerSmoothness_pos b).le⟩
      (gradient P.objective) :=
    LipschitzWith.of_dist_le_mul (fun x z => by
      simpa only [dist_eq_norm, NNReal.coe_mk] using HypergradientGeometry.outer_smoothness P x z)
  have hm := hLip.continuous.measurable.nnnorm.coe_nnreal_ennreal
  unfold Adaptive.Succeeds Adaptive.expectedNorm
  rw [PublicOuter.sourceAlgorithm_output, MeasureTheory.lintegral_map hm
    (NormalizedExecution.selected_measurable (OuterSchedule.iterations b ε))]
  rw [lintegral_coe_eq_integral _ hs.1]
  apply ENNReal.ofReal_le_ofReal
  exact hs.2.trans (by linarith)


end Smoothness2601
