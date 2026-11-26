import Bilevel.PolishedLiteralAmplitudeEta

/-! The final small-beta simplification in fb:lem:multiscale. Only
beta*theta is small; beta*(theta/alpha) remains unrestricted. -/
noncomputable section
namespace Bilevel.PolishedLiteral
open PrimitiveGeometry ChiBoundedChain ZeroChainSchedule

theorem literal_source_amplitude_multiscale_eta_small : ∃ C τ : ℝ,1≤C ∧ 0<τ ∧ τ≤1 ∧
    ∀ (U : Type*) [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
      (n : ℕ) (μ ell Lden β R α θ η : ℝ) (V : Space n →ₗᵢ[ℝ] U),
      0<μ → 0<Lden → 0<α → α≤1 → 1≤θ → 0<η → η≤1 → ell=α*Lden → 0<β → β≤R → β*θ≤τ →
      (∀ q : Joint U ℝ,
        ‖iteratedFDeriv ℝ 2 (singleAmplitudeLift n μ (η*ell) Lden β R (θ/α) V) q‖≤C*μ*(β*Real.sqrt (α*θ)+α^2*β^2) ∧
        ‖iteratedFDeriv ℝ 3 (singleAmplitudeLift n μ (η*ell) Lden β R (θ/α) V) q‖≤C*μ*θ) ∧
      (∀ u j,j≤levels (θ/α) →
        |residual n (η*ell) β (WrappedChain.coordinates n R V u)/Lden|≤width (1/64) β (θ/α) j/4 ∧
        PolishedLiteralCompensated.normal (width (1/64) β (θ/α) j)
          (residual n (η*ell) β (WrappedChain.coordinates n R V u)/Lden)=
            residual n (η*ell) β (WrappedChain.coordinates n R V u)/Lden ∧
        deriv (PolishedLiteralCompensated.normal (width (1/64) β (θ/α) j))
          (residual n (η*ell) β (WrappedChain.coordinates n R V u)/Lden)=1) := by
  obtain ⟨C,τ,hC,hτ,hb⟩ := literal_source_amplitude_multiscale_eta
  refine ⟨2*C,min τ 1,by linarith,lt_min hτ zero_lt_one,min_le_right _ _,?_⟩
  intro U _ _ _ n μ ell Lden β R α θ η V hμ hLd hα hα1 hθ hη hη1 hell hβ hR hs
  have hτ' := hs.trans (min_le_left _ _)
  have h1 := hs.trans (min_le_right _ _)
  have hβ1 : β≤1 := by nlinarith [mul_le_mul_of_nonneg_left hθ hβ.le]
  have hαsq : α^2≤1 := by nlinarith
  have hsmall : α^2*β≤θ := by nlinarith [mul_le_mul_of_nonneg_right hαsq hβ.le]
  have hh := hb U n μ ell Lden β R α θ η V hμ hLd hα hα1 hθ hη hη1 hell hβ hR
  constructor
  · intro q
    obtain ⟨h2,h3⟩ := hh.1 q
    constructor
    · apply h2.trans
      have hn : 0≤C*μ*(β*Real.sqrt (α*θ)+α^2*β^2) := by positivity
      nlinarith only [hn]
    · have ht := mul_le_mul_of_nonneg_left hsmall (show 0≤C*μ by positivity)
      nlinarith only [h3,ht]
  · exact hh.2 hτ'

end Bilevel.PolishedLiteral
