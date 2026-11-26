import Bilevel.PolishedLiteralAmplitudeScaled

/-! Exact source multiscale lift including the paper's fixed prefactor
eta. The constants are uniform for eta in (0,1], and the schedule uses
theta/alpha, never theta/(eta*alpha). -/
noncomputable section
set_option maxHeartbeats 800000
namespace Bilevel.PolishedLiteral
open PrimitiveGeometry ChiBoundedChain ChiRecursive ZeroChainSchedule

/-- Exact source fb:lem:multiscale, including its unrestricted amplitude
schedule v=theta/alpha and actual normal linearity at r/Lden. -/
theorem literal_source_amplitude_multiscale_eta : ∃ C τ : ℝ,1≤C ∧ 0<τ ∧
    ∀ (U : Type*) [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
      (n : ℕ) (μ ell Lden β R α θ η : ℝ) (V : Space n →ₗᵢ[ℝ] U),
      0<μ → 0<Lden → 0<α → α≤1 → 1≤θ → 0<η → η≤1 → ell=α*Lden → 0<β → β≤R →
      (∀ q : Joint U ℝ,
        ‖iteratedFDeriv ℝ 2 (singleAmplitudeLift n μ (η*ell) Lden β R (θ/α) V) q‖≤C*μ*(β*Real.sqrt (α*θ)+α^2*β^2) ∧
        ‖iteratedFDeriv ℝ 3 (singleAmplitudeLift n μ (η*ell) Lden β R (θ/α) V) q‖≤C*μ*(θ+α^2*β)) ∧
      (β*θ≤τ → ∀ u j,j≤levels (θ/α) →
        |residual n (η*ell) β (WrappedChain.coordinates n R V u)/Lden|≤width (1/64) β (θ/α) j/4 ∧
        PolishedLiteralCompensated.normal (width (1/64) β (θ/α) j)
          (residual n (η*ell) β (WrappedChain.coordinates n R V u)/Lden)=
            residual n (η*ell) β (WrappedChain.coordinates n R V u)/Lden ∧
        deriv (PolishedLiteralCompensated.normal (width (1/64) β (θ/α) j))
          (residual n (η*ell) β (WrappedChain.coordinates n R V u)/Lden)=1) := by
  obtain ⟨C,τ,hC,hτ,hbud⟩ := actual_literal_amplitude_budgets_scaled
  refine ⟨C,τ,hC,hτ,?_⟩
  intro U _ _ _ n μ ell Lden β R α θ η V hμ hLd hα hα1 hθ hη hη1 hell hβ hR
  have hv : 1≤θ/α := (le_div_iff₀ hα).mpr (by linarith)
  let P := singleParameters n μ (η*ell) β R (θ/α) V hβ hv
  have hellη : η*ell=η*α*Lden := by rw [hell];ring
  have hh := hbud (Space 0) U P Lden α θ η hLd hα hα1 hθ hη hη1 hellη hμ hβ hR (le_refl _) (le_refl _) rfl rfl rfl
  constructor
  · intro q
    have hb := hh.1 (singleLiftEmbed q)
    have hres : singleAmplitudeLift n μ (η*ell) Lden β R (θ/α) V=P.amplitudePerturbation Lden ∘ singleLiftEmbed :=
      singleAmplitudeLift_eq_restriction n μ (η*ell) Lden β R (θ/α) V hβ hv
    rw [hres]
    have hcont := P.amplitudePerturbation_contDiff Lden
    constructor
    · apply (ChiOuter.contraction_jet_bound (singleLiftEmbed (U:=U)) (singleLiftEmbed_norm (U:=U)) hcont q 2 (by norm_num)).trans
      exact hb.1
    · apply (ChiOuter.contraction_jet_bound (singleLiftEmbed (U:=U)) (singleLiftEmbed_norm (U:=U)) hcont q 3 (by norm_num)).trans
      exact hb.2
  · intro hs u j hj
    have hc := hh.2 hs (PrimitiveGeometry.pack 0 u) j hj
    rw [singleParameters_residual] at hc
    have hwpos := width_pos (1/64) β (θ/α) (by norm_num) hβ hv j
    exact ⟨hc,PolishedLiteralCompensated.normal_core _ _ hwpos hc,
      PolishedLiteralCompensated.normal_deriv_core _ _ hwpos hc⟩

end Bilevel.PolishedLiteral
