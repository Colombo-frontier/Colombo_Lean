import Bilevel.MultiscaleBoundedGapRate
import Bilevel.MultiscaleOracle

/-! Count arithmetic for the literal conservative source oracle and its
actual activationProbability, retaining zero noise. The statistical
execution/coupling argument is intentionally separate. -/
noncomputable section
namespace Bilevel.MultiscaleMean
set_option autoImplicit false
set_option maxHeartbeats 600000

theorem actual_inner_probability_rate
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {n T : ℕ} (P : Parameters (E:=E) n) {A η L Δ κ θ ε σ : ℝ}
    (hA : 1≤A) (hη : 0<η) (hη1 : η≤1)
    (hL : 0<L) (hΔ : 0<Δ) (hκ : 0<κ) (hθ : 0<θ) (hε : 0<ε)
    (hμ : P.μ=2*(L/κ)) (hβ : P.β=innerWidth A η ε κ L) (hPθ : P.θ=θ)
    (hcount : (η/(2048*A^4))*L*κ^2*Δ/ε^2≤(T:ℝ)) :
    ((η/(2048*A^4))/(2048*envelopeConstant E*A^4/η^2)^2)*
      (L*κ^2*Δ/ε^2+L^3*θ^2*κ^8*σ^2*Δ/ε^6)≤
      (T:ℝ)*(P.activationProbability σ)⁻¹ := by
  have hh := inner_probability_rate hA hη hη1 (envelopeConstant_one_le E)
    hL hΔ hκ hθ hε (σ:=σ) hcount
  simpa only [Parameters.activationProbability,Parameters.signalBound,hμ,hβ,hPθ] using hh

end Bilevel.MultiscaleMean
