import Bilevel.ChiExpectedRateProperty


/-! A fixed public dimension covers every truncation in the expected-time
argument, before any algorithm or orientation is chosen. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory
open scoped ENNReal
namespace Bilevel.ChiHierarchyHaar
universe u v
open ChiHierarchyIndex ChiTreeProgress ChiHierarchyExecution ChiBoundedChain ChiRecursive ChiCarrier ChiOuter
  ChiPrefixEvaluation PrimitiveGeometry ChiExtension ChiExtensionCalibration PartialLegendre BorelAdaptive ChiCurvatureSchedule
variable {macroN J dim : ℕ} {cn : ℝ} {ratios resolutions : ℕ → ℝ}
  {hdim : ∀ j,sourceChainIndex cn (ratios j) (resolutions j)+1≤dim}
  {hAll : ∀ i : FrameIndex (sourceCounts macroN cn ratios resolutions) J,chainSize i+1≤dim}
  {sc : Scale} {weight : ℕ → ℝ} {ζ CR Km : ℝ} {hJ : 1≤J}
  {v : ℝ} {rad R : ℕ → ℝ} {L K ε : ℝ}


variable (H : CanonicalQueryCertificate macroN J dim cn ratios resolutions hdim hAll sc weight ζ CR Km hJ v rad R L K ε)

theorem CanonicalQueryCertificate.RateProperty.mono {μ π rate rate' : ℝ} {hπ1 : π≤1}
    (h : CanonicalQueryCertificate.RateProperty.{u,v} H μ π hπ1 rate)
    (hrate : rate'≤rate) : CanonicalQueryCertificate.RateProperty.{u,v} H μ π hπ1 rate' := by
  intro instMX instBX instMY instBY instMR instBR instMQ instBQ Private State instP instS alg initial hinit ρseed instρ haccuracy
  obtain ⟨a,ha⟩ := @h instMX instBX instMY instBY instMR instBR instMQ instBQ
    Private State instP instS alg initial hinit ρseed instρ haccuracy
  exact ⟨a,(ENNReal.ofReal_le_ofReal hrate).trans ha⟩

end Bilevel.ChiHierarchyHaar

namespace Bilevel.ChiExtensionCalibration

theorem boundedThetaExpression_le {c L κ Δ ε σ θ Θ : ℝ}
    (hc : 0<c) (hL : 0<L) (hκ : 0<κ) (hΔ : 0<Δ) (hε : 0<ε)
    (hθ : 1≤θ) (hθΘ : θ≤Θ) :
    (c/((1+Θ)*Θ^2))*(L*(1+θ)*κ^2*Δ/ε^2+L^3*θ^2*(1+θ)*κ^8*σ^2*Δ/ε^6)≤
      c*(L*κ^2*Δ/ε^2+L^3*κ^8*σ^2*Δ/ε^6) := by
  have hΘ : 1≤Θ := hθ.trans hθΘ
  have hΘp : 0<Θ := zero_lt_one.trans_le hΘ
  have hΘsq : 1≤Θ^2 := one_le_pow₀ hΘ
  have h1 : 1+θ≤(1+Θ)*Θ^2 := by
    have hh := mul_le_mul_of_nonneg_left hΘsq (show 0≤1+Θ by positivity)
    nlinarith only [hh,hθΘ]
  have h2 : θ^2*(1+θ)≤(1+Θ)*Θ^2 := by
    have hh := mul_le_mul (pow_le_pow_left₀ (by linarith only [hθ]) hθΘ 2)
      (show 1+θ≤1+Θ by linarith only [hθΘ]) (by linarith only [hθ]) (sq_nonneg Θ)
    simpa only [mul_comm] using hh
  let D := L*κ^2*Δ/ε^2
  let G := L^3*κ^8*σ^2*Δ/ε^6
  have hD : 0≤D := by dsimp [D]; positivity
  have hG : 0≤G := by dsimp [G]; positivity
  have hh := add_le_add (mul_le_mul_of_nonneg_right h1 hD) (mul_le_mul_of_nonneg_right h2 hG)
  have hh' : L*(1+θ)*κ^2*Δ/ε^2+L^3*θ^2*(1+θ)*κ^8*σ^2*Δ/ε^6≤((1+Θ)*Θ^2)*(D+G) := by
    convert hh using 1 <;> dsimp [D,G] <;> ring
  have hden : 0<(1+Θ)*Θ^2 := by positivity
  have hm := mul_le_mul_of_nonneg_left hh' (show 0≤c/((1+Θ)*Θ^2) by positivity)
  convert hm using 1
  dsimp [D,G]
  field_simp
  ring

end Bilevel.ChiExtensionCalibration
