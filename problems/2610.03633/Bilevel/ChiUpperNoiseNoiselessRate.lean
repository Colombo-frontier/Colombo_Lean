import Bilevel.ChiUpperNoiseRateProperty

/-! Cost monotonicity for the actual upper-noise run and the bounded-kappa
comparison used for its exact zero-noise specialization. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
universe u v
namespace Bilevel.ChiHierarchyHaar
open ChiHierarchyIndex ChiTreeProgress ChiBoundedChain ChiRecursive ChiCarrier ChiOuter
  ChiUpperNoise

theorem upperNoiseRateProperty_mono
    (macroN dim : ℕ) (cn : ℝ) (ratios resolutions : ℕ → ℝ)
    (hdim : ∀ j,sourceChainIndex cn (ratios j) (resolutions j)+1≤dim)
    (hAll : ∀ i : FrameIndex (sourceCounts macroN cn ratios resolutions) 0,chainSize i+1≤dim)
    (sc : Scale) (weight : ℕ → ℝ) (ζ CR Km : ℝ) (rad R : ℕ → ℝ) (K ε μ L π : ℝ)
    (hπ1 : π≤1) {a b : ℝ}
    (H : UpperNoiseRateProperty.{u,v} macroN dim cn ratios resolutions hdim hAll sc weight ζ CR Km rad R K ε μ L π hπ1 a)
    (hab : b≤a) :
    UpperNoiseRateProperty.{u,v} macroN dim cn ratios resolutions hdim hAll sc weight ζ CR Km rad R K ε μ L π hπ1 b := by
  intro instMO instBO instMQ instBQ Private State instP instS alg initial hinit ρseed instρ haccuracy
  obtain ⟨x,hx⟩ := @H instMO instBO instMQ instBQ Private State instP instS alg initial hinit ρseed instρ haccuracy
  exact ⟨x,(ENNReal.ofReal_le_ofReal hab).trans hx⟩

end Bilevel.ChiHierarchyHaar
namespace Bilevel.ChiUpperNoise

theorem bounded_kappa_noiseless_rate {c L κ Δ ε : ℝ}
    (hc : 0≤c) (hL : 0≤L) (hΔ : 0≤Δ) (hκ : κ≤3200) :
    (c/Real.sqrt 3200)*L*κ^2*Real.sqrt κ*Δ/ε^2≤c*(L*κ^2*Δ/ε^2) := by
  have hs : Real.sqrt κ/Real.sqrt 3200≤1 := (div_le_one (by positivity)).mpr (Real.sqrt_le_sqrt hκ)
  have hh := mul_le_mul_of_nonneg_right hs (by positivity : 0≤c*(L*κ^2*Δ/ε^2))
  rw [one_mul] at hh
  convert hh using 1
  ring

end Bilevel.ChiUpperNoise
