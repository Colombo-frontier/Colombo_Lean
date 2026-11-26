import SecondOrder.CurvatureHolderQueryLower
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Filter
open scoped Topology

namespace SecondOrder
noncomputable section

def curvatureHolderEnvelopeConstant (Δ L σ ν : ℝ) : ℝ :=
  2+Δ*L^(2/ν)+Δ*σ^2*L^(2/ν)

theorem curvatureHolderEnvelopeConstant_pos {Δ L σ ν : ℝ} (hΔ : 0≤Δ) (hL : 0<L) :
    0<curvatureHolderEnvelopeConstant Δ L σ ν := by
  unfold curvatureHolderEnvelopeConstant
  positivity

theorem curvatureHolderEnvelope_le_power {Δ L σ γ ν : ℝ}
    (hΔ : 0≤Δ) (hL : 0<L) (hγ : 0<γ) (hγ1 : γ≤1) (hν : 0<ν) :
    curvatureHolderEnvelope Δ L σ γ ν≤curvatureHolderEnvelopeConstant Δ L σ ν/γ^(3+2/ν) := by
  have hq : (0:ℝ)≤3+2/ν := by positivity
  have hp : γ^(3+2/ν)≤1 := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_ge hγ hγ1 hq
  have hp' : γ^(3+2/ν)≤γ^(1+2/ν) :=
    Real.rpow_le_rpow_of_exponent_ge hγ hγ1 (by linarith)
  have h0 : (2:ℝ)≤2/γ^(3+2/ν) := (le_div_iff₀ (by positivity)).2 (by linarith only [hp])
  have h1 := div_le_div_of_nonneg_left (show 0≤Δ*L^(2/ν) by positivity) (by positivity) hp'
  unfold curvatureHolderEnvelope curvatureHolderEnvelopeConstant
  calc
    _ ≤ 2/γ^(3+2/ν)+Δ*L^(2/ν)/γ^(3+2/ν)+Δ*σ^2*L^(2/ν)/γ^(3+2/ν) :=
      add_le_add_right (add_le_add h0 h1) _
    _ = _ := by ring

theorem curvatureHolderBlockSize_log_bound {Δ L σ γ ν : ℝ}
    (hΔ : 0≤Δ) (hL : 0<L) (hγ : 0<γ) (hγ1 : γ≤1) (hν : 0<ν) (hν1 : ν≤1) :
    (curvatureHolderBlockSize Δ L σ γ ν:ℝ)≤
      131072*Real.log (curvatureHolderEnvelopeConstant Δ L σ ν)+2-
        (131072*(3+2/ν))*Real.log γ := by
  have hh := (curvatureHolderBlockSize_bounds (σ := σ) hΔ hL hγ hν hν1).2
  have he := curvatureHolderEnvelope_ge_two (σ := σ) (ν := ν) hΔ hL hγ
  have hl := Real.log_le_log (by linarith : 0<curvatureHolderEnvelope Δ L σ γ ν)
    (curvatureHolderEnvelope_le_power hΔ hL hγ hγ1 hν)
  rw [Real.log_div (curvatureHolderEnvelopeConstant_pos hΔ hL).ne' (by positivity),Real.log_rpow hγ] at hl
  linarith only [hh,hl]

/-- Every positive tolerance power dominates the actual rounded logarithmic
block dimension; no continuity of the ceiling function is assumed. -/
theorem curvatureHolderBlockSize_mul_rpow_tendsto {Δ L σ ν r : ℝ}
    (hΔ : 0≤Δ) (hL : 0<L) (hν : 0<ν) (hν1 : ν≤1) (hr : 0<r) :
    Tendsto (fun γ : ℝ => (curvatureHolderBlockSize Δ L σ γ ν:ℝ)*γ^r) (𝓝[>] 0) (𝓝 0) := by
  have hp : Tendsto (fun γ : ℝ => γ^r) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.zero_rpow hr.ne'] using
      (Real.continuousAt_rpow_const 0 r (.inr hr.le)).tendsto.mono_left nhdsWithin_le_nhds
  have hl := tendsto_log_mul_rpow_nhdsGT_zero hr
  have hup : Tendsto (fun γ : ℝ =>
      (131072*Real.log (curvatureHolderEnvelopeConstant Δ L σ ν)+2)*γ^r-
        (131072*(3+2/ν))*(Real.log γ*γ^r)) (𝓝[>] 0) (𝓝 0) := by
    simpa using (hp.const_mul (131072*Real.log (curvatureHolderEnvelopeConstant Δ L σ ν)+2)).sub
      (hl.const_mul (131072*(3+2/ν)))
  apply squeeze_zero' _ _ hup
  · filter_upwards [self_mem_nhdsWithin] with γ hγ
    exact mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (show 0≤γ from le_of_lt hγ) _)
  · have hlt : ∀ᶠ γ : ℝ in 𝓝[>] 0, γ<1 :=
      (eventually_lt_nhds (show (0:ℝ)<1 by norm_num)).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin,hlt] with γ hγ hγ1
    have hh := mul_le_mul_of_nonneg_right
      (curvatureHolderBlockSize_log_bound (σ := σ) hΔ hL hγ hγ1.le hν hν1)
      (Real.rpow_nonneg (show 0≤γ from le_of_lt hγ) r)
    convert hh using 1 <;> ring

end
end SecondOrder
