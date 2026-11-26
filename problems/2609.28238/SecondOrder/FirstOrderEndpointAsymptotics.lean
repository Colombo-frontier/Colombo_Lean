import SecondOrder.FirstOrderEndpointQueryLower
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Filter
open scoped Topology

namespace SecondOrder
noncomputable section

def firstOrderEndpointEnvelopeConstant (Δ s : ℝ) : ℝ := 2+Δ+Δ*s^2

theorem firstOrderEndpointEnvelopeConstant_pos {Δ s : ℝ} (hΔ : 0≤Δ) :
    0<firstOrderEndpointEnvelopeConstant Δ s := by
  unfold firstOrderEndpointEnvelopeConstant
  positivity

theorem firstOrderEndpointEnvelope_le_power {Δ s ε : ℝ}
    (hΔ : 0≤Δ) (hε : 0<ε) (hε1 : ε≤1) :
    firstOrderEndpointEnvelope Δ s ε≤firstOrderEndpointEnvelopeConstant Δ s/ε^3 := by
  have h3 : ε^3≤1 := by simpa using pow_le_pow_left₀ hε.le hε1 3
  have h2 : ε^2≤1 := by simpa using pow_le_pow_left₀ hε.le hε1 2
  have hp : ε^3≤ε := by nlinarith [mul_le_mul_of_nonneg_left h2 hε.le]
  have h0 : (2:ℝ)≤2/ε^3 := (le_div_iff₀ (pow_pos hε 3)).2 (by linarith only [h3])
  have h1 := div_le_div_of_nonneg_left hΔ (pow_pos hε 3) hp
  unfold firstOrderEndpointEnvelope firstOrderEndpointEnvelopeConstant
  calc
    _ ≤ 2/ε^3+Δ/ε^3+Δ*s^2/ε^3 := add_le_add_right (add_le_add h0 h1) _
    _ = _ := by ring

theorem firstOrderEndpointBlockSize_log_bound {Δ s ε : ℝ}
    (hΔ : 0≤Δ) (hε : 0<ε) (hε1 : ε≤1) :
    (firstOrderEndpointBlockSize Δ s ε:ℝ)≤
      16384*Real.log (firstOrderEndpointEnvelopeConstant Δ s)+1-49152*Real.log ε := by
  have hh := (firstOrderEndpointBlockSize_bounds (s := s) hΔ hε).2.2
  have he := firstOrderEndpointEnvelope_ge_two (s := s) hΔ hε
  have hl := Real.log_le_log (by linarith : 0<firstOrderEndpointEnvelope Δ s ε)
    (firstOrderEndpointEnvelope_le_power hΔ hε hε1)
  rw [Real.log_div (firstOrderEndpointEnvelopeConstant_pos hΔ).ne' (by positivity),Real.log_pow] at hl
  norm_num at hl
  linarith only [hh,hl]

/-- Positive powers dominate the actual rounded block size. -/
theorem firstOrderEndpointBlockSize_mul_rpow_tendsto {Δ s r : ℝ} (hΔ : 0≤Δ) (hr : 0<r) :
    Tendsto (fun ε : ℝ => (firstOrderEndpointBlockSize Δ s ε:ℝ)*ε^r) (𝓝[>] 0) (𝓝 0) := by
  have hp : Tendsto (fun ε : ℝ => ε^r) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.zero_rpow hr.ne'] using
      (Real.continuousAt_rpow_const 0 r (.inr hr.le)).tendsto.mono_left nhdsWithin_le_nhds
  have hl := tendsto_log_mul_rpow_nhdsGT_zero hr
  have hup : Tendsto (fun ε : ℝ =>
      (16384*Real.log (firstOrderEndpointEnvelopeConstant Δ s)+1)*ε^r-
        49152*(Real.log ε*ε^r)) (𝓝[>] 0) (𝓝 0) := by
    simpa using (hp.const_mul (16384*Real.log (firstOrderEndpointEnvelopeConstant Δ s)+1)).sub
      (hl.const_mul 49152)
  apply squeeze_zero' _ _ hup
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (show 0≤ε from le_of_lt hε) _)
  · have hlt : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε<1 :=
      (eventually_lt_nhds (show (0:ℝ)<1 by norm_num)).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin,hlt] with ε hε hε1
    have hh := mul_le_mul_of_nonneg_right (firstOrderEndpointBlockSize_log_bound (s := s) hΔ hε hε1.le)
      (Real.rpow_nonneg (show 0≤ε from le_of_lt hε) r)
    convert hh using 1 <;> ring

theorem firstOrderEndpointConditions_eventually (P : Parameters) {σ₀ : ℝ} (hσ₀ : 0<σ₀) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0, FirstOrderEndpointConditions P σ₀ ε := by
  have hc := firstOrderEndpointSmallConstant_bounds.1
  have hs := firstOrderNoiseBudget_pos P hσ₀
  have hid : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) :=
    (tendsto_id : Tendsto (fun ε : ℝ => ε) (𝓝 0) (𝓝 0)).mono_left nhdsWithin_le_nhds
  have hLip := hid.eventually (eventually_le_nhds (mul_pos hc P.gradientLip_pos))
  have hnoise := hid.eventually (eventually_le_nhds (mul_pos hc hs))
  have hgap := hid.eventually (eventually_le_nhds (mul_pos hc P.gap_pos))
  have hH : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      (firstOrderEndpointBlockSize P.gap (firstOrderNoiseBudget P σ₀) ε:ℝ)*ε^2≤
        (firstOrderEndpointSmallConstant*P.hessianHolder)^2 := by
    have hh : Tendsto (fun ε : ℝ =>
        (firstOrderEndpointBlockSize P.gap (firstOrderNoiseBudget P σ₀) ε:ℝ)*ε^2) (𝓝[>] 0) (𝓝 0) := by
      simpa only [Real.rpow_natCast] using firstOrderEndpointBlockSize_mul_rpow_tendsto
        (s := firstOrderNoiseBudget P σ₀) P.gap_pos.le (show (0:ℝ)<(2:ℕ) by norm_num)
    exact hh.eventually (eventually_le_nhds (sq_pos_of_pos (mul_pos hc P.hessianHolder_pos)))
  filter_upwards [self_mem_nhdsWithin,hLip,hnoise,hgap,hH] with ε hε hl hn hg hh
  refine ⟨hσ₀,hε,hl,hn,?_,hg⟩
  apply (sq_le_sq₀ (mul_nonneg hε.le (Real.sqrt_nonneg _)) (mul_pos hc P.hessianHolder_pos).le).1
  rw [mul_pow,Real.sq_sqrt (Nat.cast_nonneg _)]
  nlinarith only [hh]

theorem firstOrderEndpointConditions_small (P : Parameters) {σ₀ : ℝ} (hσ₀ : 0<σ₀) :
    ∃ ε₀ : ℝ, 0<ε₀ ∧ ∀ ε : ℝ, 0<ε → ε≤ε₀ → FirstOrderEndpointConditions P σ₀ ε := by
  obtain ⟨ε₀,hε₀,hh⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp (firstOrderEndpointConditions_eventually P hσ₀)
  exact ⟨ε₀,hε₀,fun ε hε hsmall => hh ⟨hε,hsmall⟩⟩

end
end SecondOrder
