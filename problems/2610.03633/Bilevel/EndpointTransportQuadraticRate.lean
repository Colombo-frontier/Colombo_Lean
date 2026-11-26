import Bilevel.ChiUpperNoiseCount
import Bilevel.EndpointTransportNormalization
import Bilevel.ChiRefinementRates

/-! Actual depth-zero physical layer/macro/micro floors have the required
deterministic rate. This arithmetic does not assert an SFO lower bound. -/
noncomputable section
namespace Bilevel.EndpointTransportNormalization

theorem quadratic_transport_count_lower {η η₀ L Δ Cgap Cb ε cn κ : ℝ} {n : ℕ}
    (hη : 0<η) (hη₀ : 0<η₀) (hL : 0<L) (hΔ : 0<Δ) (hCg : 0<Cgap) (hCb : 0<Cb)
    (hε : 0<ε) (hcn : 0<cn) (hκ : 3200≤κ) (hlen : 128≤cn/η^2)
    (hn : η₀*L*Δ/(4*Cgap*Cb^2*ε^2)≤(n:ℝ)) :
    (cn*η₀/(8*Cgap*Cb^2*192^2*2*Real.sqrt 128))*L*κ^2*Real.sqrt κ*Δ/ε^2≤
      ((layers κ*((n+1)*ChiUpperNoise.microLength cn (max (gain κ) (1/η))):ℕ):ℝ) := by
  have hK := gain_pos hκ
  have hKg : 0<max (gain κ) (1/η) := hK.trans_le (le_max_left _ _)
  have hc := ChiUpperNoise.macro_micro_count_lower hη₀ hL hΔ hCg hCb hε hcn
    (ChiUpperNoise.micro_length_argument hcn hη hKg hlen (le_max_right _ _)) hn
  have hkp : 0<κ := by linarith only [hκ]
  have hgain : κ/192≤max (gain κ) (1/η) := (gain_bounds hκ).1.trans (le_max_left _ _)
  have hs : (κ/192)^2≤(max (gain κ) (1/η))^2 := pow_le_pow_left₀ (by positivity) hgain 2
  have hm : (cn*η₀/(8*Cgap*Cb^2))*L*(κ/192)^2*Δ/ε^2≤
      (((n+1)*ChiUpperNoise.microLength cn (max (gain κ) (1/η)):ℕ):ℝ) := by
    apply le_trans _ hc
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs (by positivity)) hΔ.le) (sq_nonneg ε)
  have hb := mul_le_mul (layers_sqrt_kappa_bounds hκ).1 hm
    (show 0≤(cn*η₀/(8*Cgap*Cb^2))*L*(κ/192)^2*Δ/ε^2 by positivity) (Nat.cast_nonneg (layers κ))
  rw [Nat.cast_mul]
  apply le_trans _ hb
  apply le_of_eq
  ring

theorem quadratic_transport_bounded_theta {η η₀ L Δ Cgap Cb ε cn κ θ θmax : ℝ} {n : ℕ}
    (hη : 0<η) (hη₀ : 0<η₀) (hL : 0<L) (hΔ : 0<Δ) (hCg : 0<Cgap) (hCb : 0<Cb)
    (hε : 0<ε) (hcn : 0<cn) (hκ : 3200≤κ) (hlen : 128≤cn/η^2)
    (hθ : 0≤θ) (hθmax : θ≤θmax)
    (hn : η₀*L*Δ/(4*Cgap*Cb^2*ε^2)≤(n:ℝ)) :
    (cn*η₀/(8*Cgap*Cb^2*192^2*2*Real.sqrt 128*(1+θmax)))*
      ChiRefinementRates.deterministic L θ κ Δ ε≤
      ((layers κ*((n+1)*ChiUpperNoise.microLength cn (max (gain κ) (1/η))):ℕ):ℝ) := by
  apply le_trans _ (quadratic_transport_count_lower hη hη₀ hL hΔ hCg hCb hε hcn hκ hlen hn)
  have hmax : 0<1+θmax := by linarith only [hθ,hθmax]
  have hratio : (1+θ)/(1+θmax)≤1 := (div_le_one hmax).mpr (by linarith only [hθmax])
  have hnonneg : 0≤(cn*η₀/(8*Cgap*Cb^2*192^2*2*Real.sqrt 128))*L*κ^2*Real.sqrt κ*Δ/ε^2 := by positivity
  have hh := mul_le_mul_of_nonneg_right hratio hnonneg
  rw [one_mul] at hh
  convert hh using 1
  dsimp only [ChiRefinementRates.deterministic]
  field_simp
  ring

end Bilevel.EndpointTransportNormalization
