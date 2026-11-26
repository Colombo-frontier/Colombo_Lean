import Bilevel.ChiUpperNoiseCount

/-! The actual truncated-gain upper-noise family has the U-term count
arithmetic for every kappa >= 2, including sigma=0. Query conversion is separate. -/
noncomputable section
namespace Bilevel.ChiUpperNoise

theorem actual_upper_noise_probability_rate {η η₀ L Δ Cgap Cb ε cn C κ σ : ℝ} {n : ℕ}
    (hη : 0<η) (hη₀ : 0<η₀) (hL : 0<L) (hΔ : 0<Δ) (hCg : 0<Cgap)
    (hCb : 1≤Cb) (hε : 0<ε) (hcn : 0<cn) (hC : 1≤C) (hκ : 2≤κ)
    (hlen : 128≤cn/η^2)
    (hn : η₀*L*Δ/(4*Cgap*Cb^2*ε^2)≤(n:ℝ)) :
    let K := κ/6
    let Kg := max K (1/η)
    ((cn*η₀/(8*Cgap*Cb^2))/(1296*C^2*Cb^2))*
      (L*κ^2*Δ/ε^2+L*κ^4*σ^2*Δ/ε^4)≤
      (((n+1)*microLength cn Kg:ℕ):ℝ)*(BernoulliOracle.probability (C*Cb*ε/K) σ)⁻¹ := by
  dsimp only
  let K := κ/6
  let Kg := max K (1/η)
  let cN := cn*η₀/(8*Cgap*Cb^2)
  have hCb0 : 0<Cb := by linarith only [hCb]
  have hC0 : 0<C := by linarith only [hC]
  have hK : 0<K := by dsimp [K]; linarith only [hκ]
  have hKg : 0<Kg := hK.trans_le (le_max_left _ _)
  have hcN : 0<cN := by dsimp [cN]; positivity
  have hlarge := micro_length_argument hcn hη hKg hlen (le_max_right _ _)
  have hN := macro_micro_count_lower hη₀ hL hΔ hCg hCb0 hε hcn hlarge hn
  have hcount : cN*L*K^2*Δ/ε^2≤(((n+1)*microLength cn Kg:ℕ):ℝ) := by
    apply le_trans _ hN
    have hh := pow_le_pow_left₀ hK.le (le_max_left K (1/η)) 2
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh (mul_pos hcN hL).le) hΔ.le) (sq_nonneg ε)
  have hrate := macro_micro_probability_lower hcN hC hCb hL hK hΔ hε (σ:=σ) hcount
  apply le_trans _ hrate
  have he : (cN/(C^2*Cb^2))*(L*K^2*Δ/ε^2+L*K^4*σ^2*Δ/ε^4)-
      (cN/(1296*C^2*Cb^2))*(L*κ^2*Δ/ε^2+L*κ^4*σ^2*Δ/ε^4)=
      (35/1296)*(cN/(C^2*Cb^2))*(L*κ^2*Δ/ε^2) := by
    dsimp [K]
    ring
  have hp : 0≤(35/1296)*(cN/(C^2*Cb^2))*(L*κ^2*Δ/ε^2) := by positivity
  change (cN/(1296*C^2*Cb^2))*_≤_
  linarith only [he,hp]

end Bilevel.ChiUpperNoise
