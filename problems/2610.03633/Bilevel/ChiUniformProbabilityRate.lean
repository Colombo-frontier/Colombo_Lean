import Bilevel.ChiUniformActivationWindow
import Bilevel.ChiUniformSignalRate

/-! Activation count divided by the actual Bernoulli revelation
probability. The conversion to oracle queries is deliberately separate. -/
noncomputable section
namespace Bilevel.ChiIndependentWidths
open ChiExtensionCalibration

theorem count_times_inverse_probability {N : ℕ} {c C L θ κ Δ ε σ B : ℝ} {qN qB : ℕ}
    (hc : 0<c) (hC : 1≤C) (hL : 0<L) (hθ : 1≤θ) (hκ : 0<κ)
    (hΔ : 0<Δ) (hε : 0<ε) (hB : 0<B)
    (hcount : c*L*(1+θ)*κ^2*Δ/(ε^2*(Real.log (2+θ))^qN)≤(N:ℝ))
    (hsignal : B≤C*(Real.log (2+θ))^qB*ε^2/(L*θ*κ^3)) :
    (c/C^2)*(L*(1+θ)*κ^2*Δ/ε^2+L^3*θ^2*(1+θ)*κ^8*σ^2*Δ/ε^6)/
      (Real.log (2+θ))^(qN+2*qB)≤(N:ℝ)*(BernoulliOracle.probability B σ)⁻¹ := by
  let ℓ := Real.log (2+θ)
  have hℓ : 1≤ℓ := (one_le_pow₀ (by norm_num : (1:ℝ)≤4) : (1:ℝ)≤4^chosenDepth θ).trans
    (chosenDepth_bound hθ)
  have hℓp : 0<ℓ := by linarith
  have hCp : 0<C := by linarith
  have hp := inverse_probability_of_signal_bound (σ:=σ) hB (show 0<C*ℓ^qB by positivity)
    hL (by linarith only [hθ]) hκ hε hsignal
  have hM : 1≤C^2*ℓ^(2*qB) := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hC) (one_le_pow₀ hℓ)
  have hpow : ℓ^qN≤C^2*ℓ^(qN+2*qB) := by
    have hm := mul_le_mul_of_nonneg_left hM (show 0≤ℓ^qN by positivity)
    rw [pow_add]
    nlinarith only [hm]
  have hd := div_le_div_of_nonneg_left
    (show 0≤c*L*(1+θ)*κ^2*Δ/ε^2 by positivity) (show 0<ℓ^qN by positivity) hpow
  have hn : c*L*(1+θ)*κ^2*Δ/(ε^2*ℓ^qN)≤(N:ℝ) := hcount
  have hm := mul_le_mul hn hp (show 0≤1+L^2*θ^2*κ^6*σ^2/((C*ℓ^qB)^2*ε^4) by positivity)
    (Nat.cast_nonneg N)
  apply le_trans _ hm
  have he : (c/C^2)*(L*(1+θ)*κ^2*Δ/ε^2+L^3*θ^2*(1+θ)*κ^8*σ^2*Δ/ε^6)/ℓ^(qN+2*qB)=
      (c*L*(1+θ)*κ^2*Δ/ε^2)/(C^2*ℓ^(qN+2*qB))+
      (c*L*(1+θ)*κ^2*Δ/(ε^2*ℓ^qN))*(L^2*θ^2*κ^6*σ^2/((C*ℓ^qB)^2*ε^4)) := by
    rw [pow_add,pow_mul ℓ 2 qB]
    field_simp
    ring
  change (c/C^2)*_/ℓ^(qN+2*qB)≤_
  rw [he]
  calc
    _ ≤ (c*L*(1+θ)*κ^2*Δ/ε^2)/ℓ^qN+
      (c*L*(1+θ)*κ^2*Δ/(ε^2*ℓ^qN))*(L^2*θ^2*κ^6*σ^2/((C*ℓ^qB)^2*ε^4)) :=
      add_le_add_right hd _
    _ = _ := by ring

end Bilevel.ChiIndependentWidths
