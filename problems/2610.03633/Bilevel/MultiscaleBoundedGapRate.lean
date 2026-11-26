import Bilevel.MultiscaleBoundedGapScale
import Bilevel.BernoulliOracle

/-! The actual chain length and informative amplitude yield the all-gap
D+G expression. This is arithmetic for the displayed Bernoulli family;
its information-to-query conversion is a separate theorem. -/
noncomputable section
namespace Bilevel.MultiscaleMean
set_option autoImplicit false
set_option maxHeartbeats 800000

theorem inner_signal_identity {A η ε κ L θ C : ℝ}
    (hη : 0<η) (hκ : 0<κ) (hL : 0<L) (hθ : 0<θ) :
    C*(2*(L/κ))*(innerWidth A η ε κ L)^2/θ=
      (2048*C*A^4/η^2)*ε^2/(L*θ*κ^3) := by
  unfold innerWidth
  field_simp [hη.ne',hκ.ne',hL.ne',hθ.ne']
  ring

theorem inner_probability_rate {T : ℕ} {A η C L Δ κ θ ε σ : ℝ}
    (hA : 1≤A) (hη : 0<η) (hη1 : η≤1) (hC : 1≤C)
    (hL : 0<L) (hΔ : 0<Δ) (hκ : 0<κ) (hθ : 0<θ) (hε : 0<ε)
    (hcount : (η/(2048*A^4))*L*κ^2*Δ/ε^2≤(T:ℝ)) :
    ((η/(2048*A^4))/(2048*C*A^4/η^2)^2)*
      (L*κ^2*Δ/ε^2+L^3*θ^2*κ^8*σ^2*Δ/ε^6)≤
      (T:ℝ)*(BernoulliOracle.probability
        (C*(2*(L/κ))*(innerWidth A η ε κ L)^2/θ) σ)⁻¹ := by
  have hAp : 0<A := by linarith
  have hCp : 0<C := by linarith
  let cN : ℝ := η/(2048*A^4)
  let B : ℝ := 2048*C*A^4/η^2
  have hcN : 0<cN := by dsimp [cN]; positivity
  have hB : 0<B := by dsimp [B]; positivity
  have hB1 : 1≤B := by
    dsimp [B]
    apply (one_le_div (sq_pos_of_pos hη)).mpr
    have hpow : 1≤A^4 := one_le_pow₀ hA
    have hCA : 1≤C*A^4 := one_le_mul_of_one_le_of_one_le hC hpow
    have hηsq : η^2≤1 := by nlinarith
    nlinarith
  rw [inner_signal_identity hη hκ hL hθ]
  change (cN/B^2)*_≤(T:ℝ)*(BernoulliOracle.probability (B*ε^2/(L*θ*κ^3)) σ)⁻¹
  have hsig : 0<B*ε^2/(L*θ*κ^3) := by positivity
  rw [BernoulliOracle.inverse_probability hsig]
  have hh := mul_le_mul_of_nonneg_right hcount
    (show 0≤1+σ^2/(B*ε^2/(L*θ*κ^3))^2 by positivity)
  apply le_trans _ hh
  have hD : cN*L*κ^2*Δ/(B^2*ε^2)≤cN*L*κ^2*Δ/ε^2 := by
    apply div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hε)
    have hm := mul_le_mul_of_nonneg_right (one_le_pow₀ hB1 : 1≤B^2) (sq_nonneg ε)
    simpa only [one_mul] using hm
  have he : (cN/B^2)*(L*κ^2*Δ/ε^2+L^3*θ^2*κ^8*σ^2*Δ/ε^6)=
      cN*L*κ^2*Δ/(B^2*ε^2)+
        (cN*L*κ^2*Δ/ε^2)*(σ^2/(B*ε^2/(L*θ*κ^3))^2) := by
    field_simp
    ring
  rw [he]
  exact (add_le_add_right hD _).trans_eq (by ring)

end Bilevel.MultiscaleMean
