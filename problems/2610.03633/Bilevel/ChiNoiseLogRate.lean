import Bilevel.ChiFineNoiseRate
import Bilevel.ChiDepthLogBound
import Bilevel.BernoulliOracle

/-! Fixed construction constants give a genuine fixed logarithmic loss
in the actual conservative signal amplitude and revelation probability. -/
noncomputable section
namespace Bilevel.ChiExtensionCalibration

theorem exists_informative_log_factor {Bs Cf t Cb c : ℝ}
    (hBs : 0 < Bs) (hCf : 0 < Cf) (ht : 0 < t) (hCb : 0 < Cb) (hc : 0 < c) :
    ∃ C : ℝ,0 < C ∧ ∃ q : ℕ,∀ θ : ℝ,1 ≤ θ →
      let J := ChiIndependentWidths.chosenDepth θ
      13824*SmallGapLiftSupport.C*Real.exp 2*c*Bs^(J+2)*Cf^(J+1)*(J:ℝ)*((J:ℝ)+1)*Cb^2/t^(2*J) ≤
        C*(Real.log (2+θ))^q := by
  let A := Bs*Cf/t^2
  let C₀ := 13824*SmallGapLiftSupport.C*Real.exp 2*c*Bs^2*Cf*Cb^2
  have hnormal := SmallGapLiftSupport.C_pos
  have hA : 0 < A := by dsimp [A]; positivity
  have hC₀ : 0 < C₀ := by dsimp [C₀]; positivity
  obtain ⟨q,hq⟩ := ChiIndependentWidths.exists_depth_polynomial_log_bound hA.le 2
  refine ⟨4*C₀,by positivity,q+2,?_⟩
  intro θ hθ
  dsimp only
  let J := ChiIndependentWidths.chosenDepth θ
  have he : 13824*SmallGapLiftSupport.C*Real.exp 2*c*Bs^(J+2)*Cf^(J+1)*(J:ℝ)*((J:ℝ)+1)*Cb^2/t^(2*J)=
      C₀*A^J*((J:ℝ)*((J:ℝ)+1)) := by
    dsimp only [A,C₀]
    rw [pow_add Bs J 2,pow_succ Cf J,div_pow,mul_pow,← pow_mul]
    field_simp
    ring
  rw [he]
  have hj : (J:ℝ)*((J:ℝ)+1) ≤ ((J:ℝ)+1)^2 := by have := Nat.cast_nonneg (α:=ℝ) J; nlinarith
  have hh := mul_le_mul_of_nonneg_left (hq θ hθ) hC₀.le
  calc
    _ ≤ C₀*(A^J*((J:ℝ)+1)^2) := by
      convert mul_le_mul_of_nonneg_left hj (mul_nonneg hC₀.le (pow_nonneg hA.le J)) using 1; ring
    _ ≤ _ := by convert hh using 1; ring

theorem inverse_probability_of_signal_bound {B C L θ κ ε σ : ℝ}
    (hB : 0 < B) (hC : 0 < C) (_hL : 0 < L) (_hθ : 0 < θ) (_hκ : 0 < κ) (hε : 0 < ε)
    (hbound : B ≤ C*ε^2/(L*θ*κ^3)) :
    1+(L^2*θ^2*κ^6*σ^2)/(C^2*ε^4) ≤ (BernoulliOracle.probability B σ)⁻¹ := by
  rw [BernoulliOracle.inverse_probability hB]
  apply add_le_add_left
  have hs := pow_le_pow_left₀ hB.le hbound 2
  have hh := div_le_div_of_nonneg_left (sq_nonneg σ) (sq_pos_of_pos hB) hs
  apply le_trans _ hh
  apply le_of_eq
  field_simp
  ring

end Bilevel.ChiExtensionCalibration
