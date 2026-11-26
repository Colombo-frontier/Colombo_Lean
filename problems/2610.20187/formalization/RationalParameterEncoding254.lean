import RationalPredictionHeight254
import RationalScaleGrid254
import UniformHistoryGuards254

noncomputable section
namespace Paper254

theorem rationalTwoPow_height (n : ℕ) : RationalHeight ((2:ℚ)^n) n := by
  have hh := RationalHeight.of_int ((2:ℤ)^n) n
    (by rw [abs_of_pos (by positivity : (0:ℤ)<2^n)])
  simpa using hh

theorem rationalCappedVariance_height (H : ℚ) (b K k : ℕ) (hH : RationalHeight H b)
    (hk : k≤K) : RationalHeight (rationalCappedVariance H k) (b+2*(K+1)+1) := by
  have hpow : ((2:ℚ)^k)^2=(2:ℚ)^(2*k) := by rw [←pow_mul]; congr 1; omega
  have hleft : RationalHeight (H/((2:ℚ)^k)^2) (b+2*k+1) := by
    rw [hpow,div_eq_mul_inv]
    exact hH.mul (rationalTwoPow_height (2*k)).inv
  have hright : RationalHeight (H/4) (b+2+1) := by
    have hh := hH.mul (rationalTwoPow_height 2).inv
    norm_num only [pow_two] at hh
    simpa only [div_eq_mul_inv,one_mul] using hh
  unfold rationalCappedVariance
  rcases le_total (H/((2:ℚ)^k)^2) (H/4) with h | h
  · rw [min_eq_left h]
    exact hleft.mono (by omega)
  · rw [min_eq_right h]
    exact hright.mono (by omega)

theorem uniformHistoryParameters_height (a b r p B : ℕ) (lo hi : ℚ)
    (hlo : RationalHeight lo B) (hhi : RationalHeight hi B) :
    let cfg := uniformHistoryParameters a b r p lo hi
    RationalHeight cfg.smoothing (B+3*a+b+2*r+10) ∧
      RationalHeight cfg.lowerThreshold (B+3*a+b+2*r+10) ∧
      RationalHeight cfg.upperThreshold (B+3*a+b+2*r+10) := by
  dsimp only [uniformHistoryParameters]
  refine ⟨(rationalTwoPow_height (3*a+b+r+6)).inv.mono (by omega),?_,?_⟩
  · exact (hlo.add (rationalTwoPow_height (r+2)).inv).mono (by omega)
  · exact (hhi.sub (rationalTwoPow_height (r+2)).inv).mono (by omega)

end Paper254
#print axioms Paper254.rationalCappedVariance_height
#print axioms Paper254.uniformHistoryParameters_height
