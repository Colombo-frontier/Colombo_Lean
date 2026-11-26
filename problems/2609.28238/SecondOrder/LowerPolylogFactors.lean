import SecondOrder.RichEnvelopeLower
import SecondOrder.ToleranceLogBounds

namespace SecondOrder
noncomputable section

/-- A fixed coefficient for the actual rounded curvature block size. -/
def curvatureBlockLogCoefficient (Δ L σ ν : ℝ) : ℝ :=
  131072*Real.log (curvatureHolderEnvelopeConstant Δ L σ ν)+2+131072*(3+2/ν)

theorem curvatureBlockLogCoefficient_pos {Δ L σ ν : ℝ}
    (hΔ : 0≤Δ) (hL : 0<L) (hν : 0<ν) :
    0<curvatureBlockLogCoefficient Δ L σ ν := by
  have he : 1≤curvatureHolderEnvelopeConstant Δ L σ ν := by
    unfold curvatureHolderEnvelopeConstant
    have h1 : 0≤Δ*L^(2/ν) := by positivity
    have h2 : 0≤Δ*σ^2*L^(2/ν) := by positivity
    linarith only [h1,h2]
  have hl := Real.log_nonneg he
  unfold curvatureBlockLogCoefficient
  positivity

theorem curvatureHolderBlockSize_le_toleranceLog {Δ L σ ν ε γ : ℝ}
    (hΔ : 0≤Δ) (hL : 0<L) (hν : 0<ν) (hν1 : ν≤1)
    (hε : 0<ε) (hε1 : ε≤1) (hγ : 0<γ) (hγ1 : γ≤1) :
    (curvatureHolderBlockSize Δ L σ γ ν:ℝ)≤
      curvatureBlockLogCoefficient Δ L σ ν*toleranceLog ε γ := by
  have hh := curvatureHolderBlockSize_log_bound (σ := σ) hΔ hL hγ hγ1 hν hν1
  have hj := one_le_toleranceLog hε hε1 hγ hγ1
  have ht := toleranceLog_terms hε hε1 hγ hγ1
  have he : 1≤curvatureHolderEnvelopeConstant Δ L σ ν := by
    unfold curvatureHolderEnvelopeConstant
    have h1 : 0≤Δ*L^(2/ν) := by positivity
    have h2 : 0≤Δ*σ^2*L^(2/ν) := by positivity
    linarith only [h1,h2]
  have hA : 0≤131072*Real.log (curvatureHolderEnvelopeConstant Δ L σ ν)+2 := by
    have hl := Real.log_nonneg he
    positivity
  have hB : 0≤131072*(3+2/ν) := by positivity
  have hlog : -Real.log γ≤toleranceLog ε γ := by
    simp only [one_div,Real.log_inv] at ht
    unfold toleranceLog
    simp only [one_div,Real.log_inv]
    linarith only [ht.1]
  have ha := mul_le_mul_of_nonneg_left hj hA
  have hb := mul_le_mul_of_nonneg_left hlog hB
  unfold curvatureBlockLogCoefficient
  nlinarith only [hh,ha,hb]

theorem curvatureEndpointBlockSize_le_toleranceLog {Δ L σ ε γ : ℝ}
    (hΔ : 0≤Δ) (hL : 0<L)
    (hε : 0<ε) (hε1 : ε≤1) (hγ : 0<γ) (hγ1 : γ≤1) :
    (curvatureEndpointBlockSize Δ L σ γ:ℝ)≤
      curvatureBlockLogCoefficient Δ (2*L) σ 1*toleranceLog ε γ := by
  rw [curvatureEndpointBlockSize_holder hγ]
  exact curvatureHolderBlockSize_le_toleranceLog hΔ (by positivity) (by norm_num)
    (le_refl _) hε hε1 hγ hγ1

theorem firstOrderEndpointThreshold_scale (Δ s ε : ℝ) :
    firstOrderEndpointThreshold Δ s ε=firstOrderEndpointThreshold Δ s 1/ε^3 := by
  unfold firstOrderEndpointThreshold
  ring

theorem curvatureHolderThreshold_scale {Δ L σ D γ ν : ℝ} (hγ : 0<γ) :
    curvatureHolderThreshold Δ L σ D γ ν=
      curvatureHolderThreshold Δ L σ 1 1 ν/D^2*γ^(-holderRateExponent ν) := by
  unfold curvatureHolderThreshold holderRateExponent
  rw [Real.rpow_neg hγ.le]
  simp only [one_pow,Real.one_rpow,mul_one]
  ring

theorem curvatureEndpointThreshold_scale {Δ L σ D γ : ℝ} (hγ : 0<γ) :
    curvatureEndpointThreshold Δ L σ D γ=
      curvatureEndpointThreshold Δ L σ 1 1/D^2*γ^(-holderRateExponent 1) := by
  unfold curvatureEndpointThreshold holderRateExponent
  norm_num only [div_one,one_pow,mul_one]
  rw [Real.rpow_neg hγ.le]
  rw [show (γ ^ (5:ℝ)) = γ ^ (5:ℕ) from Real.rpow_natCast γ 5]
  ring

/-- Replacing a positive block size by its logarithmic upper bound only
weakens the inverse-square coefficient in the lower bound. -/
theorem inverse_block_sq_lower {a D K J : ℝ}
    (ha : 0≤a) (hD : 0<D) (hK : 0<K) (hJ : 0<J) (hDK : D≤K*J) :
    (a/K^2)/J^2≤a/D^2 := by
  have hs : D^2≤(K*J)^2 := pow_le_pow_left₀ hD.le hDK 2
  have hh := div_le_div_of_nonneg_left ha (pow_pos hD 2) hs
  calc
    (a/K^2)/J^2 = a/(K*J)^2 := by ring
    _ ≤ a/D^2 := hh

/-- A common positive coefficient combines the two endpoint lower bounds
without imposing any relation between the two tolerances. -/
theorem endpoint_half_sum_polylog {a b J X Y A B : ℝ}
    (ha : 0≤a) (hb : 0≤b) (hJ : 1≤J) (hX : 0≤X) (hY : 0≤Y)
    (hA : a*X≤A) (hB : (b/J^2)*Y≤B) :
    ((min a b)/2)/J^2*(X+Y)≤(A+B)/2 := by
  have hJ0 : 0<J := lt_of_lt_of_le (by norm_num) hJ
  have hJ2 : 1≤J^2 := one_le_pow₀ hJ
  have ham : min a b/J^2≤a := by
    apply (div_le_self (le_min ha hb) hJ2).trans
    exact min_le_left _ _
  have hbm : min a b/J^2≤b/J^2 :=
    div_le_div_of_nonneg_right (min_le_right _ _) (sq_nonneg J)
  have hx := (mul_le_mul_of_nonneg_right ham hX).trans hA
  have hy := (mul_le_mul_of_nonneg_right hbm hY).trans hB
  calc
    ((min a b)/2)/J^2*(X+Y) = ((min a b/J^2)*X+(min a b/J^2)*Y)/2 := by ring
    _ ≤ (A+B)/2 := div_le_div_of_nonneg_right (add_le_add hx hy) (by norm_num)

end
end SecondOrder
