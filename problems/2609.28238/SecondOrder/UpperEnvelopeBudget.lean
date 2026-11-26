import SecondOrder.UpperDimension
import SecondOrder.MinimaxComplexity

namespace SecondOrder
noncomputable section

def envelopeDimensionLogCoefficient (κ : ℝ) : ℝ := 1+Real.log 8+κ

theorem envelopeDimensionLogCoefficient_pos {κ : ℝ} (hκ : 0≤κ) :
    0<envelopeDimensionLogCoefficient κ := by
  have hl : 0≤Real.log 8 := Real.log_nonneg (by norm_num)
  unfold envelopeDimensionLogCoefficient
  positivity

/-- The ceiling in the manuscript's dimension range adds a fixed constant
inside the logarithm, rather than a polynomial dimension loss. -/
theorem toleranceEnvelope_dimensionLog {κ ε γ : ℝ} {d : ℕ}
    (hκ : 0≤κ) (hε : 0<ε) (hε1 : ε≤1) (hγ : 0<γ) (hγ1 : γ≤1)
    (hd : 0<d) (hD : d≤toleranceDimensionEnvelope κ ε γ) :
    1+Real.log (4*(d:ℝ))≤envelopeDimensionLogCoefficient κ*toleranceLog ε γ := by
  let x := (ε*γ)^(-κ)
  have hprod : ε*γ≤1 := mul_le_one₀ hε1 hγ.le hγ1
  have hx : 1≤x := Real.one_le_rpow_of_pos_of_le_one_of_nonpos (mul_pos hε hγ) hprod (neg_nonpos.mpr hκ)
  have hceil := Nat.ceil_lt_add_one (show 0≤x by linarith only [hx])
  have hcast : (d:ℝ)≤(⌈x⌉₊:ℝ) := by exact_mod_cast hD
  have hd' : (0:ℝ)<d := by exact_mod_cast hd
  have hscale : 4*(d:ℝ)≤8*x := by linarith only [hcast,hceil,hx]
  have hl := Real.log_le_log (by positivity : 0<4*(d:ℝ)) hscale
  have hid : Real.log (8*x)=Real.log 8+κ*(Real.log (1/ε)+Real.log (1/γ)) := by
    dsimp only [x]
    rw [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos (mul_pos hε hγ) _).ne',
      Real.log_rpow (mul_pos hε hγ),Real.log_mul hε.ne' hγ.ne']
    simp only [one_div,Real.log_inv]
    ring
  rw [hid] at hl
  have hj := one_le_toleranceLog hε hε1 hγ hγ1
  have hlog : 0≤Real.log 8 := Real.log_nonneg (by norm_num)
  have hA : 0≤1+Real.log 8 := by linarith only [hlog]
  have hm := mul_le_mul_of_nonneg_left hj hA
  unfold envelopeDimensionLogCoefficient toleranceLog at *
  nlinarith only [hl,hm,hκ]

def stochasticEnvelopeCoefficient (P : Parameters) (ν κ : ℝ) : ℝ :=
  stochasticDimensionFreeCoefficient P ν*(envelopeDimensionLogCoefficient κ)^2

theorem stochasticEnvelopeCoefficient_pos (P : Parameters) {ν κ : ℝ}
    (hν : 0<ν) (hκ : 0≤κ) : 0<stochasticEnvelopeCoefficient P ν κ := by
  exact mul_pos (stochasticDimensionFreeCoefficient_pos P hν)
    (pow_pos (envelopeDimensionLogCoefficient_pos hκ) 2)

/-- The actual deterministic cap of the analyzed upper program is uniformly
bounded by a sixth-power tolerance logarithm throughout the dimension range. -/
theorem stochasticUpperCap_envelope_rate (P : Parameters) {ν κ ε γ : ℝ} {d : ℕ}
    (hν : 0<ν) (hκ : 0≤κ) (hε : 0<ε) (hε1 : ε≤1) (hγ : 0<γ) (hγ1 : γ≤1)
    (hd : 0<d) (hD : d≤toleranceDimensionEnvelope κ ε γ) :
    (stochasticUpperCap P ν d ε γ:ℝ)<
      stochasticEnvelopeCoefficient P ν κ*(toleranceLog ε γ)^6*holderEndpointRate ν ε γ := by
  have hc := stochasticUpperCoefficient_dimension P hν hd
  have hdim := toleranceEnvelope_dimensionLog hκ hε hε1 hγ hγ1 hd hD
  have hp := pow_le_pow_left₀ (by linarith only [one_le_dimensionLog hd]) hdim 2
  have hf := hc.trans (mul_le_mul_of_nonneg_left hp (stochasticDimensionFreeCoefficient_pos P hν).le)
  have hj := one_le_toleranceLog hε hε1 hγ hγ1
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hf (pow_nonneg (by linarith only [hj]) 4))
    (holderEndpointRate_pos ν hε hγ).le
  apply (stochasticUpperCap_rate P d hν hε hε1 hγ hγ1).trans_le
  apply hh.trans_eq
  unfold stochasticEnvelopeCoefficient
  ring

end
end SecondOrder
