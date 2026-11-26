import RationalTaylorHeight254

noncomputable section
namespace Paper254

theorem RationalHeight.real_abs {x : ℚ} {b : ℕ} (hx : RationalHeight x b) :
    |(x:ℝ)|≤(2:ℝ)^b := by
  obtain ⟨Z,q,hq,hqb,hZ,hr⟩ := hx
  have hq1 : (1:ℤ)≤|q| := by have hh := abs_pos.mpr hq; omega
  have hqreal : (1:ℝ)≤|(q:ℝ)| := by exact_mod_cast hq1
  have hzreal : |(Z 0 0:ℝ)|≤(2:ℝ)^b := by exact_mod_cast hZ 0 0
  have hrep : x=(Z 0 0:ℚ)/(q:ℚ) := hr 0 0
  rw [hrep,Rat.cast_div,Rat.cast_intCast,Rat.cast_intCast,abs_div]
  exact (div_le_self (abs_nonneg _) hqreal).trans hzreal

theorem RationalHeight.inverse_real_abs {x : ℚ} {b : ℕ} (hx : RationalHeight x b) :
    |(x:ℝ)⁻¹|≤(2:ℝ)^b := by
  simpa only [Rat.cast_inv] using hx.inv.real_abs

theorem RationalHeight.positive_lower {x : ℚ} {b : ℕ}
    (hx : RationalHeight x b) (hx0 : 0<(x:ℝ)) : ((2:ℝ)^b)⁻¹≤(x:ℝ) := by
  have hi : (x:ℝ)⁻¹≤(2:ℝ)^b := by
    simpa only [abs_of_pos (inv_pos.mpr hx0)] using hx.inverse_real_abs
  have hh := (inv_le_inv₀ (by positivity : (0:ℝ)<2^b) (inv_pos.mpr hx0)).mpr hi
  simpa only [inv_inv] using hh

end Paper254
#print axioms Paper254.RationalHeight.real_abs
#print axioms Paper254.RationalHeight.positive_lower
