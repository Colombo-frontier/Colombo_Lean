import SecondOrder.UpperDimension

namespace SecondOrder
noncomputable section

/-- Only the dimension and confidence logarithms remain in this factor;
the full physical scale is B²/γ². -/
def ojaFullPriceFactor (d : ℕ) (δ : ℝ) : ℝ :=
  400*(104976+4000*2336)*(1+Real.log (4*(d:ℝ)))^2*(ojaConfidenceLog δ)^2

theorem ojaFullPriceFactor_nonneg (d : ℕ) (δ : ℝ) : 0 ≤ ojaFullPriceFactor d δ := by
  unfold ojaFullPriceFactor
  positivity

theorem hessianBound_le_eigenHessianBound (P : Parameters) :
    P.hessianBound ≤ eigenHessianBound P := by
  unfold eigenHessianBound
  linarith [P.gradientLip_pos]

/-- Full-scale curvature price. The ceiling overhead is absorbed using
γ≤4B, so neither an extra variance parameter nor γ≤1 is required. -/
theorem ojaAmplifiedQueryCount_full_bound (P : Parameters) {d : ℕ} (hd : 0 < d)
    {γ δ : ℝ} (hγ : 0 < γ) (hγB : γ ≤ 4*eigenHessianBound P)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (ojaAmplifiedQueryCount P d γ δ : ℝ) ≤
      ojaFullPriceFactor d δ*(eigenHessianBound P)^2/γ^2 := by
  let D := (1+Real.log (4*(d:ℝ)))^2
  let U := (eigenHessianBound P)^2*D/γ^2
  let L := ojaConfidenceLog δ
  have hD : 1 ≤ D := one_le_pow₀ (one_le_dimensionLog hd)
  have hU : 0 ≤ U := by dsimp only [U, D]; positivity
  have hL : 1 ≤ L := one_le_ojaConfidenceLog hδ hδ1
  have hB := eigenHessianBound_pos P
  have hbar := pow_le_pow_left₀ P.hessianBound_pos.le (hessianBound_le_eigenHessianBound P) 2
  have hγ2 := pow_le_pow_left₀ hγ.le hγB 2
  have htwo : (2:ℝ) ≤ 32*(eigenHessianBound P)^2/γ^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hγ)).mpr
    nlinarith
  have hu : (eigenHessianBound P)^2/γ^2 ≤ U := by
    exact div_le_div_of_nonneg_right
      (le_mul_of_one_le_right (sq_nonneg _) hD) (sq_nonneg γ)
  have hv : 2304*P.hessianBound^2/γ^2+2 ≤ 2336*U := by
    have hh := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hbar (by norm_num : (0:ℝ) ≤ 2304)) (sq_nonneg γ)
    calc
      _ ≤ 2304*(eigenHessianBound P)^2/γ^2+32*(eigenHessianBound P)^2/γ^2 := add_le_add hh htwo
      _ = 2336*((eigenHessianBound P)^2/γ^2) := by ring
      _ ≤ 2336*U := mul_le_mul_of_nonneg_left hu (by norm_num)
  have hf : 0 ≤ 8*Real.log (1/ojaValidationFailure δ)+2 :=
    chordConfidenceFactor_nonneg (ojaValidationFailure_pos hδ)
      ((ojaValidationFailure_le hδ1).trans (by norm_num))
  have hvl := mul_le_mul hv (ojaValidation_confidenceLog hδ hδ1) hf (by positivity : 0 ≤ 2336*U)
  have hb := ojaAmplifiedQueryCount_bound P hd hγ hγB hδ hδ1
  have he : 104976*(eigenHessianBound P)^2*(1+Real.log (4*(d:ℝ)))^2/γ^2 = 104976*U := by
    dsimp only [U, D]
    ring
  rw [he] at hb
  have hr := mul_le_mul (ojaRepeats_confidenceLog hδ hδ1)
    (add_le_add_left hvl (104976*U)) (by positivity) (by positivity : 0 ≤ 400*L)
  have hUL := mul_nonneg hU (sub_nonneg.mpr hL)
  have hlast : 400*L*(104976*U+2336*U*(4000*L)) ≤
      400*(104976+4000*2336)*U*L^2 := by
    nlinarith [mul_nonneg (show 0 ≤ L by linarith) hUL]
  exact hb.trans (hr.trans (hlast.trans_eq (by dsimp only [U, D, L, ojaFullPriceFactor]; ring)))

theorem branchedOjaQueryCount_full_bound (P : Parameters) (d : ℕ)
    {γ δ : ℝ} (hγ : 0 < γ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (branchedOjaQueryCount P d γ δ : ℝ) ≤
      ojaFullPriceFactor d δ*(eigenHessianBound P)^2/γ^2 := by
  by_cases hc : zeroQueryCurvatureCase P d γ
  · simp only [branchedOjaQueryCount, if_pos hc, Nat.cast_zero]
    exact div_nonneg (mul_nonneg (ojaFullPriceFactor_nonneg d δ) (sq_nonneg _)) (sq_nonneg γ)
  · simpa only [branchedOjaQueryCount, if_neg hc] using
      ojaAmplifiedQueryCount_full_bound P (not_zeroQueryCurvatureCase_dimension hc) hγ
        (not_zeroQueryCurvatureCase_tolerance hc) hδ hδ1

end
end SecondOrder
