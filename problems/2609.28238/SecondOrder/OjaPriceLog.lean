import SecondOrder.OjaAmplifiedCost

namespace SecondOrder
noncomputable section

def ojaConfidenceLog (δ : ℝ) : ℝ := 1+Real.log (1/δ)

def ojaPriceCoefficient (P : Parameters) (d : ℕ) : ℝ :=
  400*(104976*(eigenHessianBound P)^2*(1+Real.log (4*(d:ℝ)))^2 +
    4000*(2304*P.hessianBound^2+2))

theorem ojaPriceCoefficient_pos (P : Parameters) (d : ℕ) : 0 < ojaPriceCoefficient P d := by
  unfold ojaPriceCoefficient
  positivity

theorem one_le_ojaConfidenceLog {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) : 1 ≤ ojaConfidenceLog δ := by
  have hl := Real.log_nonneg ((le_div_iff₀ hδ).mpr (by simpa using hδ1))
  unfold ojaConfidenceLog
  linarith

theorem ojaRepeats_confidenceLog {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (ojaRepeats δ:ℝ) ≤ 400*ojaConfidenceLog δ := by
  have hR := ojaRepeats_bound hδ hδ1
  have hL := one_le_ojaConfidenceLog hδ hδ1
  have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
  have he : Real.log (2/δ) = Real.log 2+Real.log (1/δ) := by
    rw [Real.log_div (by norm_num) hδ.ne', Real.log_div one_ne_zero hδ.ne', Real.log_one]
    ring
  rw [he] at hR
  unfold ojaConfidenceLog at *
  linarith

theorem ojaValidation_log_identity {δ : ℝ} (hδ : 0 < δ) :
    Real.log (1/ojaValidationFailure δ) =
      Real.log 2+Real.log (ojaRepeats δ:ℝ)+Real.log (1/δ) := by
  have hR : (0:ℝ) < ojaRepeats δ := Nat.cast_pos.mpr (ojaRepeats_pos δ)
  have he : 1/ojaValidationFailure δ = 2*(ojaRepeats δ:ℝ)*(1/δ) := by
    unfold ojaValidationFailure
    field_simp
  rw [he, Real.log_mul (by positivity : (2*(ojaRepeats δ:ℝ)) ≠ 0) (by positivity),
    Real.log_mul (by norm_num) hR.ne']

theorem ojaValidation_confidenceLog {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    8*Real.log (1/ojaValidationFailure δ)+2 ≤ 4000*ojaConfidenceLog δ := by
  have hR := ojaRepeats_confidenceLog hδ hδ1
  have hL := one_le_ojaConfidenceLog hδ hδ1
  have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
  have hr := Real.log_le_sub_one_of_pos (Nat.cast_pos.mpr (ojaRepeats_pos δ))
  rw [ojaValidation_log_identity hδ]
  unfold ojaConfidenceLog at *
  linarith

/-- The complete candidate/validation/repetition price is quadratic in
the confidence logarithm, with explicit logarithmic dimension dependence. -/
theorem ojaAmplifiedQueryCount_log_bound (P : Parameters) {d : ℕ} (hd : 0 < d)
    {γ δ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hγB : γ ≤ 4*eigenHessianBound P)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (ojaAmplifiedQueryCount P d γ δ:ℝ) ≤
      ojaPriceCoefficient P d*(ojaConfidenceLog δ)^2/γ^2 := by
  let A := 104976*(eigenHessianBound P)^2*(1+Real.log (4*(d:ℝ)))^2
  let D := 2304*P.hessianBound^2+2
  let L := ojaConfidenceLog δ
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hL : 1 ≤ L := one_le_ojaConfidenceLog hδ hδ1
  have hL0 : 0 ≤ L := by linarith
  have hV : 2304*P.hessianBound^2/γ^2+2 ≤ D/γ^2 := by
    have hγ2 : γ^2 ≤ 1 := pow_le_one₀ hγ.le hγ1
    have htwo : (2:ℝ) ≤ 2/γ^2 := (le_div_iff₀ (sq_pos_of_pos hγ)).mpr (by nlinarith)
    simpa only [D, add_div] using add_le_add_left htwo (2304*P.hessianBound^2/γ^2)
  have hfactor : 0 ≤ 8*Real.log (1/ojaValidationFailure δ)+2 := by
    have hα1 : ojaValidationFailure δ ≤ 1 := (ojaValidationFailure_le hδ1).trans (by norm_num)
    have hl := Real.log_nonneg ((le_div_iff₀ (ojaValidationFailure_pos hδ)).mpr (by simpa using hα1))
    linarith
  have hi := mul_le_mul hV (ojaValidation_confidenceLog hδ hδ1) hfactor
    (div_nonneg hD (sq_nonneg γ))
  have hR := ojaRepeats_confidenceLog hδ hδ1
  have hprice := ojaAmplifiedQueryCount_bound P hd hγ hγB hδ hδ1
  have hbase : 0 ≤ A/γ^2+(2304*P.hessianBound^2/γ^2+2)*
      (8*Real.log (1/ojaValidationFailure δ)+2) := by positivity
  have hall := mul_le_mul hR (add_le_add_left hi (A/γ^2)) hbase (by positivity : 0 ≤ 400*L)
  have hAL := mul_le_mul_of_nonneg_left hL hA
  have hb : 400*L*(A/γ^2+D/γ^2*(4000*L)) ≤
      400*(A+4000*D)*L^2/γ^2 := by
    calc
      _ = (400*L*(A+D*(4000*L)))/γ^2 := by ring
      _ ≤ (400*(A+4000*D)*L^2)/γ^2 :=
        div_le_div_of_nonneg_right (by nlinarith [mul_nonneg (sub_nonneg.mpr hAL) hL0]) (sq_nonneg γ)
  exact hprice.trans (hall.trans hb)

end
end SecondOrder
