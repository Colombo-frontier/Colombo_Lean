import Bilevel.RadialRegularity

/-! Dimension-independent second derivative bounds for the actual compression. -/
noncomputable section
open scoped RealInnerProductSpace
namespace Bilevel.RadialWrapper
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def rankOne (b v : E) : E := ⟪b, v⟫ • b

theorem rankOne_norm_bound (b v : E) : ‖rankOne b v‖ ≤ ‖b‖ ^ 2 * ‖v‖ := by
  rw [rankOne, norm_smul, Real.norm_eq_abs]
  have h := mul_le_mul_of_nonneg_right (abs_real_inner_le_norm b v) (norm_nonneg b)
  nlinarith

theorem rankOne_difference_bound (R : ℝ) (b c v : E)
    (hb : ‖b‖ ≤ R) (hc : ‖c‖ ≤ R) :
    ‖rankOne b v - rankOne c v‖ ≤ 2 * R * ‖b - c‖ * ‖v‖ := by
  have he : rankOne b v - rankOne c v = ⟪b, v⟫ • (b - c) + ⟪b - c, v⟫ • c := by
    simp only [rankOne, inner_sub_left, smul_sub, sub_smul]
    abel
  rw [he]
  calc
    _ ≤ ‖⟪b, v⟫ • (b - c)‖ + ‖⟪b - c, v⟫ • c‖ := norm_add_le _ _
    _ = |⟪b, v⟫| * ‖b - c‖ + |⟪b - c, v⟫| * ‖c‖ := by simp only [norm_smul, Real.norm_eq_abs]
    _ ≤ (R * ‖v‖) * ‖b - c‖ + (‖b - c‖ * ‖v‖) * R := by
      apply add_le_add
      · apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        exact (abs_real_inner_le_norm b v).trans (mul_le_mul_of_nonneg_right hb (norm_nonneg v))
      · exact mul_le_mul (abs_real_inner_le_norm (b - c) v) hc (norm_nonneg c) (by positivity)
    _ = _ := by ring

theorem compressDerivative_rankOne (R : ℝ) (u v : E) :
    compressDerivative R u v =
      scale R u • (v - (R ^ 2)⁻¹ • rankOne (compress R u) v) := by
  simp only [compressDerivative_apply, rankOne, compress, real_inner_smul_left, smul_smul, smul_sub]
  congr 1
  congr 1
  ring

theorem rankOne_compressed_norm (R : ℝ) (hR : 0 < R) (u v : E) :
    ‖rankOne (compress R u) v‖ ≤ R ^ 2 * ‖v‖ := by
  have hb := compress_norm_le_radius R hR u
  exact (rankOne_norm_bound _ v).trans (mul_le_mul_of_nonneg_right
    ((sq_le_sq₀ (norm_nonneg _) hR.le).mpr hb) (norm_nonneg v))

theorem normalizedRank_norm (R : ℝ) (hR : 0 < R) (u v : E) :
    ‖(R ^ 2)⁻¹ • rankOne (compress R u) v‖ ≤ ‖v‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (R ^ 2)⁻¹)]
  calc
    _ ≤ (R ^ 2)⁻¹ * (R ^ 2 * ‖v‖) := mul_le_mul_of_nonneg_left
      (rankOne_compressed_norm R hR u v) (by positivity)
    _ = _ := by field_simp

theorem compressDerivative_difference_apply (R : ℝ) (hR : 0 < R) (u w v : E) :
    ‖(compressDerivative R u - compressDerivative R w) v‖ ≤ (4 / R) * ‖u - w‖ * ‖v‖ := by
  let bu := compress R u
  let bw := compress R w
  let q := v - (R ^ 2)⁻¹ • rankOne bu v
  have hq : ‖q‖ ≤ 2 * ‖v‖ := by
    have ht := norm_sub_le v ((R ^ 2)⁻¹ • rankOne bu v)
    have hn := normalizedRank_norm R hR u v
    dsimp [q, bu] at *
    linarith
  have he : (compressDerivative R u - compressDerivative R w) v =
      (scale R u - scale R w) • q -
        (scale R w / R ^ 2) • (rankOne bu v - rankOne bw v) := by
    simp only [ContinuousLinearMap.sub_apply, compressDerivative_rankOne, q, bu, bw,
      smul_sub, sub_smul, smul_smul]
    rw [div_eq_mul_inv]
    simp only [sub_mul, sub_smul]
    abel
  have ha := (scale_lipschitz R hR).norm_sub_le u w
  change |scale R u - scale R w| ≤ (1 / R) * ‖u - w‖ at ha
  have hb : ‖bu - bw‖ ≤ ‖u - w‖ := by
    simpa only [NNReal.coe_one, one_mul] using (compress_lipschitz R hR).norm_sub_le u w
  have hr : ‖rankOne bu v - rankOne bw v‖ ≤ 2 * R * ‖u - w‖ * ‖v‖ := by
    exact (rankOne_difference_bound R bu bw v
      (compress_norm_le_radius R hR u) (compress_norm_le_radius R hR w)).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb (by positivity)) (norm_nonneg v))
  have hw0 := (scale_pos R w).le
  have hw1 := scale_le_one R w
  have hc : scale R w / R ^ 2 ≤ 1 / R ^ 2 := div_le_div_of_nonneg_right hw1 (sq_nonneg R)
  rw [he]
  calc
    _ ≤ ‖(scale R u - scale R w) • q‖ +
        ‖(scale R w / R ^ 2) • (rankOne bu v - rankOne bw v)‖ := norm_sub_le _ _
    _ = |scale R u - scale R w| * ‖q‖ +
        (scale R w / R ^ 2) * ‖rankOne bu v - rankOne bw v‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg hw0 (sq_nonneg R))]
    _ ≤ ((1 / R) * ‖u - w‖) * (2 * ‖v‖) +
        (1 / R ^ 2) * (2 * R * ‖u - w‖ * ‖v‖) := by
      exact add_le_add (mul_le_mul ha hq (norm_nonneg _) (by positivity))
        (mul_le_mul hc hr (norm_nonneg _) (by positivity))
    _ = _ := by field_simp; ring

theorem compressDerivative_lipschitz (R : ℝ) (hR : 0 < R) :
    LipschitzWith ⟨4 / R, by positivity⟩ (compressDerivative (E := E) R) := by
  apply LipschitzWith.of_dist_le_mul
  intro u w
  simp only [dist_eq_norm]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  exact compressDerivative_difference_apply R hR u w

theorem compressDerivative_contDiff (R : ℝ) (k : ℕ) :
    ContDiff ℝ k (compressDerivative (E := E) R) := by
  have he : compressDerivative (E := E) R = fderiv ℝ (compress R) :=
    funext (fun u => (compress_hasFDerivAt R u).fderiv.symm)
  rw [he]
  exact (compress_contDiff R (k + 1)).fderiv_right (by simp)

theorem second_derivative_norm (R : ℝ) (hR : 0 < R) (u : E) :
    ‖fderiv ℝ (fderiv ℝ (compress R)) u‖ ≤ 4 / R := by
  have he : fderiv ℝ (compress (E := E) R) = compressDerivative R :=
    funext (fun u => (compress_hasFDerivAt R u).fderiv)
  rw [he]
  exact norm_fderiv_le_of_lipschitz ℝ (compressDerivative_lipschitz R hR)

end Bilevel.RadialWrapper
