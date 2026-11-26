import MatchingBounds1005.PowerDimension

/-! Explicit logarithmic confidence and cyclic-angle scaling for the source
choice K=ceil(t^(-42)), ε=t³. -/
noncomputable section

namespace MatchingBounds1005.AnalyticFamily

def confidenceExponent (D : ℕ) (t : ℝ) : ℝ :=
  Real.log (4 * (D : ℝ) * (powerCopies t : ℝ) ^ 4)

def angleConstant (H : ℝ) : ℝ := 96 * (12 * H + 7) + 32 * (H + 189)

theorem powerCopies_pos {t : ℝ} (ht : 0 < t) : 0 < powerCopies t := by
  have h := lt_of_lt_of_le (by positivity : (0 : ℝ) < 1 / t ^ 42) (powerCopies_lower (t := t))
  exact_mod_cast h

theorem powerCopies_large {t : ℝ} (ht : 0 < t) (hhalf : t ≤ 1 / 2) : 18 ≤ powerCopies t := by
  have ht1 : t ≤ 1 := by linarith
  have hpow : t ^ 42 ≤ (1 / 32 : ℝ) := by
    calc
      _ ≤ t ^ 5 := pow_le_pow_of_le_one ht.le ht1 (by omega)
      _ ≤ (1 / 2 : ℝ) ^ 5 := pow_le_pow_left₀ ht.le hhalf _
      _ = _ := by norm_num
  have hk := (div_le_iff₀ (pow_pos ht 42)).mp (powerCopies_lower (t := t))
  have hm := mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg (powerCopies t) : (0 : ℝ) ≤ _)
  have hkr : (18 : ℝ) ≤ powerCopies t := by nlinarith only [hk, hm]
  exact_mod_cast hkr

theorem confidenceExponent_nonneg {D : ℕ} (hD : 0 < D) {t : ℝ} (ht : 0 < t) :
    0 ≤ confidenceExponent D t := by
  have hD' : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hK : (1 : ℝ) ≤ powerCopies t := by exact_mod_cast powerCopies_pos ht
  apply Real.log_nonneg
  have hp : (1 : ℝ) ≤ (powerCopies t : ℝ) ^ 4 := one_le_pow₀ hK
  nlinarith

theorem confidenceExponent_bound {D : ℕ} (hD : 0 < D) {H t : ℝ}
    (hH : 0 < H) (ht : 0 < t) (ht1 : t ≤ 1) (hsize : (D : ℝ) ≤ H / t ^ 5) :
    confidenceExponent D t ≤ (H + 189) / t ^ 5 := by
  have hDpos : (0 : ℝ) < D := by exact_mod_cast hD
  have hKpos : (0 : ℝ) < powerCopies t := by exact_mod_cast powerCopies_pos ht
  have hlogD := Real.log_le_log hDpos hsize
  rw [Real.log_div hH.ne' (pow_ne_zero _ ht.ne'), Real.log_pow] at hlogD
  have hKupper : (powerCopies t : ℝ) ≤ 3 / t ^ 42 := by
    have hh := powerCopies_upper ht ht1
    push_cast at hh
    linarith
  have hlogK := Real.log_le_log hKpos hKupper
  rw [Real.log_div (by norm_num : (3 : ℝ) ≠ 0) (pow_ne_zero _ ht.ne'), Real.log_pow] at hlogK
  have hlogH := Real.log_le_sub_one_of_pos hH
  have hlog4 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
  have hlog3 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
  have hlogt := Real.log_le_sub_one_of_pos (inv_pos.mpr ht)
  rw [Real.log_inv] at hlogt
  have hrough : confidenceExponent D t ≤ H + 16 + 173 / t := by
    unfold confidenceExponent
    rw [Real.log_mul (mul_ne_zero (by norm_num) hDpos.ne') (pow_ne_zero _ hKpos.ne'),
      Real.log_mul (by norm_num) hDpos.ne', Real.log_pow]
    norm_num only [Nat.cast_ofNat] at hlogD hlogK ⊢
    simp only [one_div, div_eq_mul_inv]
    nlinarith only [hlogD, hlogK, hlogH, hlog4, hlog3, hlogt]
  have ht5 : t ^ 5 ≤ 1 := pow_le_one₀ ht.le ht1
  have ht4 : t ^ 4 ≤ 1 := pow_le_one₀ ht.le ht1
  have h1 : (1 : ℝ) ≤ 1 / t ^ 5 := (le_div_iff₀ (pow_pos ht 5)).mpr (by linarith)
  have hinv : (1 : ℝ) / t ≤ 1 / t ^ 5 := by
    apply one_div_le_one_div_of_le (pow_pos ht 5)
    nlinarith only [mul_le_mul_of_nonneg_left ht4 ht.le]
  have hc := mul_le_mul_of_nonneg_left h1 (show 0 ≤ H + 16 by linarith)
  have hv := mul_le_mul_of_nonneg_left hinv (by norm_num : (0 : ℝ) ≤ 173)
  apply hrough.trans
  calc
    _ = (H + 16) * 1 + 173 * (1 / t) := by ring
    _ ≤ (H + 16) * (1 / t ^ 5) + 173 * (1 / t ^ 5) := add_le_add hc hv
    _ = _ := by ring

theorem angleConstant_pos {H : ℝ} (hH : 0 < H) : 0 < angleConstant H := by
  unfold angleConstant
  positivity

theorem geometric_numerator_bound {D k : ℕ} (hD : 0 < D) {H t : ℝ}
    (hH : 0 < H) (ht : 0 < t) (ht1 : t ≤ 1) (hsize : (D : ℝ) ≤ H / t ^ 5)
    (hk : k ≤ 12 * D + 6) :
    96 * ((k : ℝ) + 1) + 32 * confidenceExponent D t ≤ angleConstant H / t ^ 5 := by
  have hs := confidenceExponent_bound hD hH ht ht1 hsize
  have hk' : (k : ℝ) ≤ 12 * (D : ℝ) + 6 := by exact_mod_cast hk
  have ht5 : t ^ 5 ≤ 1 := pow_le_one₀ ht.le ht1
  have h1 : (1 : ℝ) ≤ 1 / t ^ 5 := (le_div_iff₀ (pow_pos ht 5)).mpr (by linarith)
  have hk'' : (k : ℝ) + 1 ≤ (12 * H + 7) / t ^ 5 := by
    calc
      _ ≤ 12 * (D : ℝ) + 7 := by linarith only [hk']
      _ ≤ 12 * (H / t ^ 5) + 7 * (1 / t ^ 5) := by nlinarith only [hsize, h1]
      _ = _ := by ring
  unfold angleConstant
  calc
    _ ≤ 96 * ((12 * H + 7) / t ^ 5) + 32 * ((H + 189) / t ^ 5) :=
      add_le_add (mul_le_mul_of_nonneg_left hk'' (by norm_num))
        (mul_le_mul_of_nonneg_left hs (by norm_num))
    _ = _ := by ring

def geometricAngle (D k : ℕ) (t : ℝ) : ℝ :=
  Real.sqrt ((96 * ((k : ℝ) + 1) + 32 * confidenceExponent D t) / (powerCopies t + 1 : ℕ))

theorem geometricAngle_sq {D k : ℕ} (hD : 0 < D) {t : ℝ} (ht : 0 < t) :
    geometricAngle D k t ^ 2 =
      (96 * ((k : ℝ) + 1) + 32 * confidenceExponent D t) / (powerCopies t + 1 : ℕ) := by
  unfold geometricAngle
  apply Real.sq_sqrt
  have hs := confidenceExponent_nonneg hD ht
  positivity

theorem geometricAngle_bound {D k : ℕ} (hD : 0 < D) {H t : ℝ}
    (hH : 0 < H) (ht : 0 < t) (ht1 : t ≤ 1) (hsize : (D : ℝ) ≤ H / t ^ 5)
    (hk : k ≤ 12 * D + 6) : geometricAngle D k t ^ 2 ≤ angleConstant H * t ^ 37 := by
  rw [geometricAngle_sq hD ht]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < (powerCopies t + 1 : ℕ))).mpr
  have hn := geometric_numerator_bound hD hH ht ht1 hsize hk
  have hK : 1 / t ^ 42 ≤ ((powerCopies t + 1 : ℕ) : ℝ) := by
    have h := powerCopies_lower (t := t)
    push_cast
    linarith
  have hm := mul_le_mul_of_nonneg_left hK
    (show 0 ≤ angleConstant H * t ^ 37 by have h := angleConstant_pos hH; positivity)
  have he : angleConstant H * t ^ 37 * (1 / t ^ 42) = angleConstant H / t ^ 5 := by
    rw [show (42 : ℕ) = 37 + 5 by omega, pow_add]
    field_simp [ht.ne']
    ring
  rw [he] at hm
  exact hn.trans hm

theorem geometricAngle_nonneg (D k : ℕ) (t : ℝ) : 0 ≤ geometricAngle D k t :=
  Real.sqrt_nonneg _

theorem geometricAngle_half {D k : ℕ} (hD : 0 < D) {H t : ℝ}
    (hH : 0 < H) (ht : 0 < t) (ht1 : t ≤ 1) (hsize : (D : ℝ) ≤ H / t ^ 5)
    (hk : k ≤ 12 * D + 6) (hsmall : t ≤ 1 / (4 * angleConstant H)) :
    geometricAngle D k t ≤ 1 / 2 := by
  have hbound := geometricAngle_bound hD hH ht ht1 hsize hk
  have hC := angleConstant_pos hH
  have ht36 : t ^ 36 ≤ 1 := pow_le_one₀ ht.le ht1
  have ht37 : t ^ 37 ≤ t := by nlinarith only [mul_le_mul_of_nonneg_left ht36 ht.le]
  have hm := mul_le_mul_of_nonneg_left ht37 hC.le
  have hsmall' := (le_div_iff₀ (by positivity : 0 < 4 * angleConstant H)).mp hsmall
  nlinarith only [hbound, hm, hsmall', geometricAngle_nonneg D k t]

theorem geometricAngle_multiplicity {D k : ℕ} (hD : 0 < D) {t : ℝ} (ht : 0 < t) :
    96 * ((k : ℝ) + 1) + 32 * confidenceExponent D t ≤
      ((powerCopies t + 1 : ℕ) : ℝ) * geometricAngle D k t ^ 2 := by
  rw [geometricAngle_sq hD ht]
  exact le_of_eq (by field_simp [show ((powerCopies t + 1 : ℕ) : ℝ) ≠ 0 by positivity])

theorem confidence_failure_exact {D : ℕ} (hD : 0 < D) {t : ℝ} (ht : 0 < t) :
    4 * (D : ℝ) * Real.exp (-confidenceExponent D t) = 1 / (powerCopies t : ℝ) ^ 4 := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hK : (0 : ℝ) < powerCopies t := by exact_mod_cast powerCopies_pos ht
  unfold confidenceExponent
  rw [Real.exp_neg, Real.exp_log (by positivity : 0 < 4 * (D : ℝ) * (powerCopies t : ℝ) ^ 4)]
  field_simp

end MatchingBounds1005.AnalyticFamily

namespace MatchingBounds1005.BlockGeometry
open AnalyticFamily GaussianMatrix GaussianBlockGeometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem power_copy_dimension_room (n k : ℕ) (hD : 0 < baseDimension (E := E) n)
    (hk : k ≤ 12 * baseDimension (E := E) n + 6) {t : ℝ}
    (ht : 0 < t) (hhalf : t ≤ 1 / 2) :
    k ≤ copyDimension (E := E) n (powerCopies t) := by
  rw [copyDimension_eq]
  have hK := powerCopies_large ht hhalf
  have hm : 19 * baseDimension (E := E) n ≤ (powerCopies t + 1) * baseDimension (E := E) n :=
    Nat.mul_le_mul_right _ (by omega)
  omega

theorem power_chain_angle_failure (G : BlockGeometry E) (n k : ℕ)
    (hD : 0 < baseDimension (E := E) n) {t : ℝ} (ht : 0 < t)
    (hhalf : geometricAngle (baseDimension (E := E) n) k t ≤ 1 / 2) :
    (gaussianMatrixLaw (copyDimension (E := E) n (powerCopies t)) k).real
      {g | ¬ CyclicAngleGood (copyAmbientActiveSpace n (powerCopies t))
        (G.copyAmbientOperator n (powerCopies t)) g (geometricAngle (baseDimension (E := E) n) k t)} ≤
      1 / (powerCopies t : ℝ) ^ 4 := by
  have h := G.chain_copy_high_multiplicity n (powerCopies t) k
    (geometricAngle_nonneg _ _ _) hhalf (confidenceExponent_nonneg hD ht)
    (geometricAngle_multiplicity hD ht)
  rwa [confidence_failure_exact hD ht] at h

end MatchingBounds1005.BlockGeometry
