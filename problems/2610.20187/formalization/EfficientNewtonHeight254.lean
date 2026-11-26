import EfficientInverseHeight254
import EfficientSpectralClip254

open scoped Matrix.Norms.Operator
open Matrix
namespace Paper254

theorem certifiedMatrixSqrt_prefix_norm {d : ℕ} (hd : 0<d) (a L s : ℕ)
    (hdim : (d:ℝ)≤(2:ℝ)^a) (A : Matrix (Fin d) (Fin d) ℚ)
    (U : Matrix.unitaryGroup (Fin d) ℝ) (v : Coordinates d)
    (hv : ∀ j,0<v j) (hA : realMatrix A=rotatedPrecision U v)
    (hlo : ∀ j,((2:ℝ)^L)⁻¹≤Real.sqrt (v j))
    (hhi : ∀ j,Real.sqrt (v j)≤(2:ℝ)^L) :
    ∀ k≤matrixSqrtIterations a L s,‖realMatrix (rationalMatrixNewton
      (matrixSqrtPrecision a L s) A ((2:ℚ)^L • 1) k)‖≤(2:ℝ)^(2*a+L+2) := by
  let m := 2*a+L
  let b := 6*a+4*L+1
  let N := matrixSqrtIterations a L s
  let p := matrixSqrtPrecision a L s
  have hp : p=a+(b+1)*N+m+s+2 := rfl
  have hnorm : ‖realMatrix A‖≤(d:ℝ)^2*((2:ℝ)^L)^2 := by
    rw [hA]
    apply rotatedPrecision_norm_bound U v _ (by positivity)
    intro j
    rw [abs_of_pos (hv j)]
    have hh := hhi j
    have hs := Real.sq_sqrt (hv j).le
    nlinarith [Real.sqrt_nonneg (v j)]
  have hM : (d:ℝ)^2/(((2:ℝ)^L)⁻¹)≤(2:ℝ)^m := by
    rw [div_inv_eq_mul]
    have he : (2:ℝ)^m=((2:ℝ)^a)^2*(2:ℝ)^L := by
      dsimp [m]
      rw [pow_add,pow_mul']
    rw [he]
    gcongr
  have hlip : (1+2*((2:ℝ)^m)^2*‖realMatrix A‖)/2≤(2:ℝ)^b := by
    have hdim2 : (d:ℝ)^2≤((2:ℝ)^a)^2 := by gcongr
    have hn := hnorm.trans (mul_le_mul_of_nonneg_right hdim2 (by positivity))
    have hprod := mul_le_mul_of_nonneg_left hn (show 0≤2*((2:ℝ)^m)^2 by positivity)
    have hid : ((2:ℝ)^m)^2*(((2:ℝ)^a)^2*((2:ℝ)^L)^2)=(2:ℝ)^(6*a+4*L) := by
      dsimp [m]
      simp only [pow_add,pow_mul']
      ring
    have hb : (2:ℝ)^b=2*(2:ℝ)^(6*a+4*L) := by dsimp [b]; rw [pow_succ]; ring
    have hone : 1≤(2:ℝ)^(6*a+4*L) := one_le_pow₀ (by norm_num)
    rw [hb]
    nlinarith [hid]
  have hguard0 := dyadic_newton_guard a b m s N (d:ℝ) ((2:ℝ)^m) ((2:ℝ)^b)
    (by positivity) (by positivity) (by positivity) hdim le_rfl le_rfl
  have hsmall : ((2:ℝ)^(s+2))⁻¹≤1/2 := by
    have hh : (2:ℝ)≤2^(s+2) := by
      calc
        _ ≤ (2:ℝ)^2 := by norm_num
        _ ≤ (2:ℝ)^(s+2) := pow_le_pow_right₀ (by norm_num) (by omega)
    simpa only [inv_eq_one_div] using
      (inv_le_inv₀ (by positivity : (0:ℝ)<2^(s+2)) (by norm_num : (0:ℝ)<2)).mpr hh
  have ht := rationalMatrixNewton_sqrt_error hd A U v hv hA ((2:ℚ)^L)
    (((2:ℝ)^L)⁻¹) ((2:ℝ)^m) ((2:ℝ)^b) (by positivity) (by positivity)
    (one_le_pow₀ (by norm_num)) hlo (by simpa using hhi) hM hlip p N
    (by rw [hp]; exact hguard0.trans hsmall)
  intro k hk
  have hpow : (2*((2:ℝ)^b))^k≤(2*((2:ℝ)^b))^N := by
    apply pow_le_pow_right₀ _ hk
    have hh : (1:ℝ)≤2^b := one_le_pow₀ (by norm_num)
    linarith
  have hguardK : (d:ℝ)*((2:ℝ)^p)⁻¹*(2*((2:ℝ)^b))^k*((2:ℝ)^m)≤1/2 := by
    apply le_trans _ (show (d:ℝ)*((2:ℝ)^p)⁻¹*(2*((2:ℝ)^b))^N*((2:ℝ)^m)≤1/2 from ?_)
    · gcongr
    · rw [hp]
      exact hguard0.trans hsmall
  have htK := rationalMatrixNewton_sqrt_error hd A U v hv hA ((2:ℚ)^L)
    (((2:ℝ)^L)⁻¹) ((2:ℝ)^m) ((2:ℝ)^b) (by positivity) (by positivity)
    (one_le_pow₀ (by norm_num)) hlo (by simpa using hhi) hM hlip p k hguardK
  have hrK : (d:ℝ)*((2:ℝ)^p)⁻¹*(2*((2:ℝ)^b))^k≤1/2 := by
    have hm1 : (1:ℝ)≤2^m := one_le_pow₀ (by norm_num)
    have hn0 : (0:ℝ)≤d*((2:ℝ)^p)⁻¹*(2*((2:ℝ)^b))^k := by positivity
    nlinarith
  have hd2 : (d:ℝ)^2*(2:ℝ)^L≤(2:ℝ)^(2*a+L) := by
    rw [pow_add,pow_mul']
    gcongr
  have hhalf : (1/2:ℝ)^k≤1 := pow_le_one₀ (by norm_num) (by norm_num)
  have htail : (d:ℝ)^2*(2:ℝ)^L*(1/2:ℝ)^k≤(2:ℝ)^(2*a+L) := by
    exact (mul_le_of_le_one_right (by positivity) hhalf).trans hd2
  have hroot : ‖rotatedPrecision U (fun j=>Real.sqrt (v j))‖≤(2:ℝ)^(2*a+L) := by
    apply (rotatedPrecision_norm_bound U _ ((2:ℝ)^L) (by positivity) ?_).trans hd2
    intro j
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    exact hhi j
  have htri := norm_le_norm_sub_add (realMatrix (rationalMatrixNewton p A ((2:ℚ)^L • 1) k))
    (rotatedPrecision U (fun j=>Real.sqrt (v j)))
  have herror := htK.2
  push_cast at herror
  have hbase : (1:ℝ)≤2^(2*a+L) := one_le_pow₀ (by norm_num)
  have hexp : (2:ℝ)^(2*a+L+2)=4*(2:ℝ)^(2*a+L) := by rw [pow_add]; norm_num; ring
  change ‖realMatrix (rationalMatrixNewton p A ((2:ℚ)^L • 1) k)‖≤_
  rw [hexp]
  linarith


theorem rationalMatrixNewton_height_of_norm {d : ℕ} (p n B : ℕ)
    (A X : Matrix (Fin d) (Fin d) ℚ)
    (hnorm : ‖realMatrix (rationalMatrixNewton p A X (n+1))‖≤(2:ℝ)^B) :
    MatrixHeight (rationalMatrixNewton p A X (n+1)) (B+p) := by
  have hh := rationalMatrixNewton_numerator_bound p n A X ((2:ℝ)^B) (by positivity) hnorm
  choose Z hrep hZ using hh
  refine ⟨Z,(2:ℤ)^p,pow_ne_zero _ (by norm_num),?_,?_,?_⟩
  · rw [abs_of_pos (by positivity : (0:ℤ)<2^p)]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  · intro i j
    have hz := hZ i j
    rw [←pow_add] at hz
    exact_mod_cast hz
  · intro i j
    simpa using hrep i j

theorem scalar_initial_height (d L : ℕ) :
    MatrixHeight ((2:ℚ)^L • (1:Matrix (Fin d) (Fin d) ℚ)) L := by
  refine ⟨(2:ℤ)^L • (1:Matrix (Fin d) (Fin d) ℤ),1,by norm_num,?_,?_,?_⟩
  · simp only [abs_one]
    exact one_le_pow₀ (by norm_num)
  · intro i j
    simp only [Matrix.smul_apply,smul_eq_mul,Matrix.one_apply]
    split_ifs
    · simp
    · simp
  · intro i j
    simp only [Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,Int.cast_one,div_one]
    split_ifs <;> push_cast <;> simp

def newtonStateHeight (a L s : ℕ) := 2*a+L+2+matrixSqrtPrecision a L s

/-- All stored Newton iterates have polynomial binary size. Every rounding
step restores the same denominator bound, independently of earlier fractions. -/
theorem efficientNewton_prefix_height {d : ℕ} (hd : 0<d) (a L s : ℕ)
    (hdim : (d:ℝ)≤(2:ℝ)^a) (A : Matrix (Fin d) (Fin d) ℚ)
    (U : Matrix.unitaryGroup (Fin d) ℝ) (v : Coordinates d)
    (hv : ∀ j,0<v j) (hA : realMatrix A=rotatedPrecision U v)
    (hlo : ∀ j,((2:ℝ)^L)⁻¹≤Real.sqrt (v j))
    (hhi : ∀ j,Real.sqrt (v j)≤(2:ℝ)^L) (k : ℕ)
    (hk : k≤matrixSqrtIterations a L s) :
    MatrixHeight (efficientNewton (matrixSqrtPrecision a L s) A ((2:ℚ)^L • 1) k)
      (newtonStateHeight a L s) := by
  have hu := certifiedMatrixSqrt_units hd a L s hdim A U v hv hA hlo hhi
  rw [efficientNewton_eq _ _ _ _ (fun j hj=>hu j (by omega))]
  cases k with
  | zero =>
    rw [rationalMatrixNewton_zero]
    exact (scalar_initial_height d L).mono (by dsimp [newtonStateHeight]; omega)
  | succ n =>
    exact rationalMatrixNewton_height_of_norm _ n (2*a+L+2) A _
      (certifiedMatrixSqrt_prefix_norm hd a L s hdim A U v hv hA hlo hhi (n+1) hk)

/-- This includes every exact intermediate matrix inside each inverse call,
even though the rounded Newton iterates themselves need not be symmetric. -/
theorem efficientNewton_inverse_stages_height {d : ℕ} (hd : 0<d) (a L s : ℕ)
    (hdim : (d:ℝ)≤(2:ℝ)^a) (A : Matrix (Fin d) (Fin d) ℚ)
    (U : Matrix.unitaryGroup (Fin d) ℝ) (v : Coordinates d)
    (hv : ∀ j,0<v j) (hA : realMatrix A=rotatedPrecision U v)
    (hlo : ∀ j,((2:ℝ)^L)⁻¹≤Real.sqrt (v j))
    (hhi : ∀ j,Real.sqrt (v j)≤(2:ℝ)^L) (k : ℕ)
    (hk : k<matrixSqrtIterations a L s)
    (S : Matrix (Fin d) (Fin d) ℚ)
    (hS : S=efficientNewton (matrixSqrtPrecision a L s) A ((2:ℚ)^L • 1) k)
    {n : ℕ} (B : Matrix (Fin (n+1)) (Fin (n+1)) ℚ)
    (hB : SchurDescendant (Sᵀ*S) B) :
    SchurStageHeight B (efficientInverse (inverseSchur B))
      (inverseHeight d (2*newtonStateHeight a L s+d)+
        5*inverseHeight d (inverseHeight d (2*newtonStateHeight a L s+d))+2*n+3) := by
  have hu := certifiedMatrixSqrt_units hd a L s hdim A U v hv hA hlo hhi
  have hsheight : MatrixHeight S (newtonStateHeight a L s) := by
    rw [hS]
    exact efficientNewton_prefix_height hd a L s hdim A U v hv hA hlo hhi k hk.le
  have hunit : IsUnit S := by
    rw [hS,efficientNewton_eq _ _ _ _ (fun j hj=>hu j (by omega))]
    exact realMatrix_unit_reflect _ (hu k hk.le)
  exact efficientGeneralInverse_all_stages_height S hunit hsheight B hB

end Paper254
#print axioms Paper254.certifiedMatrixSqrt_prefix_norm
#print axioms Paper254.efficientNewton_prefix_height
#print axioms Paper254.efficientNewton_inverse_stages_height
