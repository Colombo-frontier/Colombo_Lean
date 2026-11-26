import MatrixSqrtApprox254

open scoped Matrix.Norms.Operator BigOperators
open Matrix
namespace Paper254

def matrixSqrtIterations (a L s : ℕ) : ℕ := 2*a+L+s+2
def matrixSqrtPrecision (a L s : ℕ) : ℕ :=
  a+(6*a+4*L+2)*matrixSqrtIterations a L s+(2*a+L)+s+2

def certifiedMatrixSqrt {d : ℕ} (a L s : ℕ) (A : Matrix (Fin d) (Fin d) ℚ) :=
  rationalMatrixNewton (matrixSqrtPrecision a L s) A ((2:ℚ)^L • 1)
    (matrixSqrtIterations a L s)

theorem certifiedMatrixSqrt_error {d : ℕ} (hd : 0<d) (a L s : ℕ)
    (hdim : (d:ℝ)≤(2:ℝ)^a) (A : Matrix (Fin d) (Fin d) ℚ)
    (U : Matrix.unitaryGroup (Fin d) ℝ) (v : Coordinates d)
    (hv : ∀ j,0<v j) (hA : realMatrix A=rotatedPrecision U v)
    (hlo : ∀ j,((2:ℝ)^L)⁻¹≤Real.sqrt (v j))
    (hhi : ∀ j,Real.sqrt (v j)≤(2:ℝ)^L) :
    ‖realMatrix (certifiedMatrixSqrt a L s A)-
      rotatedPrecision U (fun j=>Real.sqrt (v j))‖≤((2:ℝ)^s)⁻¹ := by
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
  have herr0 := dyadic_newton_error a b m s N (d:ℝ) ((2:ℝ)^b)
    (by positivity) (by positivity) hdim le_rfl
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
  have htail : (d:ℝ)^2*(2:ℝ)^L*(1/2:ℝ)^N≤((2:ℝ)^(s+2))⁻¹ := by
    have he : ((2:ℝ)^a)^2*(2:ℝ)^L*(1/2:ℝ)^N=((2:ℝ)^(s+2))⁻¹ := by
      dsimp [N,matrixSqrtIterations]
      simp only [div_pow,one_pow,pow_add,pow_mul']
      field_simp
      <;> ring
    rw [← he]
    gcongr
  have heps : 2*((2:ℝ)^(s+2))⁻¹≤((2:ℝ)^s)⁻¹ := by
    rw [pow_add]
    norm_num
    nlinarith [inv_nonneg.mpr (show (0:ℝ)≤2^s by positivity)]
  have hfinal := ht.2
  push_cast at hfinal
  change ‖realMatrix (certifiedMatrixSqrt a L s A)-_‖≤_ at hfinal
  rw [hp] at hfinal
  exact hfinal.trans (by linarith)

end Paper254
#print axioms Paper254.certifiedMatrixSqrt_error
