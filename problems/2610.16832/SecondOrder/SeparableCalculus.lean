import SecondOrder.HyperbolicScalar
import SecondOrder.EuclideanCoordinates
import SecondOrder.PeriodicThird

open scoped BigOperators Classical InnerProductSpace

namespace SecondOrder
noncomputable section
variable {d : ℕ}

def separablePotential (φ : ℝ → ℝ) (a : Fin d → ℝ) (s : ℝ) (x : Point d) : ℝ :=
  ∑ i, a i*φ (s*x i)

def separableGradient (φ' : ℝ → ℝ) (a : Fin d → ℝ) (s : ℝ) (x : Point d) : Point d :=
  euclideanVector (fun i => a i*s*φ' (s*x i))

def separableHessian (φ'' : ℝ → ℝ) (a : Fin d → ℝ) (s : ℝ) (x : Point d) : Point d →L[ℝ] Point d :=
  diagonalMap (euclideanVector (fun i => a i*s^2*φ'' (s*x i)))

theorem separablePotential_contDiff {φ : ℝ → ℝ} {n : WithTop ℕ∞} (hφ : ContDiff ℝ n φ)
    (a : Fin d → ℝ) (s : ℝ) : ContDiff ℝ n (separablePotential φ a s) := by
  apply ContDiff.sum
  intro i _
  exact contDiff_const.mul (hφ.comp (contDiff_const.mul (EuclideanSpace.proj i : Point d →L[ℝ] ℝ).contDiff))

theorem separablePotential_hasGradientAt {φ φ' : ℝ → ℝ}
    (hφ : ∀ t, HasDerivAt φ (φ' t) t) (a : Fin d → ℝ) (s : ℝ) (x : Point d) :
    HasGradientAt (separablePotential φ a s) (separableGradient φ' a s x) x := by
  apply hasGradientAt_iff_hasFDerivAt.mpr
  rw [separableGradient,dual_euclideanVector]
  apply HasFDerivAt.sum
  intro i _
  convert ((hφ (s*x i)).comp_hasFDerivAt x ((EuclideanSpace.proj i : Point d →L[ℝ] ℝ).hasFDerivAt.const_mul s)).const_mul (a i) using 1
  ext v
  simp only [ContinuousLinearMap.smul_apply,smul_eq_mul]
  ring

theorem gradient_separablePotential {φ φ' : ℝ → ℝ}
    (hφ : ∀ t, HasDerivAt φ (φ' t) t) (a : Fin d → ℝ) (s : ℝ) :
    gradient (separablePotential φ a s)=separableGradient φ' a s :=
  funext (fun x => (separablePotential_hasGradientAt hφ a s x).gradient)

theorem separableGradient_hasFDerivAt {φ' φ'' : ℝ → ℝ}
    (hφ : ∀ t, HasDerivAt φ' (φ'' t) t) (a : Fin d → ℝ) (s : ℝ) (x : Point d) :
    HasFDerivAt (separableGradient φ' a s) (separableHessian φ'' a s x) x := by
  apply hasFDerivAt_coordinates
  intro i
  convert ((hφ (s*x i)).comp_hasFDerivAt x ((EuclideanSpace.proj i : Point d →L[ℝ] ℝ).hasFDerivAt.const_mul s)).const_mul (a i*s) using 1
  ext v
  simp only [separableHessian,ContinuousLinearMap.comp_apply,PiLp.proj_apply,diagonalMap_apply,
    euclideanVector_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
  ring

theorem hessian_separablePotential {φ φ' φ'' : ℝ → ℝ}
    (hφ : ∀ t, HasDerivAt φ (φ' t) t) (hφ' : ∀ t, HasDerivAt φ' (φ'' t) t)
    (a : Fin d → ℝ) (s : ℝ) (x : Point d) :
    hessian (separablePotential φ a s) x=separableHessian φ'' a s x := by
  rw [hessian,gradient_separablePotential hφ]
  exact (separableGradient_hasFDerivAt hφ' a s x).fderiv

theorem euclideanVector_norm_bound (c : Fin d → ℝ) {M : ℝ} (hM : 0≤M) (hc : ∀ i, |c i|≤M) :
    ‖euclideanVector c‖≤M*Real.sqrt d := by
  have hs : ‖euclideanVector c‖^2≤M^2*(d:ℝ) := by
    rw [euclidean_norm_sq]
    calc
      _ ≤ ∑ _i : Fin d, M^2 := Finset.sum_le_sum (fun i _ => by
        simpa only [euclideanVector_apply,sq_abs] using pow_le_pow_left₀ (abs_nonneg (c i)) (hc i) 2)
      _ = _ := by simp; ring
  have hr := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) d)
  have he : (M*Real.sqrt d)^2=M^2*(d:ℝ) := by rw [mul_pow,hr]
  nlinarith [norm_nonneg (euclideanVector c),mul_nonneg hM (Real.sqrt_nonneg (d:ℝ))]

theorem diagonalMap_sub_norm_bound (c b : Point d) {M : ℝ} (hM : 0≤M)
    (hc : ∀ i, |c i-b i|≤M) : ‖diagonalMap c-diagonalMap b‖≤M := by
  have he : diagonalMap c-diagonalMap b=diagonalMap (euclideanVector (fun i => c i-b i)) := by
    ext v i
    simp only [ContinuousLinearMap.sub_apply,PiLp.sub_apply,diagonalMap_apply,euclideanVector_apply]
    ring
  rw [he]
  exact diagonalMap_norm_le _ hM hc

theorem separableGradient_norm_bound (φ' : ℝ → ℝ) (a : Fin d → ℝ)
    {s A M : ℝ} (hs : 0≤s) (hA : 0≤A) (hM : 0≤M)
    (ha : ∀ i, |a i|≤A) (hφ : ∀ t, |φ' t|≤M) (x : Point d) :
    ‖separableGradient φ' a s x‖≤A*s*M*Real.sqrt d := by
  apply euclideanVector_norm_bound _ (by positivity)
  intro i
  rw [abs_mul,abs_mul,abs_of_nonneg hs]
  exact mul_le_mul (mul_le_mul_of_nonneg_right (ha i) hs) (hφ _) (abs_nonneg _) (by positivity)

theorem separableHessian_norm_bound (φ'' : ℝ → ℝ) (a : Fin d → ℝ)
    {s A M : ℝ} (hA : 0≤A) (hM : 0≤M)
    (ha : ∀ i, |a i|≤A) (hφ : ∀ t, |φ'' t|≤M) (x : Point d) :
    ‖separableHessian φ'' a s x‖≤A*s^2*M := by
  apply diagonalMap_norm_le _ (by positivity)
  intro i
  simp only [euclideanVector_apply,abs_mul,abs_of_nonneg (sq_nonneg s)]
  exact mul_le_mul (mul_le_mul_of_nonneg_right (ha i) (sq_nonneg s)) (hφ _) (abs_nonneg _) (by positivity)

theorem separableHessian_lipschitz (φ'' : ℝ → ℝ) (a : Fin d → ℝ)
    {s A K : ℝ} (hs : 0≤s) (hA : 0≤A) (hK : 0≤K)
    (ha : ∀ i, |a i|≤A) (hφ : ∀ u v, |φ'' v-φ'' u|≤K*|v-u|) (x y : Point d) :
    ‖separableHessian φ'' a s y-separableHessian φ'' a s x‖≤A*s^3*K*‖y-x‖ := by
  apply diagonalMap_sub_norm_bound _ _ (by positivity)
  intro i
  simp only [euclideanVector_apply,←mul_sub,abs_mul,abs_of_nonneg (sq_nonneg s)]
  have hi : |y i-x i|≤‖y-x‖ := PiLp.norm_apply_le (p := (2:ENNReal)) (y-x) i
  have hh := hφ (s*x i) (s*y i)
  rw [←mul_sub,abs_mul,abs_of_nonneg hs] at hh
  have hh' := hh.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hi hs) hK)
  have hm := mul_le_mul (mul_le_mul_of_nonneg_right (ha i) (sq_nonneg s)) hh' (abs_nonneg _) (by positivity : 0≤A*s^2)
  convert hm using 1 <;> ring

end
end SecondOrder
