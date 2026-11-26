import RationalSpectralClip254

noncomputable section
open scoped BigOperators Matrix.Norms.Operator
open Matrix
namespace Paper254

def spectralCoordinateVector {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℝ) (j : Fin d) : Space d :=
  WithLp.toLp 2 ((U:Precision d)ᴴ *ᵥ Pi.single j 1)

theorem spectralCoordinateVector_norm {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℝ) (j : Fin d) :
    ‖spectralCoordinateVector U j‖^2=1 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Real.norm_eq_abs,sq_abs]
  change (∑ k,((U:Precision d)ᴴ *ᵥ Pi.single j 1) k^2)=1
  have hh := unitary_sum_squares (star U) (Pi.single j 1)
  simpa only [unitary.coe_star,star_eq_conjTranspose,Pi.single_apply,
    ite_pow,one_pow,zero_pow (by norm_num : (2:ℕ)≠0),Finset.sum_ite_eq',Finset.mem_univ,if_true] using hh

theorem spectralCoordinateVector_quadratic {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℝ)
    (c : Coordinates d) (j : Fin d) :
    matrixQuadratic (rotatedPrecision U c) (spectralCoordinateVector U j)=c j := by
  rw [rotatedPrecision_quadratic]
  have hu : (U:Precision d)*ᵥ (spectralCoordinateVector U j:Coordinates d)=Pi.single j 1 := by
    change (U:Precision d)*ᵥ ((U:Precision d)ᴴ *ᵥ Pi.single j 1)=_
    rw [Matrix.mulVec_mulVec]
    have hid : (U:Precision d)*(U:Precision d)ᴴ=1 := unitary.coe_mul_star_self U
    rw [hid,Matrix.one_mulVec]
  rw [hu]
  simp [Pi.single_apply]

theorem eigenvalues_from_quadratic_bounds {d : ℕ} (A : Precision d) (hA : A.PosDef)
    (lo hi : ℝ)
    (hlo : ∀ x : Space d,lo*‖x‖^2≤matrixQuadratic A x)
    (hhi : ∀ x : Space d,matrixQuadratic A x≤hi*‖x‖^2) :
    ∀ j,lo≤hA.isHermitian.eigenvalues j ∧ hA.isHermitian.eigenvalues j≤hi := by
  intro j
  let U := star hA.isHermitian.eigenvectorUnitary
  have hl := hlo (spectralCoordinateVector U j)
  have hh := hhi (spectralCoordinateVector U j)
  rw [spectralCoordinateVector_norm,mul_one,precision_spectral_rotated hA,
    spectralCoordinateVector_quadratic] at hl hh
  exact ⟨hl,hh⟩

theorem determinant_lower_from_quadratic {d : ℕ} (A : Precision d) (hA : A.PosDef)
    (lo hi : ℝ) (hl : 0≤lo)
    (hlo : ∀ x : Space d,lo*‖x‖^2≤matrixQuadratic A x)
    (hhi : ∀ x : Space d,matrixQuadratic A x≤hi*‖x‖^2) : lo^d≤A.det := by
  rw [hA.isHermitian.det_eq_prod_eigenvalues]
  have he := eigenvalues_from_quadratic_bounds A hA lo hi hlo hhi
  calc
    _ = ∏ _j : Fin d,lo := by simp
    _ ≤ _ := Finset.prod_le_prod (fun _ _=>hl) (fun j _=>(he j).1)

theorem precision_bounds_from_covariance {d : ℕ} (C : Precision d) (hC : C.PosDef)
    (lo hi : ℝ) (hl : 0<lo) (hh : 0<hi)
    (hlo : ∀ x : Space d,lo*‖x‖^2≤matrixQuadratic C x)
    (hhi : ∀ x : Space d,matrixQuadratic C x≤hi*‖x‖^2) :
    (∀ x : Space d,(1/hi)*‖x‖^2≤matrixQuadratic C⁻¹ x ∧
      matrixQuadratic C⁻¹ x≤(1/lo)*‖x‖^2) ∧
    (1/hi)^d≤C⁻¹.det ∧ (∀ i j,|C⁻¹ i j|≤(d:ℝ)^2/lo) := by
  let U := star hC.isHermitian.eigenvectorUnitary
  let c := hC.isHermitian.eigenvalues
  have he := eigenvalues_from_quadratic_bounds C hC lo hi hlo hhi
  have hiEq : C⁻¹=rotatedPrecision U (c⁻¹) := by
    rw [Matrix.nonsing_inv_eq_ringInverse,precision_spectral_rotated hC,
      rotatedPrecision_inverse _ _ (fun j=>(hC.eigenvalues_pos j).ne')]
  have hcl : ∀ j,1/hi≤(c j)⁻¹ := by
    intro j
    rw [one_div]
    exact (inv_le_inv₀ hh (hC.eigenvalues_pos j)).mpr (he j).2
  have hch : ∀ j,(c j)⁻¹≤1/lo := by
    intro j
    rw [one_div]
    exact (inv_le_inv₀ (hC.eigenvalues_pos j) hl).mpr (he j).1
  have hbounds : ∀ x : Space d,(1/hi)*‖x‖^2≤matrixQuadratic C⁻¹ x ∧
      matrixQuadratic C⁻¹ x≤(1/lo)*‖x‖^2 := by
    intro x
    rw [hiEq]
    exact ⟨rotatedPrecision_lower_bound U _ _ hcl x,rotatedPrecision_quadratic_bound U _ _ hch x⟩
  refine ⟨hbounds,determinant_lower_from_quadratic C⁻¹ hC.inv (1/hi) (1/lo)
    (by positivity) (fun x=>(hbounds x).1) (fun x=>(hbounds x).2),?_⟩
  have hn : ‖C⁻¹‖≤(d:ℝ)^2/lo := by
    rw [hiEq]
    have hr := rotatedPrecision_norm_bound U (c⁻¹) (1/lo) (by positivity)
      (fun j=>by change |(c j)⁻¹|≤_; rw [abs_of_pos (inv_pos.mpr (hC.eigenvalues_pos j))]; exact hch j)
    simpa only [div_eq_mul_inv,one_mul] using hr
  intro i j
  exact (matrix_entry_le_operator_norm C⁻¹ i j).trans hn

end Paper254
#print axioms Paper254.precision_bounds_from_covariance
