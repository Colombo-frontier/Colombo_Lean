import RationalStepFeasible254

noncomputable section
namespace Paper254

theorem inverse_quadratic_upper_of_lower {d : ℕ} (A : Precision d) (hA : A.PosDef)
    (l : ℝ) (hl : 0<l)
    (hbound : ∀ x : Space d,l*‖x‖^2≤matrixQuadratic A x) :
    ∀ x : Space d,matrixQuadratic A⁻¹ x≤(1/l)*‖x‖^2 := by
  let U := star hA.isHermitian.eigenvectorUnitary
  let c := hA.isHermitian.eigenvalues
  have hc : ∀ j,l≤c j := by
    intro j
    have hh := hbound (spectralCoordinateVector U j)
    rw [spectralCoordinateVector_norm,mul_one,precision_spectral_rotated hA,
      spectralCoordinateVector_quadratic] at hh
    exact hh
  have he : A⁻¹=rotatedPrecision U (c⁻¹) := by
    rw [Matrix.nonsing_inv_eq_ringInverse,precision_spectral_rotated hA,
      rotatedPrecision_inverse _ _ (fun j=>(hA.eigenvalues_pos j).ne')]
  intro x
  rw [he]
  apply rotatedPrecision_quadratic_bound
  intro j
  change (c j)⁻¹≤1/l
  rw [one_div]
  exact (inv_le_inv₀ (hA.eigenvalues_pos j) hl).mpr (hc j)

/-- A rank-one tilt cannot enlarge the covariance upper bound. -/
theorem rationalTiltCovariance_upper {d : ℕ} (S : RationalHistoryData d)
    (hS : (realMatrix S.covariance).PosDef) (lo hi : ℝ) (hlo : 0<lo) (hhi : 0<hi)
    (hloS : ∀ x : Space d,lo*‖x‖^2≤matrixQuadratic (realMatrix S.covariance) x)
    (hhiS : ∀ x : Space d,matrixQuadratic (realMatrix S.covariance) x≤hi*‖x‖^2)
    (lam : ℚ) (g : Fin d→ℚ) :
    ∀ x : Space d,matrixQuadratic
      (realMatrix (rationalMatrixInverse (rationalTiltPrecision S lam g))) x≤hi*‖x‖^2 := by
  have hb := (precision_bounds_from_covariance _ hS lo hi hlo hhi hloS hhiS).1
  have ht := rationalTiltPrecision_posDef S hS lam g
  have hl : ∀ x : Space d,(1/hi)*‖x‖^2≤
      matrixQuadratic (realMatrix (rationalTiltPrecision S lam g)) x := by
    intro x
    rw [rationalTiltPrecision_cast,← Matrix.nonsing_inv_eq_ringInverse,
      rankOnePrecision_quadratic]
    have hn : 0≤((lam:ℝ)*(2*(lam:ℝ)))*
      ((fun j=>(g j:ℝ)) ⬝ᵥ (x:Coordinates d))^2 :=
      mul_nonneg (by nlinarith [sq_nonneg (lam:ℝ)]) (sq_nonneg _)
    linarith [(hb x).1]
  have hh := inverse_quadratic_upper_of_lower _ ht (1/hi) (by positivity) hl
  rw [realMatrix_inverse,← Matrix.nonsing_inv_eq_ringInverse]
  simpa only [one_div,inv_inv] using hh

theorem rationalTiltCovariance_spectrum {d : ℕ} (S : RationalHistoryData d)
    (hS : (realMatrix S.covariance).PosDef) (lo hi : ℝ) (hlo : 0<lo) (hhi : 0<hi)
    (hloS : ∀ x : Space d,lo*‖x‖^2≤matrixQuadratic (realMatrix S.covariance) x)
    (hhiS : ∀ x : Space d,matrixQuadratic (realMatrix S.covariance) x≤hi*‖x‖^2)
    (lam : ℚ) (g : Fin d→ℚ) :
    ∃ U : Matrix.unitaryGroup (Fin d) ℝ,∃ c : Coordinates d,
      realMatrix (rationalMatrixInverse (rationalTiltPrecision S lam g))=rotatedPrecision U c ∧
      ∀ j,0<c j ∧ c j≤hi := by
  let C := realMatrix (rationalMatrixInverse (rationalTiltPrecision S lam g))
  have hC : C.PosDef := by
    dsimp [C]
    rw [realMatrix_inverse,← Matrix.nonsing_inv_eq_ringInverse]
    exact (rationalTiltPrecision_posDef S hS lam g).inv
  let U := star hC.isHermitian.eigenvectorUnitary
  refine ⟨U,hC.isHermitian.eigenvalues,precision_spectral_rotated hC,?_⟩
  intro j
  refine ⟨hC.eigenvalues_pos j,?_⟩
  have hh := rationalTiltCovariance_upper S hS lo hi hlo hhi hloS hhiS lam g
    (spectralCoordinateVector U j)
  change matrixQuadratic C (spectralCoordinateVector U j)≤_ at hh
  rw [spectralCoordinateVector_norm,mul_one,precision_spectral_rotated hC,
    spectralCoordinateVector_quadratic] at hh
  exact hh

end Paper254
#print axioms Paper254.rationalTiltCovariance_spectrum
