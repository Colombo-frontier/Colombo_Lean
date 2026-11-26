import GaussianFloor254
import Projection254

noncomputable section
open scoped Matrix BigOperators
open Matrix
namespace Paper254

def rotatedFactorMap {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℝ)
    (c : Coordinates d) : Space d →ₗ[ℝ] Space d :=
  Matrix.toEuclideanLin (Matrix.diagonal (fun j => Real.sqrt (c j))*(U : Precision d))

theorem rotatedFactorMap_apply {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℝ)
    (c : Coordinates d) (x : Space d) (j : Fin d) :
    rotatedFactorMap U c x j = Real.sqrt (c j)*((U : Precision d) *ᵥ x) j := by
  simp only [rotatedFactorMap, Matrix.toEuclideanLin_apply, ← Matrix.mulVec_mulVec,
    PiLp.toLp_apply, Matrix.mulVec_diagonal]
  rfl

theorem rotatedFactorMap_norm {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℝ)
    (c : Coordinates d) (hc : ∀ j, 0 ≤ c j) (x : Space d) :
    ‖rotatedFactorMap U c x‖^2 = matrixQuadratic (rotatedPrecision U c) x := by
  rw [EuclideanSpace.norm_sq_eq, rotatedPrecision_quadratic]
  apply Finset.sum_congr rfl
  intro j _
  rw [rotatedFactorMap_apply]
  simp only [Real.norm_eq_abs, sq_abs, mul_pow, Real.sq_sqrt (hc j)]

theorem rotatedFactorMap_injective {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℝ)
    (c : Coordinates d) (hc : ∀ j, 0 < c j) : Function.Injective (rotatedFactorMap U c) := by
  intro x y h
  have hu : (U : Precision d) *ᵥ (x : Coordinates d) = (U : Precision d) *ᵥ (y : Coordinates d) := by
    ext j
    have hj := congrArg (fun z : Space d => z j) h
    simp only [rotatedFactorMap_apply] at hj
    exact mul_left_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr (hc j))) hj
  have hxy := unitary_mulVec_injective U hu
  ext j
  exact congrFun hxy j

def rotatedFactor {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℝ)
    (c : Coordinates d) (hc : ∀ j, 0 < c j) : Space d ≃L[ℝ] Space d :=
  (LinearEquiv.ofBijective (rotatedFactorMap U c)
    ⟨rotatedFactorMap_injective U c hc,
      LinearMap.injective_iff_surjective.mp (rotatedFactorMap_injective U c hc)⟩).toContinuousLinearEquiv

theorem rotatedFactor_norm {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℝ)
    (c : Coordinates d) (hc : ∀ j, 0 < c j) (x : Space d) :
    ‖rotatedFactor U c hc x‖^2 = matrixQuadratic (rotatedPrecision U c) x :=
  rotatedFactorMap_norm U c (fun j => (hc j).le) x

def precisionFactor {d : ℕ} {A : Precision d} (hA : A.PosDef) : Space d ≃L[ℝ] Space d :=
  rotatedFactor (star hA.isHermitian.eigenvectorUnitary) hA.isHermitian.eigenvalues
    hA.eigenvalues_pos

theorem precisionFactor_norm {d : ℕ} {A : Precision d} (hA : A.PosDef) (x : Space d) :
    ‖precisionFactor hA x‖^2 = matrixQuadratic A x := by
  rw [precisionFactor, rotatedFactor_norm, ← precision_spectral_rotated hA]

def PrecisionGaussian.projectMean {d : ℕ} {D : ℝ} (P : PrecisionGaussian d)
    (W : Domain d D) : PrecisionGaussian d :=
  ⟨(metricProject W (precisionFactor P.positive) (WithLp.toLp 2 P.mean)).val,
    P.precision, P.positive⟩

theorem PrecisionGaussian.projectMean_feasible {d : ℕ} {D : ℝ} (P : PrecisionGaussian d)
    (W : Domain d D) : WithLp.toLp 2 (P.projectMean W).mean ∈ W.carrier := by
  exact (metricProject W (precisionFactor P.positive) (WithLp.toLp 2 P.mean)).property

theorem PrecisionGaussian.project_potential_decreases {d : ℕ} {D : ℝ} (P : PrecisionGaussian d)
    (W : Domain d D) (q : ℝ) (u : W.carrier) :
    (P.projectMean W).potential q u.val ≤ P.potential q u.val := by
  have hh := metricProject_potential_decreases W (precisionFactor P.positive)
    (WithLp.toLp 2 P.mean) u (precisionCovariancePart q P.precision/2)
  rw [precisionFactor_norm, precisionFactor_norm] at hh
  change precisionCovariancePart q P.precision/2+
    matrixQuadratic P.precision (fun j => u.val j-
      (metricProject W (precisionFactor P.positive) (WithLp.toLp 2 P.mean)).val j)/2 ≤
    precisionCovariancePart q P.precision/2+
      matrixQuadratic P.precision (fun j => u.val j-P.mean j)/2 at hh
  change (precisionCovariancePart q P.precision+
    matrixQuadratic P.precision (fun j => u.val j-
      (metricProject W (precisionFactor P.positive) (WithLp.toLp 2 P.mean)).val j))/2 ≤
    (precisionCovariancePart q P.precision+matrixQuadratic P.precision (fun j => u.val j-P.mean j))/2
  linarith

end Paper254
#print axioms Paper254.precisionFactor_norm
#print axioms Paper254.PrecisionGaussian.project_potential_decreases
