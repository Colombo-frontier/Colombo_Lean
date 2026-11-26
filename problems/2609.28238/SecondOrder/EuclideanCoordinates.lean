import SecondOrder.Model
import Mathlib.Analysis.Calculus.ContDiff.Operations

open scoped BigOperators InnerProductSpace

namespace SecondOrder
noncomputable section

def euclideanVector {d : ℕ} (v : Fin d → ℝ) : Point d :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm v

@[simp] theorem euclideanVector_apply {d : ℕ} (v : Fin d → ℝ) (i : Fin d) :
    euclideanVector v i = v i := rfl

def coordinateMap {d n : ℕ} (L : Fin n → Point d →L[ℝ] ℝ) : Point d →L[ℝ] Point n :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi L)

@[simp] theorem coordinateMap_apply {d n : ℕ} (L : Fin n → Point d →L[ℝ] ℝ)
    (v : Point d) (i : Fin n) : coordinateMap L v i = L i v := rfl

theorem hasFDerivAt_coordinates {d n : ℕ} {f : Point d → Point n}
    {L : Point d →L[ℝ] Point n} {x : Point d}
    (h : ∀ i, HasFDerivAt (fun y => f y i) ((EuclideanSpace.proj i).comp L) x) :
    HasFDerivAt f L x := by
  have hh := ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm.hasFDerivAt).comp x
    (hasFDerivAt_pi.mpr h)
  convert hh using 1

theorem contDiff_coordinates {d n : ℕ} {k : WithTop ℕ∞} {f : Point d → Point n}
    (h : ∀ i, ContDiff ℝ k (fun y => f y i)) : ContDiff ℝ k f :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm.contDiff.comp (contDiff_pi.mpr h)

theorem euclidean_inner {d : ℕ} (v w : Point d) : ⟪v,w⟫_ℝ = ∑ i, v i*w i := by
  simp only [PiLp.inner_apply, real_inner_comm, RCLike.inner_apply, conj_trivial, mul_comm]

theorem euclidean_norm_sq {d : ℕ} (v : Point d) : ‖v‖^2 = ∑ i, (v i)^2 := by
  simp [PiLp.norm_sq_eq_of_L2, Real.norm_eq_abs, sq_abs]

theorem dual_euclideanVector {d : ℕ} (c : Fin d → ℝ) :
    InnerProductSpace.toDual ℝ (Point d) (euclideanVector c) =
      ∑ i, c i • EuclideanSpace.proj i := by
  ext v
  simp only [InnerProductSpace.toDual_apply, euclidean_inner, euclideanVector_apply,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, PiLp.proj_apply, smul_eq_mul]

/-- Diagonal multiplication in the Euclidean norm. -/
def diagonalMap {d : ℕ} (c : Point d) : Point d →L[ℝ] Point d :=
  coordinateMap (fun i => c i • EuclideanSpace.proj i)

@[simp] theorem diagonalMap_apply {d : ℕ} (c v : Point d) (i : Fin d) :
    diagonalMap c v i = c i*v i := rfl

theorem diagonalMap_norm_le {d : ℕ} (c : Point d) {M : ℝ} (hM : 0 ≤ M)
    (hc : ∀ i, |c i| ≤ M) : ‖diagonalMap c‖ ≤ M := by
  apply (diagonalMap c).opNorm_le_bound hM
  intro v
  have hsq : ‖diagonalMap c v‖^2 ≤ M^2*‖v‖^2 := by
    simp only [euclidean_norm_sq, diagonalMap_apply, mul_pow, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    nlinarith [sq_abs (c i), sq_nonneg (M-|c i|), hc i, abs_nonneg (c i)]
  nlinarith [norm_nonneg (diagonalMap c v), mul_nonneg hM (norm_nonneg v)]

theorem diagonalMap_inner {d : ℕ} (c v : Point d) :
    ⟪diagonalMap c v,v⟫_ℝ = ∑ i, c i*(v i)^2 := by
  simp only [euclidean_inner, diagonalMap_apply]
  apply Finset.sum_congr rfl
  intro i _
  ring

end
end SecondOrder
