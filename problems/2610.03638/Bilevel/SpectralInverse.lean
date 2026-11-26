import Bilevel.InversePolynomial
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.LinearAlgebra.Eigenspace.Minpoly

/-!
# Spectral transfer of the Chebyshev inverse approximation

For a real finite-dimensional symmetric operator with quadratic-form bounds
`μ I ≤ H ≤ M I`, this module obtains the orthonormal eigenbasis from Mathlib's
spectral theorem. It constructs and verifies a two-sided inverse and transfers
the scalar polynomial approximation to vector error and operator-norm bounds.
-/

noncomputable section
open Polynomial
open scoped BigOperators

namespace Bilevel.SpectralInverse

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [Fintype ι]

/-- The linear operator defined by diagonal coordinates in an orthonormal basis. -/
def diagonal (b : OrthonormalBasis ι ℝ E) (c : ι → ℝ) : E →ₗ[ℝ] E where
  toFun v := b.repr.symm (fun i => c i * b.repr v i)
  map_add' v w := by
    apply b.repr.injective
    ext i
    simp [mul_add]
  map_smul' a v := by
    apply b.repr.injective
    ext i
    simp [mul_left_comm]

theorem diagonal_repr (b : OrthonormalBasis ι ℝ E) (c : ι → ℝ) (v : E) (i : ι) :
    b.repr (diagonal b c v) i = c i * b.repr v i := by
  simp [diagonal]

theorem norm_sq_coordinates (b : OrthonormalBasis ι ℝ E) (v : E) :
    ‖v‖ ^ 2 = ∑ i, (b.repr v i) ^ 2 := by
  rw [← b.repr.norm_map v, PiLp.norm_sq_eq_of_L2]
  simp [Real.norm_eq_abs, sq_abs]

/-- A coordinatewise scalar bound transfers to the Hilbert-space operator bound. -/
theorem coordinate_bound (b : OrthonormalBasis ι ℝ E) (T : E →ₗ[ℝ] E)
    (c : ι → ℝ) (hT : ∀ v i, b.repr (T v) i = c i * b.repr v i)
    {C : ℝ} (hC : 0 ≤ C) (hc : ∀ i, |c i| ≤ C) (v : E) : ‖T v‖ ≤ C * ‖v‖ := by
  have hs : ‖T v‖ ^ 2 ≤ C ^ 2 * ‖v‖ ^ 2 := by
    rw [norm_sq_coordinates b (T v), norm_sq_coordinates b v, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [hT, mul_pow]
    have hci : (c i) ^ 2 ≤ C ^ 2 := by
      have := hc i
      nlinarith [sq_abs (c i), abs_nonneg (c i)]
    exact mul_le_mul_of_nonneg_right hci (sq_nonneg _)
  apply (sq_le_sq₀ (norm_nonneg (T v)) (mul_nonneg hC (norm_nonneg v))).mp
  simpa only [mul_pow] using hs

theorem eigenvalues_in_interval [FiniteDimensional ℝ E]
    (H : E →ₗ[ℝ] E) (hH : H.IsSymmetric) {μ M : ℝ}
    (lower : ∀ v, μ * ‖v‖ ^ 2 ≤ inner (𝕜 := ℝ) (H v) v)
    (upper : ∀ v, inner (𝕜 := ℝ) (H v) v ≤ M * ‖v‖ ^ 2)
    (i : Fin (Module.finrank ℝ E)) : hH.eigenvalues rfl i ∈ Set.Icc μ M := by
  have hl := lower (hH.eigenvectorBasis rfl i)
  have hu := upper (hH.eigenvectorBasis rfl i)
  rw [hH.apply_eigenvectorBasis] at hl hu
  have hn : ‖hH.eigenvectorBasis rfl i‖ = 1 := (hH.eigenvectorBasis rfl).orthonormal.norm_eq_one i
  simp only [real_inner_smul_left, real_inner_self_eq_norm_sq, hn, one_pow, mul_one] at hl hu
  exact ⟨hl, hu⟩

theorem polynomial_eigen_coordinates [FiniteDimensional ℝ E]
    (H : E →ₗ[ℝ] E) (hH : H.IsSymmetric) (p : ℝ[X]) (v : E)
    (i : Fin (Module.finrank ℝ E)) :
    (hH.eigenvectorBasis rfl).repr ((aeval H p) v) i =
      p.eval (hH.eigenvalues rfl i) * (hH.eigenvectorBasis rfl).repr v i := by
  let b := hH.eigenvectorBasis rfl
  have heq : (aeval H p : E →ₗ[ℝ] E) = diagonal b (fun i => p.eval (hH.eigenvalues rfl i)) := by
    apply b.toBasis.ext
    intro j
    change (aeval H p) (hH.eigenvectorBasis rfl j) = _
    rw [Module.End.aeval_apply_of_hasEigenvector (hH.hasEigenvector_eigenvectorBasis rfl j)]
    apply b.repr.injective
    ext k
    by_cases hjk : j = k <;> simp [diagonal_repr, b, hjk, eq_comm]
  rw [heq, diagonal_repr]

section Inverse
variable [FiniteDimensional ℝ E]

/-- The genuine inverse, constructed in the orthonormal eigenbasis. Two-sided
inverse identities below certify its meaning independently of approximation. -/
def spectralInverse (H : E →ₗ[ℝ] E) (hH : H.IsSymmetric) : E →ₗ[ℝ] E :=
  diagonal (hH.eigenvectorBasis rfl) (fun i => (hH.eigenvalues rfl i)⁻¹)

theorem apply_inverse (H : E →ₗ[ℝ] E) (hH : H.IsSymmetric) {μ M : ℝ} (hμ : 0 < μ)
    (lower : ∀ v, μ * ‖v‖ ^ 2 ≤ inner (𝕜 := ℝ) (H v) v)
    (upper : ∀ v, inner (𝕜 := ℝ) (H v) v ≤ M * ‖v‖ ^ 2) (v : E) :
    H (spectralInverse H hH v) = v := by
  apply (hH.eigenvectorBasis rfl).repr.injective
  ext i
  rw [hH.eigenvectorBasis_apply_self_apply]
  have hi := eigenvalues_in_interval H hH lower upper i
  have hz : hH.eigenvalues rfl i ≠ 0 := (lt_of_lt_of_le hμ hi.1).ne'
  simp [spectralInverse, diagonal_repr, ← mul_assoc, hz]

theorem inverse_apply (H : E →ₗ[ℝ] E) (hH : H.IsSymmetric) {μ M : ℝ} (hμ : 0 < μ)
    (lower : ∀ v, μ * ‖v‖ ^ 2 ≤ inner (𝕜 := ℝ) (H v) v)
    (upper : ∀ v, inner (𝕜 := ℝ) (H v) v ≤ M * ‖v‖ ^ 2) (v : E) :
    spectralInverse H hH (H v) = v := by
  apply (hH.eigenvectorBasis rfl).repr.injective
  ext i
  rw [spectralInverse, diagonal_repr, hH.eigenvectorBasis_apply_self_apply]
  have hi := eigenvalues_in_interval H hH lower upper i
  have hz : hH.eigenvalues rfl i ≠ 0 := (lt_of_lt_of_le hμ hi.1).ne'
  simp [← mul_assoc, hz]

theorem approximation_error (H : E →ₗ[ℝ] E) (hH : H.IsSymmetric) {μ M : ℝ}
    (hμ : 0 < μ) (hM : μ < M)
    (lower : ∀ v, μ * ‖v‖ ^ 2 ≤ inner (𝕜 := ℝ) (H v) v)
    (upper : ∀ v, inner (𝕜 := ℝ) (H v) v ≤ M * ‖v‖ ^ 2)
    (m : ℕ) (v : E) :
    ‖(aeval H (InversePolynomial.inverseApprox μ M m)) v - spectralInverse H hH v‖ ≤
      ((2 / μ) * (InversePolynomial.rate μ M) ^ m) * ‖v‖ := by
  let b := hH.eigenvectorBasis rfl
  let p := InversePolynomial.inverseApprox μ M m
  have hcoord : ∀ w i, b.repr (((aeval H p : E →ₗ[ℝ] E) - spectralInverse H hH) w) i =
      (p.eval (hH.eigenvalues rfl i) - (hH.eigenvalues rfl i)⁻¹) * b.repr w i := by
    intro w i
    simp only [LinearMap.sub_apply, map_sub, PiLp.sub_apply]
    rw [polynomial_eigen_coordinates, spectralInverse, diagonal_repr]
    ring
  apply coordinate_bound b ((aeval H p : E →ₗ[ℝ] E) - spectralInverse H hH)
    (fun i => p.eval (hH.eigenvalues rfl i) - (hH.eigenvalues rfl i)⁻¹) hcoord
  · have := (InversePolynomial.rate_range hμ hM).1
    positivity
  · intro i
    have hi := eigenvalues_in_interval H hH lower upper i
    simpa only [one_div] using InversePolynomial.inverseApprox_error hμ hM hi.1 hi.2 m

theorem approximation_norm (H : E →ₗ[ℝ] E) (hH : H.IsSymmetric) {μ M : ℝ}
    (hμ : 0 < μ) (hM : μ < M)
    (lower : ∀ v, μ * ‖v‖ ^ 2 ≤ inner (𝕜 := ℝ) (H v) v)
    (upper : ∀ v, inner (𝕜 := ℝ) (H v) v ≤ M * ‖v‖ ^ 2)
    (m : ℕ) (v : E) :
    ‖(aeval H (InversePolynomial.inverseApprox μ M m)) v‖ ≤ (3 / μ) * ‖v‖ := by
  apply coordinate_bound (hH.eigenvectorBasis rfl)
    (aeval H (InversePolynomial.inverseApprox μ M m))
    (fun i => (InversePolynomial.inverseApprox μ M m).eval (hH.eigenvalues rfl i))
    (polynomial_eigen_coordinates H hH _) (by positivity)
  intro i
  have hi := eigenvalues_in_interval H hH lower upper i
  exact InversePolynomial.inverseApprox_bound hμ hM hi.1 hi.2 m

theorem approximation_opNorm (H : E →ₗ[ℝ] E) (hH : H.IsSymmetric) {μ M : ℝ}
    (hμ : 0 < μ) (hM : μ < M)
    (lower : ∀ v, μ * ‖v‖ ^ 2 ≤ inner (𝕜 := ℝ) (H v) v)
    (upper : ∀ v, inner (𝕜 := ℝ) (H v) v ≤ M * ‖v‖ ^ 2) (m : ℕ) :
    ‖(aeval H (InversePolynomial.inverseApprox μ M m)).toContinuousLinearMap‖ ≤ 3 / μ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  exact approximation_norm H hH hμ hM lower upper m

theorem approximation_error_opNorm (H : E →ₗ[ℝ] E) (hH : H.IsSymmetric) {μ M : ℝ}
    (hμ : 0 < μ) (hM : μ < M)
    (lower : ∀ v, μ * ‖v‖ ^ 2 ≤ inner (𝕜 := ℝ) (H v) v)
    (upper : ∀ v, inner (𝕜 := ℝ) (H v) v ≤ M * ‖v‖ ^ 2) (m : ℕ) :
    ‖((aeval H (InversePolynomial.inverseApprox μ M m) : E →ₗ[ℝ] E) -
      spectralInverse H hH).toContinuousLinearMap‖ ≤
        (2 / μ) * (InversePolynomial.rate μ M) ^ m := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by
    have := (InversePolynomial.rate_range hμ hM).1
    positivity)
  exact approximation_error H hH hμ hM lower upper m

theorem operator_opNorm (H : E →ₗ[ℝ] E) (hH : H.IsSymmetric) {μ M : ℝ}
    (hμ : 0 < μ) (hM : μ < M)
    (lower : ∀ v, μ * ‖v‖ ^ 2 ≤ inner (𝕜 := ℝ) (H v) v)
    (upper : ∀ v, inner (𝕜 := ℝ) (H v) v ≤ M * ‖v‖ ^ 2) :
    ‖H.toContinuousLinearMap‖ ≤ M := by
  apply ContinuousLinearMap.opNorm_le_bound _ (lt_trans hμ hM).le
  intro v
  apply coordinate_bound (hH.eigenvectorBasis rfl) H (hH.eigenvalues rfl)
    (hH.eigenvectorBasis_apply_self_apply rfl) (lt_trans hμ hM).le
  intro i
  have hi := eigenvalues_in_interval H hH lower upper i
  rw [abs_of_nonneg (lt_of_lt_of_le hμ hi.1).le]
  exact hi.2

/-- The scaled operator used by the inexact Horner evaluator is contractive. -/
theorem scaled_operator_contractive (H : E →ₗ[ℝ] E) (hH : H.IsSymmetric) {μ M : ℝ}
    (hμ : 0 < μ) (hM : μ < M)
    (lower : ∀ v, μ * ‖v‖ ^ 2 ≤ inner (𝕜 := ℝ) (H v) v)
    (upper : ∀ v, inner (𝕜 := ℝ) (H v) v ≤ M * ‖v‖ ^ 2) :
    ‖(1 / M) • H.toContinuousLinearMap‖ ≤ 1 := by
  have hpos : 0 < M := lt_trans hμ hM
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hpos)]
  calc
    _ ≤ (1 / M) * M := mul_le_mul_of_nonneg_left
      (operator_opNorm H hH hμ hM lower upper) (one_div_nonneg.mpr hpos.le)
    _ = 1 := by field_simp

end Inverse

end Bilevel.SpectralInverse
