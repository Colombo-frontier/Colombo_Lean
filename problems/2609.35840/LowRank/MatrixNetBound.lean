import LowRank.HalfSphereNet
import LowRank.GaussianModel
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Deterministic control of the Euclidean matrix operator norm from two
half-radius sphere nets, and its implication for the Wishart Loewner bound. -/

namespace LowRank
open Matrix
open scoped Matrix InnerProductSpace
noncomputable section

theorem opNorm_le_four_of_bilinear_net {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (f : E →L[ℝ] F) (s : Finset F) (t : Finset E)
    (hs : ∀ x : F, ‖x‖ = 1 → ∃ y ∈ s, ‖x - y‖ < (1 : ℝ) / 2)
    (ht : ∀ x : E, ‖x‖ = 1 → ∃ y ∈ t, ‖x - y‖ < (1 : ℝ) / 2)
    {B : ℝ} (hB : 0 ≤ B) (hval : ∀ u ∈ s, ∀ v ∈ t, |⟪u, f v⟫_ℝ| ≤ B) :
    ‖f‖ ≤ 4 * B := by
  have hv : ∀ v ∈ t, ‖f v‖ ≤ 2 * B := by
    intro v hv
    have h := opNorm_le_twice_of_half_net (innerSL ℝ (f v)) s hs hB (fun u hu => ?_)
    · simpa only [innerSL_apply_norm] using h
    · change |⟪f v, u⟫_ℝ| ≤ B
      rw [real_inner_comm]
      exact hval u hu v hv
  have h := opNorm_le_twice_of_half_net f t ht (by positivity : 0 ≤ 2 * B) hv
  linarith

def matrixEuclideanMap {r s : ℕ} (X : Matrix (Fin r) (Fin s) ℝ) :
    EuclideanSpace ℝ (Fin s) →L[ℝ] EuclideanSpace ℝ (Fin r) :=
  LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin X)

theorem continuous_matrixEuclideanMap (r s : ℕ) :
    Continuous (matrixEuclideanMap : Matrix (Fin r) (Fin s) ℝ → _) := by
  let f : Matrix (Fin r) (Fin s) ℝ →ₗ[ℝ]
      (EuclideanSpace ℝ (Fin s) →L[ℝ] EuclideanSpace ℝ (Fin r)) :=
    LinearMap.toContinuousLinearMap.toLinearMap.comp Matrix.toEuclideanLin.toLinearMap
  exact f.continuous_of_finiteDimensional

theorem matrixEuclideanMap_apply {r s : ℕ} (X : Matrix (Fin r) (Fin s) ℝ)
    (v : EuclideanSpace ℝ (Fin s)) :
    ⇑(matrixEuclideanMap X v) = X *ᵥ ⇑v := rfl

theorem matrixEuclideanMap_inner {r s : ℕ} (X : Matrix (Fin r) (Fin s) ℝ)
    (u : EuclideanSpace ℝ (Fin r)) (v : EuclideanSpace ℝ (Fin s)) :
    ⟪u, matrixEuclideanMap X v⟫_ℝ = ⇑u ⬝ᵥ (X *ᵥ ⇑v) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct_comm]
  rfl

theorem euclidean_dot_self {r : ℕ} (u : EuclideanSpace ℝ (Fin r)) :
    ⇑u ⬝ᵥ ⇑u = ‖u‖ ^ 2 := by
  simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] using real_inner_self_eq_norm_sq u

theorem wishart_le_of_transpose_opNorm {r s : ℕ} (X : Matrix (Fin r) (Fin s) ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hX : ‖matrixEuclideanMap Xᵀ‖ ≤ B) :
    LoewnerLE (wishart X) ((B ^ 2) • 1) := by
  refine ⟨?_, ?_⟩
  · apply Matrix.IsHermitian.sub _ (wishart_posSemidef X).isHermitian
    change ((B ^ 2) • (1 : Matrix (Fin r) (Fin r) ℝ))ᴴ = _
    simp
  · intro z
    let u : EuclideanSpace ℝ (Fin r) := (WithLp.equiv 2 (Fin r → ℝ)).symm z
    have hn : ‖matrixEuclideanMap Xᵀ u‖ ≤ B * ‖u‖ :=
      (matrixEuclideanMap Xᵀ).le_of_opNorm_le hX u
    have hsq : (Xᵀ *ᵥ z) ⬝ᵥ (Xᵀ *ᵥ z) ≤ B ^ 2 * (z ⬝ᵥ z) := by
      have he := euclidean_dot_self (matrixEuclideanMap Xᵀ u)
      have hz := euclidean_dot_self u
      rw [matrixEuclideanMap_apply] at he
      change (Xᵀ *ᵥ z) ⬝ᵥ (Xᵀ *ᵥ z) = _ at he
      change z ⬝ᵥ z = ‖u‖ ^ 2 at hz
      rw [he, hz]
      nlinarith [norm_nonneg (matrixEuclideanMap Xᵀ u), norm_nonneg u]
    have hgram : z ⬝ᵥ (wishart X *ᵥ z) = (Xᵀ *ᵥ z) ⬝ᵥ (Xᵀ *ᵥ z) := by
      rw [wishart, ← Matrix.mulVec_mulVec, dotProduct_mulVec, ← vecMul_transpose]
      simp only [Matrix.transpose_transpose]
    simpa only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec_assoc,
      Matrix.one_mulVec, dotProduct_sub, dotProduct_smul, hgram, sub_nonneg] using hsq

end
end LowRank
