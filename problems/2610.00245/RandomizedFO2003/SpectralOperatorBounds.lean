import RandomizedFO2003.MarkedSpectral
import RandomizedFO2003.SpectralProjectors
import Mathlib.Analysis.InnerProductSpace.Adjoint

namespace RandomizedFO2003.SpectralCoordinates

open scoped BigOperators

variable {J : ℕ}

@[simp] theorem continuousDiagonal_apply (K : Fin J → ℕ) (f : Fin J → ℝ) (x : BlockSpace K) :
    continuousDiagonal K f x = diagonal K f x := rfl

theorem continuousDiagonal_selfAdjoint (K : Fin J → ℕ) (f : Fin J → ℝ) :
    IsSelfAdjoint (continuousDiagonal K f) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  exact (diagonal_self_adjoint K f x y).symm

theorem continuousDiagonal_pairing (K : Fin J → ℕ) (f : Fin J → ℝ) (x : BlockSpace K) :
    inner (𝕜 := ℝ) x (continuousDiagonal K f x) = ∑ j, weight K x j * f j := by
  have hunit : diagonal K (fun _ => 1) x = x := by rw [diagonal_one]; rfl
  simpa only [weightedPair, hunit, mul_one] using inner_diagonal K x (fun _ => 1) f

theorem continuousDiagonal_inner_lower (K : Fin J → ℕ) (f : Fin J → ℝ) (γ : ℝ)
    (hf : ∀ j, γ ≤ f j) (x : BlockSpace K) :
    γ * ‖x‖ ^ 2 ≤ inner (𝕜 := ℝ) x (continuousDiagonal K f x) := by
  rw [continuousDiagonal_pairing, ← weight_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _hj
  simpa only [mul_comm γ] using mul_le_mul_of_nonneg_left (hf j) (weight_nonneg K x j)

theorem continuousDiagonal_nonneg (K : Fin J → ℕ) (f : Fin J → ℝ)
    (hf : ∀ j, 0 ≤ f j) (x : BlockSpace K) : 0 ≤ inner (𝕜 := ℝ) x (continuousDiagonal K f x) := by
  simpa only [zero_mul] using continuousDiagonal_inner_lower K f 0 hf x

theorem continuousDiagonal_coercive (K : Fin J → ℕ) (f : Fin J → ℝ) (γ : ℝ)
    (hf : ∀ j, γ ≤ f j) (x : BlockSpace K) : γ * ‖x‖ ≤ ‖continuousDiagonal K f x‖ := by
  by_cases hx : x = 0
  · simp [hx]
  · have hx0 : 0 < ‖x‖ := norm_pos_iff.mpr hx
    apply (mul_le_mul_left hx0).mp
    calc
      ‖x‖ * (γ * ‖x‖) = γ * ‖x‖ ^ 2 := by ring
      _ ≤ inner (𝕜 := ℝ) x (continuousDiagonal K f x) := continuousDiagonal_inner_lower K f γ hf x
      _ ≤ |inner (𝕜 := ℝ) x (continuousDiagonal K f x)| := le_abs_self _
      _ ≤ ‖x‖ * ‖continuousDiagonal K f x‖ := abs_real_inner_le_norm _ _

theorem continuousDiagonal_apply_norm_le (K : Fin J → ℕ) (f : Fin J → ℝ) {M : ℝ}
    (hM : 0 ≤ M) (hf : ∀ j, |f j| ≤ M) (x : BlockSpace K) :
    ‖continuousDiagonal K f x‖ ≤ M * ‖x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hM (norm_nonneg x))).mp
  change ‖diagonal K f x‖ ^ 2 ≤ (M * ‖x‖) ^ 2
  rw [norm_diagonal_sq, weightedEnergy]
  calc
    _ ≤ ∑ j, weight K x j * M ^ 2 := by
      apply Finset.sum_le_sum
      intro j _hj
      apply mul_le_mul_of_nonneg_left _ (weight_nonneg K x j)
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hM).mpr (hf j)
    _ = (M * ‖x‖) ^ 2 := by rw [← Finset.sum_mul, weight_sum]; ring

theorem continuousDiagonal_norm_le (K : Fin J → ℕ) (f : Fin J → ℝ) {M : ℝ}
    (hM : 0 ≤ M) (hf : ∀ j, |f j| ≤ M) : ‖continuousDiagonal K f‖ ≤ M :=
  (continuousDiagonal K f).opNorm_le_bound hM (continuousDiagonal_apply_norm_le K f hM hf)

theorem continuousDiagonal_inverse_left (K : Fin J → ℕ) (f : Fin J → ℝ)
    (hf : ∀ j, f j ≠ 0) (x : BlockSpace K) :
    continuousDiagonal K (fun j => (f j)⁻¹) (continuousDiagonal K f x) = x := by
  change diagonal K (fun j => (f j)⁻¹) (diagonal K f x) = x
  ext i
  simp [diagonal_apply, ← mul_assoc, hf]

theorem continuousDiagonal_inverse_norm_le (K : Fin J → ℕ) (f : Fin J → ℝ)
    {γ : ℝ} (hγ : 0 < γ) (hf : ∀ j, γ ≤ f j) :
    ‖continuousDiagonal K (fun j => (f j)⁻¹)‖ ≤ γ⁻¹ := by
  apply continuousDiagonal_norm_le K _ (inv_nonneg.mpr hγ.le)
  intro j
  rw [abs_of_pos (inv_pos.mpr (hγ.trans_le (hf j)))]
  exact (inv_le_inv₀ (hγ.trans_le (hf j)) hγ).mpr (hf j)

end RandomizedFO2003.SpectralCoordinates
