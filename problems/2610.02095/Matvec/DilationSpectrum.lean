import Matvec.SpectralBridge
import Matvec.GameAlgebra

/-!
# Euclidean symmetric dilation and the normalized source promise

The domain is the actual 2N-dimensional Euclidean space indexed by the sum
of two copies of Fin N. Its norm is the Euclidean norm, not the max product
norm. The matrix is the `dilation` already used for exact oracle simulation.
-/

namespace Matvec

noncomputable section
open Matrix
open scoped Matrix InnerProductSpace

abbrev DilationSpace (n : ℕ) := EuclideanSpace ℝ (Fin n ⊕ Fin n)

def dilationLeft {n : ℕ} (w : DilationSpace n) : EuclideanSpace ℝ (Fin n) :=
  (WithLp.equiv 2 (Fin n → ℝ)).symm (fun i => w (Sum.inl i))

def dilationRight {n : ℕ} (w : DilationSpace n) : EuclideanSpace ℝ (Fin n) :=
  (WithLp.equiv 2 (Fin n → ℝ)).symm (fun i => w (Sum.inr i))

def dilationJoin {n : ℕ} (u v : EuclideanSpace ℝ (Fin n)) : DilationSpace n :=
  (WithLp.equiv 2 ((Fin n ⊕ Fin n) → ℝ)).symm (Sum.elim (u : Fin n → ℝ) (v : Fin n → ℝ))

theorem dilationLeft_join {n : ℕ} (u v : EuclideanSpace ℝ (Fin n)) :
    dilationLeft (dilationJoin u v) = u := rfl

theorem dilationRight_join {n : ℕ} (u v : EuclideanSpace ℝ (Fin n)) :
    dilationRight (dilationJoin u v) = v := rfl

def dilationMap {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ) :
    DilationSpace n →L[ℝ] DilationSpace n :=
  LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (dilation G))

theorem euclidean_norm_sq {ι : Type*} [Fintype ι] (x : EuclideanSpace ℝ ι) :
    ‖x‖ ^ 2 = ∑ i, (x i) ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
  simp only [Real.norm_eq_abs, sq_abs]

theorem dilation_norm_split {n : ℕ} (w : DilationSpace n) :
    ‖w‖ ^ 2 = ‖dilationLeft w‖ ^ 2 + ‖dilationRight w‖ ^ 2 := by
  simp only [euclidean_norm_sq, Fintype.sum_sum_type, dilationLeft, dilationRight,
    Equiv.apply_symm_apply]
  rfl

theorem dilationMap_left {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ) (w : DilationSpace n) :
    dilationLeft (dilationMap G w) = LowRank.matrixEuclideanMap G (dilationRight w) := by
  apply (WithLp.equiv 2 (Fin n → ℝ)).injective
  funext i
  change ((dilation G) *ᵥ (w : (Fin n ⊕ Fin n) → ℝ)) (Sum.inl i) =
    (G *ᵥ (fun j => w (Sum.inr j))) i
  simp [dilation, Matrix.mulVec, dotProduct, Fintype.sum_sum_type]

theorem dilationMap_right {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ) (w : DilationSpace n) :
    dilationRight (dilationMap G w) = LowRank.matrixEuclideanMap G.transpose (dilationLeft w) := by
  apply (WithLp.equiv 2 (Fin n → ℝ)).injective
  funext i
  change ((dilation G) *ᵥ (w : (Fin n ⊕ Fin n) → ℝ)) (Sum.inr i) =
    (G.transpose *ᵥ (fun j => w (Sum.inl j))) i
  simp [dilation, Matrix.mulVec, dotProduct, Fintype.sum_sum_type]

theorem dilationMap_norm_sq {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ) (w : DilationSpace n) :
    ‖dilationMap G w‖ ^ 2 =
      ‖LowRank.matrixEuclideanMap G (dilationRight w)‖ ^ 2 +
      ‖LowRank.matrixEuclideanMap G.transpose (dilationLeft w)‖ ^ 2 := by
  rw [dilation_norm_split, dilationMap_left, dilationMap_right]

theorem dilationMap_symmetric {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ) :
    (dilationMap G).toLinearMap.IsSymmetric := by
  apply Matrix.isHermitian_iff_isSymmetric.mp
  change (dilation G).conjTranspose = dilation G
  rw [Matrix.conjTranspose_eq_transpose_of_trivial, dilation_transpose]

theorem dilationMap_norm_le {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ)
    (B : ℝ) (hB : 0 ≤ B) (hG : ‖LowRank.matrixEuclideanMap G‖ ≤ B) :
    ‖dilationMap G‖ ≤ B := by
  apply ContinuousLinearMap.opNorm_le_bound _ hB
  intro w
  have hr := (LowRank.matrixEuclideanMap G).le_of_opNorm_le hG (dilationRight w)
  have ht : ‖LowRank.matrixEuclideanMap G.transpose‖ ≤ B := by
    rwa [matrixEuclideanMap_transpose_norm]
  have hl := (LowRank.matrixEuclideanMap G.transpose).le_of_opNorm_le ht (dilationLeft w)
  have hr2 := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hB (norm_nonneg _))).mpr hr
  have hl2 := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hB (norm_nonneg _))).mpr hl
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hB (norm_nonneg _))).mp
  rw [dilationMap_norm_sq, mul_pow, dilation_norm_split]
  rw [mul_pow] at hr2 hl2
  nlinarith

theorem dilationMap_expansion {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ)
    (a : ℝ) (ha : 0 ≤ a)
    (hG : ∀ x, a * ‖x‖ ≤ ‖LowRank.matrixEuclideanMap G x‖)
    (hGt : ∀ x, a * ‖x‖ ≤ ‖LowRank.matrixEuclideanMap G.transpose x‖) :
    ∀ w, a * ‖w‖ ≤ ‖dilationMap G w‖ := by
  intro w
  have hr := (sq_le_sq₀ (mul_nonneg ha (norm_nonneg _)) (norm_nonneg _)).mpr (hG (dilationRight w))
  have hl := (sq_le_sq₀ (mul_nonneg ha (norm_nonneg _)) (norm_nonneg _)).mpr (hGt (dilationLeft w))
  apply (sq_le_sq₀ (mul_nonneg ha (norm_nonneg _)) (norm_nonneg _)).mp
  rw [dilationMap_norm_sq, mul_pow, dilation_norm_split]
  rw [mul_pow] at hr hl
  nlinarith

theorem dilationJoin_zero_norm {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    ‖dilationJoin 0 x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [dilation_norm_split, dilationLeft_join, dilationRight_join, norm_zero, zero_pow (by decide), zero_add]

theorem dilationMap_join_zero_norm {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖dilationMap G (dilationJoin 0 x)‖ = ‖LowRank.matrixEuclideanMap G x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [dilationMap_norm_sq, dilationLeft_join, dilationRight_join, map_zero, norm_zero,
    zero_pow (by decide), add_zero]

theorem dilationMap_norm_eq {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ) :
    ‖dilationMap G‖ = ‖LowRank.matrixEuclideanMap G‖ := by
  apply le_antisymm (dilationMap_norm_le G _ (norm_nonneg _) le_rfl)
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  have h := (dilationMap G).le_opNorm (dilationJoin 0 x)
  rwa [dilationMap_join_zero_norm, dilationJoin_zero_norm] at h

theorem dilationMap_leastStretch_eq {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ)
    (hn : 0 < n) (hG : Function.Injective G.mulVec) :
    leastStretch (dilationMap G) = leastStretch (LowRank.matrixEuclideanMap G) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hu : ∃ x : EuclideanSpace ℝ (Fin n), ‖x‖ = 1 := exists_unit_vector
  have hadjoint := matrix_leastStretch_transpose G hn hG
  have hlow : ∀ x, leastStretch (LowRank.matrixEuclideanMap G) * ‖x‖ ≤
      ‖LowRank.matrixEuclideanMap G x‖ := leastStretch_mul_norm_le _
  have hlowt : ∀ x, leastStretch (LowRank.matrixEuclideanMap G) * ‖x‖ ≤
      ‖LowRank.matrixEuclideanMap G.transpose x‖ := by
    intro x
    rw [← hadjoint]
    exact leastStretch_mul_norm_le _ x
  have hnonneg : 0 ≤ leastStretch (LowRank.matrixEuclideanMap G) := by
    rw [matrix_leastStretch_eq_inverse_norm G hn hG]
    positivity
  apply le_antisymm
  · apply leastStretch_le_of_lifts _ _ hu
    intro x hx
    refine ⟨dilationJoin 0 x, ?_, dilationMap_join_zero_norm G x⟩
    rw [dilationJoin_zero_norm, hx]
  · have h := dilationMap_expansion G _ hnonneg hlow hlowt
    apply le_csInf
    · obtain ⟨x, hx⟩ := hu
      exact ⟨‖dilationMap G (dilationJoin 0 x)‖, dilationJoin 0 x,
        (dilationJoin_zero_norm x).trans hx, rfl⟩
    · rintro r ⟨w, hw, rfl⟩
      simpa only [hw, mul_one] using h w

def gaussianSourceMap {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ) (a : ℝ) :
    DilationSpace n →L[ℝ] DilationSpace n :=
  (Real.sqrt (n : ℝ) / a) • dilationMap G

/-- Exact spectral promise for the scaled source H=(sqrt N/a)D(G). -/
theorem gaussianSource_promise {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ)
    (hn : 0 < n) (a C : ℝ) (ha : 0 < a) (hC : 0 ≤ C)
    (hG : ∀ x, (a / Real.sqrt n) * ‖x‖ ≤ ‖LowRank.matrixEuclideanMap G x‖)
    (hGt : ∀ x, (a / Real.sqrt n) * ‖x‖ ≤ ‖LowRank.matrixEuclideanMap G.transpose x‖)
    (hupper : ‖LowRank.matrixEuclideanMap G‖ ≤ C * Real.sqrt n) :
    (gaussianSourceMap G a).toLinearMap.IsSymmetric ∧
    (∀ w, ‖w‖ ≤ ‖gaussianSourceMap G a w‖) ∧
    ‖gaussianSourceMap G a‖ ≤ (C / a) * n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn'
  have hscale : 0 < Real.sqrt (n : ℝ) / a := div_pos hs ha
  have heq : (Real.sqrt (n : ℝ) / a) * (a / Real.sqrt n) = 1 := by field_simp
  refine ⟨?_, ?_, ?_⟩
  · intro x y
    change ⟪(Real.sqrt (n : ℝ) / a) • dilationMap G x, y⟫_ℝ =
      ⟪x, (Real.sqrt (n : ℝ) / a) • dilationMap G y⟫_ℝ
    rw [real_inner_smul_left, real_inner_smul_right]
    have hsym := dilationMap_symmetric G x y
    change ⟪dilationMap G x, y⟫_ℝ = ⟪x, dilationMap G y⟫_ℝ at hsym
    rw [hsym]
  · intro w
    have h := dilationMap_expansion G (a / Real.sqrt n) (by positivity) hG hGt w
    have hmul := mul_le_mul_of_nonneg_left h hscale.le
    rw [← mul_assoc, heq, one_mul] at hmul
    simpa only [gaussianSourceMap, ContinuousLinearMap.smul_apply, norm_smul,
      Real.norm_eq_abs, abs_of_pos hscale] using hmul
  · have h := dilationMap_norm_le G (C * Real.sqrt n) (by positivity) hupper
    have hscaled := ContinuousLinearMap.opNorm_smul_le (Real.sqrt (n : ℝ) / a) (dilationMap G)
    rw [Real.norm_eq_abs, abs_of_pos hscale] at hscaled
    refine hscaled.trans ((mul_le_mul_of_nonneg_left h hscale.le).trans_eq ?_)
    have hsquare := Real.sq_sqrt hn'.le
    field_simp
    nlinarith

theorem gaussianSource_leastStretch {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ)
    (hn : 0 < n) (hG : Function.Injective G.mulVec) (a : ℝ) (ha : 0 < a) :
    leastStretch (gaussianSourceMap G a) =
      (Real.sqrt (n : ℝ) / a) * leastStretch (LowRank.matrixEuclideanMap G) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [gaussianSourceMap, leastStretch_smul _ _ (by positivity), dilationMap_leastStretch_eq G hn hG]

/-- Exact inverse-norm/smallest-singular-value relation used to turn the
inverse-power estimate back into a spectral estimate of G. -/
theorem gaussianSource_inverse_norm {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ)
    (hn : 0 < n) (hG : Function.Injective G.mulVec) (a : ℝ) (ha : 0 < a)
    (M : DilationSpace n →L[ℝ] DilationSpace n)
    (hHM : ∀ x, gaussianSourceMap G a (M x) = x)
    (hMH : ∀ x, M (gaussianSourceMap G a x) = x) :
    ‖M‖ = a / (Real.sqrt (n : ℝ) * leastStretch (LowRank.matrixEuclideanMap G)) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have heq := leastStretch_eq_inverse_norm (gaussianSourceMap G a) M hHM hMH
  rw [gaussianSource_leastStretch G hn hG a ha] at heq
  have h := congrArg (fun t : ℝ => t⁻¹) heq
  dsimp only at h
  rw [inv_inv, _root_.mul_inv_rev, inv_div] at h
  rw [← h]
  ring

end
end Matvec
