import Matvec.CoreAlgebra
import Matvec.InversePower
import LowRank.InverseGramWishartBound
import LowRank.MatrixNetBound
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Deterministic spectral bridges for the Gaussian solve reduction

Uses the existing `leastStretch` and `LowRank.matrixEuclideanMap` definitions.
Spectral witnesses are constructed from Mathlib's finite-dimensional spectral
theorem rather than supplied as unproved existence assumptions.
-/

namespace Matvec

noncomputable section
open Matrix
open scoped Matrix InnerProductSpace

section Spectral
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]

/-- A self-adjoint real operator has a unit eigenvector at its operator norm
in absolute value. The index is chosen from an orthonormal eigenbasis. -/
theorem symmetric_top_eigenvector (M : E →L[ℝ] E)
    (hM : M.toLinearMap.IsSymmetric) :
    ∃ (μ : ℝ) (v : E), ‖v‖ = 1 ∧ M v = μ • v ∧ ‖M‖ ≤ |μ| := by
  let n := Module.finrank ℝ E
  have hn : 0 < n := Module.finrank_pos_iff.mpr inferInstance
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let b := hM.eigenvectorBasis (show Module.finrank ℝ E = n from rfl)
  let lam := hM.eigenvalues (show Module.finrank ℝ E = n from rfl)
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ (fun j : Fin n => |lam j|)
    Finset.univ_nonempty
  refine ⟨lam i, b i, b.norm_eq_one i, ?_, ?_⟩
  · exact hM.apply_eigenvectorBasis rfl i
  · apply M.opNorm_le_bound (abs_nonneg _)
    intro x
    have hcoord (j : Fin n) : b.repr (M x) j = lam j * b.repr x j :=
      hM.eigenvectorBasis_apply_self_apply rfl x j
    have hnorm (y : E) : ∑ j, (b.repr y j) ^ 2 = ‖y‖ ^ 2 := by
      have h := LowRank.euclidean_dot_self (b.repr y)
      simpa only [dotProduct, pow_two, b.repr.norm_map] using h
    have hs : ∑ j, (b.repr (M x) j) ^ 2 ≤ |lam i| ^ 2 * ∑ j, (b.repr x j) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j hj
      rw [hcoord, mul_pow]
      have hval := hi j (Finset.mem_univ j)
      have hsq := (sq_le_sq₀ (abs_nonneg (lam j)) (abs_nonneg (lam i))).mpr hval
      rw [sq_abs] at hsq
      exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
    rw [hnorm, hnorm] at hs
    rw [← mul_pow] at hs
    exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (abs_nonneg _) (norm_nonneg _))).mp hs

omit [FiniteDimensional ℝ E] [Nontrivial E] in
/-- Symmetry passes to an actual two-sided inverse. -/
theorem inverse_isSymmetric (H M : E →L[ℝ] E) (hH : H.toLinearMap.IsSymmetric)
    (hHM : ∀ x, H (M x) = x) : M.toLinearMap.IsSymmetric := by
  intro x y
  calc
    ⟪M x, y⟫_ℝ = ⟪M x, H (M y)⟫_ℝ := by rw [hHM]
    _ = ⟪H (M x), M y⟫_ℝ := (hH (M x) (M y)).symm
    _ = ⟪x, M y⟫_ℝ := by rw [hHM]

/-- The least stretch is exactly the reciprocal inverse norm. The upper
bound uses the norm-attaining eigenvector just constructed. -/
theorem leastStretch_eq_inv_norm (H M : E →L[ℝ] E)
    (hH : H.toLinearMap.IsSymmetric)
    (hHM : ∀ x, H (M x) = x) (hMH : ∀ x, M (H x) = x) :
    leastStretch H = ‖M‖⁻¹ := by
  obtain ⟨μ, v, hv, heigen, hnorm⟩ := symmetric_top_eigenvector M (inverse_isSymmetric H M hH hHM)
  have hμ : μ ≠ 0 := by
    intro h
    have hvzero : v = 0 := by
      have he := hHM v
      rw [heigen, h, zero_smul, map_zero] at he
      exact he.symm
    rw [hvzero, norm_zero] at hv
    norm_num at hv
  have heq := top_eigenvalue_eq_opNorm M v μ heigen hv hnorm
  have hnpos : 0 < ‖M‖ := by rw [← heq]; exact abs_pos.mpr hμ
  apply le_antisymm
  · have hHv : H v = μ⁻¹ • v := by
      have he := congrArg H heigen
      rw [hHM, map_smul] at he
      calc
        H v = μ⁻¹ • (μ • H v) := by rw [smul_smul, inv_mul_cancel₀ hμ, one_smul]
        _ = μ⁻¹ • v := by rw [← he]
    calc
      leastStretch H ≤ ‖H v‖ := leastStretch_le_of_unit H hv
      _ = ‖M‖⁻¹ := by rw [hHv, norm_smul, hv, mul_one, Real.norm_eq_abs, abs_inv, heq]
  · apply le_csInf
    · exact ⟨‖H v‖, v, hv, rfl⟩
    · rintro r ⟨x, hx, rfl⟩
      have h := M.le_opNorm (H x)
      rw [hMH, hx] at h
      rw [inv_eq_one_div]
      exact (div_le_iff₀ hnpos).mpr (by simpa [mul_comm] using h)

end Spectral

section GeneralInverse
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E]

theorem exists_unit_vector : ∃ x : E, ‖x‖ = 1 := by
  obtain ⟨x, hx⟩ := exists_ne (0 : E)
  refine ⟨(‖x‖⁻¹ : ℝ) • x, ?_⟩
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x)),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]

theorem leastStretch_mul_norm_le (A : E →L[ℝ] E) (x : E) :
    leastStretch A * ‖x‖ ≤ ‖A x‖ := by
  by_cases hx : x = 0
  · simp [hx]
  · exact (le_div_iff₀ (norm_pos_iff.mpr hx)).mp (leastStretch_le_ratio A hx)

/-- Reciprocal inverse-norm characterization without symmetry assumptions. -/
theorem leastStretch_eq_inverse_norm (H M : E →L[ℝ] E)
    (hHM : ∀ x, H (M x) = x) (hMH : ∀ x, M (H x) = x) :
    leastStretch H = ‖M‖⁻¹ := by
  obtain ⟨v, hv⟩ := exists_unit_vector (E := E)
  have hMzero : M ≠ 0 := by
    intro hz
    have h := hHM v
    rw [hz, ContinuousLinearMap.zero_apply, map_zero] at h
    have hvzero : v = 0 := h.symm
    rw [hvzero, norm_zero] at hv
    norm_num at hv
  have hnorm : 0 < ‖M‖ := norm_pos_iff.mpr hMzero
  have hlo : ‖M‖⁻¹ ≤ leastStretch H := by
    apply le_csInf
    · exact ⟨‖H v‖, v, hv, rfl⟩
    · rintro r ⟨x, hx, rfl⟩
      have h := M.le_opNorm (H x)
      rw [hMH, hx] at h
      rw [inv_eq_one_div]
      exact (div_le_iff₀ hnorm).mpr (by simpa [mul_comm] using h)
  have hleast : 0 < leastStretch H := (inv_pos.mpr hnorm).trans_le hlo
  have hu : ‖M‖ ≤ (leastStretch H)⁻¹ := by
    apply M.opNorm_le_bound (inv_nonneg.mpr hleast.le)
    intro x
    have h := leastStretch_mul_norm_le H (M x)
    rw [hHM] at h
    have h' : ‖M x‖ ≤ ‖x‖ / leastStretch H :=
      (le_div_iff₀ hleast).mpr (by simpa only [mul_comm] using h)
    simpa only [div_eq_mul_inv, mul_comm] using h'
  apply le_antisymm _ hlo
  rw [inv_eq_one_div] at hu ⊢
  apply (le_div_iff₀ hnorm).mpr
  have h := (le_div_iff₀ hleast).mp hu
  simpa only [mul_comm] using h

theorem leastStretch_smul (A : E →L[ℝ] E) (c : ℝ) (hc : 0 < c) :
    leastStretch (c • A) = c * leastStretch A := by
  obtain ⟨v, hv⟩ := exists_unit_vector (E := E)
  have hnorm (x : E) : ‖(c • A) x‖ = c * ‖A x‖ := by
    simp only [ContinuousLinearMap.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_pos hc]
  apply le_antisymm
  · have hdiv : leastStretch (c • A) / c ≤ leastStretch A := by
      apply le_csInf
      · exact ⟨‖A v‖, v, hv, rfl⟩
      · rintro r ⟨x, hx, rfl⟩
        apply (div_le_iff₀ hc).mpr
        have h := leastStretch_le_of_unit (c • A) hx
        rw [hnorm] at h
        simpa only [mul_comm] using h
    have h := (div_le_iff₀ hc).mp hdiv
    simpa only [mul_comm] using h
  · apply le_csInf
    · exact ⟨‖(c • A) v‖, v, hv, rfl⟩
    · rintro r ⟨x, hx, rfl⟩
      rw [hnorm]
      exact mul_le_mul_of_nonneg_left (leastStretch_le_of_unit A hx) hc.le

end GeneralInverse

section Matrices

/-- Every ordered eigenvalue of a full-column-rank Gram matrix is strictly
positive, independently of the chosen ordered spectral certificate. -/
theorem ordered_gram_values_pos {d s : ℕ} (X : Matrix (Fin d) (Fin s) ℝ)
    (hX : Function.Injective X.mulVec) (sp : LowRank.OrderedMatrixSpectrum (X.transpose * X)) :
    ∀ i, 0 < sp.value i := by
  have hgram : IsUnit (X.transpose * X).det := LowRank.gram_det_isUnit_of_injective X hX
  have hbas : IsUnit sp.basis.det := Matrix.isUnit_det_of_left_inverse sp.orthogonal
  have hdiag : IsUnit (Matrix.diagonal sp.value).det := by
    rw [← sp.diagonalizes, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    exact (hbas.mul hgram).mul hbas
  have hprod : (∏ i, sp.value i) ≠ 0 := by
    simpa only [Matrix.det_diagonal] using hdiag.ne_zero
  intro i
  have hne : sp.value i ≠ 0 := (Finset.prod_ne_zero_iff.mp hprod) i (Finset.mem_univ i)
  exact lt_of_le_of_ne (sp.value_nonneg (LowRank.rightGram_posSemidef X) i) hne.symm

theorem matrixEuclideanMap_transpose_adjoint {m n : ℕ} (G : Matrix (Fin m) (Fin n) ℝ) :
    LowRank.matrixEuclideanMap G.transpose =
      ContinuousLinearMap.adjoint (LowRank.matrixEuclideanMap G) := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℝ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_right]
  conv_rhs => rw [real_inner_comm]
  rw [LowRank.matrixEuclideanMap_inner, LowRank.matrixEuclideanMap_inner,
    dotProduct_mulVec, Matrix.vecMul_transpose, dotProduct_comm]

theorem matrixEuclideanMap_transpose_norm {m n : ℕ} (G : Matrix (Fin m) (Fin n) ℝ) :
    ‖LowRank.matrixEuclideanMap G.transpose‖ = ‖LowRank.matrixEuclideanMap G‖ := by
  rw [matrixEuclideanMap_transpose_adjoint]
  exact ContinuousLinearMap.adjoint.norm_map _

theorem square_leftKernelProjector_zero {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ)
    (hG : Function.Injective G.mulVec) : LowRank.leftKernelProjector G = 0 := by
  have hdet : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det G).mp
    (Matrix.mulVec_injective_iff_isUnit.mp hG)
  have hz := congrArg Matrix.transpose (LowRank.transpose_mul_leftKernelProjector G hG)
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero,
    (LowRank.leftKernelProjector_isProjector G).symmetric] at hz
  calc
    LowRank.leftKernelProjector G = LowRank.leftKernelProjector G * (G * G⁻¹) := by
      rw [Matrix.mul_nonsing_inv G hdet, Matrix.mul_one]
    _ = (LowRank.leftKernelProjector G * G) * G⁻¹ := (Matrix.mul_assoc _ _ _).symm
    _ = 0 := by rw [hz, Matrix.zero_mul]

/-- The inverse-Gram top-eigenvalue bound gives a lower squared stretch for
the transpose, with the square full-rank projector explicitly eliminated. -/
theorem inverseGram_top_transpose_expansion {n : ℕ}
    (G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hG : Function.Injective G.mulVec)
    (R : ℝ) (hR : 0 < R) (htop : LowRank.inverseGramEigenvalue G (Fin.last n) ≤ R)
    (x : EuclideanSpace ℝ (Fin (n + 1))) :
    R⁻¹ * ‖x‖ ^ 2 ≤ ‖LowRank.matrixEuclideanMap G.transpose x‖ ^ 2 := by
  have hlo := LowRank.wishart_lower_of_inverseGram_top_le G hR htop
  rw [square_leftKernelProjector_zero G hG, sub_zero] at hlo
  have h := hlo.2 (x : Fin (n + 1) → ℝ)
  have hgram : (x : Fin (n + 1) → ℝ) ⬝ᵥ (LowRank.wishart G *ᵥ (x : Fin (n + 1) → ℝ)) =
      ‖LowRank.matrixEuclideanMap G.transpose x‖ ^ 2 := by
    rw [LowRank.wishart, ← Matrix.mulVec_mulVec, dotProduct_mulVec,
      ← Matrix.vecMul_transpose, Matrix.transpose_transpose]
    simpa only [LowRank.matrixEuclideanMap_apply, Matrix.mulVec_transpose] using
      LowRank.euclidean_dot_self (LowRank.matrixEuclideanMap G.transpose x)
  simp only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec_assoc, Matrix.one_mulVec,
    dotProduct_sub, dotProduct_smul, hgram, LowRank.euclidean_dot_self, sub_nonneg] at h
  change R⁻¹ * ((x : Fin (n + 1) → ℝ) ⬝ᵥ (x : Fin (n + 1) → ℝ)) ≤ _ at h
  have heq : ((x : Fin (n + 1) → ℝ) ⬝ᵥ (x : Fin (n + 1) → ℝ)) = ‖x‖ ^ 2 :=
    LowRank.euclidean_dot_self x
  rwa [heq] at h

/-- A lower norm bound for a surjective adjoint also holds for the original
operator; this is duality plus Cauchy-Schwarz, not an assumed singular-value law. -/
theorem expansion_of_adjoint_expansion
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (A : E →L[ℝ] F) (a : ℝ) (ha : 0 < a)
    (hsurj : Function.Surjective (ContinuousLinearMap.adjoint A))
    (hlower : ∀ y, a * ‖y‖ ≤ ‖ContinuousLinearMap.adjoint A y‖) :
    ∀ x, a * ‖x‖ ≤ ‖A x‖ := by
  intro x
  obtain ⟨y, hy⟩ := hsurj x
  have hlow := hlower y
  rw [hy] at hlow
  have hinner : ‖x‖ ^ 2 = ⟪y, A x⟫_ℝ := by
    rw [← ContinuousLinearMap.adjoint_inner_left, hy, real_inner_self_eq_norm_sq]
  have hcs : ‖x‖ ^ 2 ≤ ‖y‖ * ‖A x‖ := by
    rw [hinner]
    exact real_inner_le_norm _ _
  by_cases hx : x = 0
  · simp [hx]
  · have hnx : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hmul := mul_le_mul_of_nonneg_left hcs ha.le
    have hmul' := mul_le_mul_of_nonneg_right hlow (norm_nonneg (A x))
    have hfinal : ‖x‖ * (a * ‖x‖) ≤ ‖x‖ * ‖A x‖ := by nlinarith
    exact (mul_le_mul_left hnx).mp hfinal

theorem matrixEuclideanMap_surjective_of_injective {n : ℕ}
    (G : Matrix (Fin n) (Fin n) ℝ) (hG : Function.Injective G.mulVec) :
    Function.Surjective (LowRank.matrixEuclideanMap G) := by
  have hs : Function.Surjective G.mulVec := Matrix.mulVec_surjective_iff_isUnit.mpr
    (Matrix.mulVec_injective_iff_isUnit.mp hG)
  intro x
  obtain ⟨y, hy⟩ := hs (x : Fin n → ℝ)
  refine ⟨(WithLp.equiv 2 (Fin n → ℝ)).symm y, ?_⟩
  apply (WithLp.equiv 2 (Fin n → ℝ)).injective
  exact hy

/-- Concrete least-singular-value expansion obtained from the inverse-Gram
tail event, for both G and its transpose. -/
theorem inverseGram_top_expansion {n : ℕ}
    (G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hG : Function.Injective G.mulVec)
    (R a : ℝ) (hR : 0 < R) (ha : 0 < a)
    (hscale : a ^ 2 ≤ R⁻¹) (htop : LowRank.inverseGramEigenvalue G (Fin.last n) ≤ R) :
    (∀ x, a * ‖x‖ ≤ ‖LowRank.matrixEuclideanMap G.transpose x‖) ∧
    (∀ x, a * ‖x‖ ≤ ‖LowRank.matrixEuclideanMap G x‖) := by
  have hlower : ∀ x, a * ‖x‖ ≤ ‖LowRank.matrixEuclideanMap G.transpose x‖ := by
    intro x
    have h := inverseGram_top_transpose_expansion G hG R hR htop x
    have hs := mul_le_mul_of_nonneg_right hscale (sq_nonneg ‖x‖)
    apply (sq_le_sq₀ (mul_nonneg ha.le (norm_nonneg _)) (norm_nonneg _)).mp
    rw [mul_pow]
    exact hs.trans h
  refine ⟨hlower, ?_⟩
  apply expansion_of_adjoint_expansion (LowRank.matrixEuclideanMap G) a ha
  · rw [← matrixEuclideanMap_transpose_adjoint]
    apply matrixEuclideanMap_surjective_of_injective
    apply Matrix.mulVec_injective_iff_isUnit.mpr
    exact (Matrix.isUnit_transpose G).mpr (Matrix.mulVec_injective_iff_isUnit.mp hG)
  · rwa [← matrixEuclideanMap_transpose_adjoint]

/-- Dimension-normalized form used to select the Gaussian source event. -/
theorem inverseGram_gaussian_expansion {n : ℕ}
    (G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hG : Function.Injective G.mulVec)
    (a : ℝ) (ha : 0 < a)
    (htop : LowRank.inverseGramEigenvalue G (Fin.last n) ≤ (n + 1 : ℝ) / a ^ 2) :
    (∀ x, (a / Real.sqrt (n + 1 : ℝ)) * ‖x‖ ≤ ‖LowRank.matrixEuclideanMap G.transpose x‖) ∧
    (∀ x, (a / Real.sqrt (n + 1 : ℝ)) * ‖x‖ ≤ ‖LowRank.matrixEuclideanMap G x‖) := by
  apply inverseGram_top_expansion G hG ((n + 1 : ℝ) / a ^ 2)
    (a / Real.sqrt (n + 1 : ℝ)) (by positivity) (by positivity) _ htop
  rw [div_pow, Real.sq_sqrt (by positivity), inv_div]

theorem matrix_leastStretch_lower {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ)
    (hn : 0 < n) (a : ℝ) (hG : ∀ x, a * ‖x‖ ≤ ‖LowRank.matrixEuclideanMap G x‖) :
    a ≤ leastStretch (LowRank.matrixEuclideanMap G) := by
  let i : Fin n := ⟨0, hn⟩
  let v := (EuclideanSpace.basisFun (Fin n) ℝ) i
  have hv : ‖v‖ = 1 := (EuclideanSpace.basisFun (Fin n) ℝ).norm_eq_one i
  apply le_csInf
  · exact ⟨‖LowRank.matrixEuclideanMap G v‖, v, hv, rfl⟩
  · rintro r ⟨x, hx, rfl⟩
    simpa only [hx, mul_one] using hG x

theorem matrix_inverse_maps {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ)
    (hG : Function.Injective G.mulVec) :
    (∀ x, LowRank.matrixEuclideanMap G (LowRank.matrixEuclideanMap G⁻¹ x) = x) ∧
    (∀ x, LowRank.matrixEuclideanMap G⁻¹ (LowRank.matrixEuclideanMap G x) = x) := by
  have hdet : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det G).mp
    (Matrix.mulVec_injective_iff_isUnit.mp hG)
  constructor
  · intro x
    apply (WithLp.equiv 2 (Fin n → ℝ)).injective
    change G *ᵥ (G⁻¹ *ᵥ (x : Fin n → ℝ)) = (x : Fin n → ℝ)
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv G hdet, Matrix.one_mulVec]
  · intro x
    apply (WithLp.equiv 2 (Fin n → ℝ)).injective
    change G⁻¹ *ᵥ (G *ᵥ (x : Fin n → ℝ)) = (x : Fin n → ℝ)
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul G hdet, Matrix.one_mulVec]

theorem matrix_leastStretch_eq_inverse_norm {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ)
    (hn : 0 < n) (hG : Function.Injective G.mulVec) :
    leastStretch (LowRank.matrixEuclideanMap G) = ‖LowRank.matrixEuclideanMap G⁻¹‖⁻¹ := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨hr, hl⟩ := matrix_inverse_maps G hG
  exact leastStretch_eq_inverse_norm _ _ hr hl

theorem matrix_leastStretch_transpose {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ)
    (hn : 0 < n) (hG : Function.Injective G.mulVec) :
    leastStretch (LowRank.matrixEuclideanMap G.transpose) =
      leastStretch (LowRank.matrixEuclideanMap G) := by
  have ht : Function.Injective G.transpose.mulVec := Matrix.mulVec_injective_iff_isUnit.mpr
    ((Matrix.isUnit_transpose G).mpr (Matrix.mulVec_injective_iff_isUnit.mp hG))
  rw [matrix_leastStretch_eq_inverse_norm G.transpose hn ht,
    matrix_leastStretch_eq_inverse_norm G hn hG, ← Matrix.transpose_nonsing_inv,
    matrixEuclideanMap_transpose_norm]

theorem matrixEuclideanMap_mul {m n k : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (B : Matrix (Fin n) (Fin k) ℝ) :
    LowRank.matrixEuclideanMap (A * B) =
      (LowRank.matrixEuclideanMap A).comp (LowRank.matrixEuclideanMap B) := by
  apply ContinuousLinearMap.ext
  intro x
  apply (WithLp.equiv 2 (Fin m → ℝ)).injective
  exact (Matrix.mulVec_mulVec (x : Fin k → ℝ) A B).symm

/-- A spectral value is bounded by the actual Euclidean operator norm,
using its orthogonal column as a unit Rayleigh witness. -/
theorem ordered_value_le_opNorm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (sp : LowRank.OrderedMatrixSpectrum A) (i : Fin n) :
    sp.value i ≤ ‖LowRank.matrixEuclideanMap A‖ := by
  let e : Fin n → ℝ := Pi.single i 1
  let v : EuclideanSpace ℝ (Fin n) := (WithLp.equiv 2 (Fin n → ℝ)).symm (sp.basis *ᵥ e)
  have hv : ‖v‖ = 1 := by
    have hdot := LowRank.orthogonal_columns_dot sp.basis sp.orthogonal e
    have heq := LowRank.euclidean_dot_self v
    change (sp.basis *ᵥ e) ⬝ᵥ (sp.basis *ᵥ e) = ‖v‖ ^ 2 at heq
    rw [hdot] at heq
    simp [e, dotProduct, Pi.single_apply] at heq
    nlinarith [norm_nonneg v]
  have hinner : ⟪v, LowRank.matrixEuclideanMap A v⟫_ℝ = sp.value i := by
    rw [LowRank.matrixEuclideanMap_inner]
    change (sp.basis *ᵥ e) ⬝ᵥ (A *ᵥ (sp.basis *ᵥ e)) = _
    rw [sp.quadratic]
    simp [e, Pi.single_apply]
  have h := real_inner_le_norm v (LowRank.matrixEuclideanMap A v)
  rw [hinner, hv, one_mul] at h
  have hop := (LowRank.matrixEuclideanMap A).le_opNorm v
  rw [hv, mul_one] at hop
  exact h.trans hop

theorem inverseGram_eigenvalue_le_inverse_norm_sq {n : ℕ}
    (G : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    LowRank.inverseGramEigenvalue G i ≤ ‖LowRank.matrixEuclideanMap G⁻¹‖ ^ 2 := by
  have heig := ordered_value_le_opNorm (LowRank.inverseGram G)
    (LowRank.orderedMatrixSpectrum (LowRank.inverseGram_posSemidef G).isHermitian) i
  change LowRank.inverseGramEigenvalue G i ≤ _ at heig
  refine heig.trans ?_
  rw [LowRank.inverseGram, Matrix.mul_inv_rev, ← Matrix.transpose_nonsing_inv,
    matrixEuclideanMap_mul]
  have h := (LowRank.matrixEuclideanMap G⁻¹).opNorm_comp_le
    (LowRank.matrixEuclideanMap G⁻¹.transpose)
  rw [matrixEuclideanMap_transpose_norm] at h
  simpa only [pow_two] using h

/-- A large inverse-Gram eigenvalue forces a small least singular value.
This is the deterministic event inclusion needed for the lower hard edge. -/
theorem leastStretch_le_of_inverseGram_eigenvalue {n : ℕ}
    (G : Matrix (Fin n) (Fin n) ℝ) (hn : 0 < n) (hG : Function.Injective G.mulVec)
    (i : Fin n) (R : ℝ) (hR : 0 < R) (hlarge : R ≤ LowRank.inverseGramEigenvalue G i) :
    leastStretch (LowRank.matrixEuclideanMap G) ≤ (Real.sqrt R)⁻¹ := by
  have h := hlarge.trans (inverseGram_eigenvalue_le_inverse_norm_sq G i)
  have hs : Real.sqrt R ≤ ‖LowRank.matrixEuclideanMap G⁻¹‖ :=
    (Real.sqrt_le_left (norm_nonneg _)).mpr h
  rw [matrix_leastStretch_eq_inverse_norm G hn hG]
  exact inv_anti₀ (Real.sqrt_pos.mpr hR) hs

end Matrices

end
end Matvec
