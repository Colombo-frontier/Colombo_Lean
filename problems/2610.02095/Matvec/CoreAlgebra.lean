import Mathlib.Data.Matrix.Block
import Mathlib.Analysis.NormedSpace.OperatorNorm.Basic
import Mathlib.Tactic

/-!
Deterministic algebra and variational comparison in `lem:gaussian-core`.
No Gaussian law, adaptive posterior, or measurable frame selection is claimed
in this module.
-/
namespace Matvec
open Matrix
open scoped Matrix

section Blocks
variable {q k l : Type*} [Fintype q] [Fintype k] [Fintype l]
  [DecidableEq q]

/-- The projection decomposition in `lem:posterior`, without any probabilistic
assumptions. -/
theorem posterior_decomposition (G P Q : Matrix q q ℝ) :
    G = P * G + (1 - P) * G * Q + (1 - P) * G * (1 - Q) := by
  noncomm_ring

/-- The square pivot lift cancels the observed top rows exactly. -/
theorem schur_lift (A Ainv : Matrix q q ℝ) (B : Matrix q k ℝ)
    (C : Matrix k q ℝ) (Z : Matrix k k ℝ)
    (hA : A * Ainv = 1) (z : k → ℝ) :
    Matrix.fromBlocks A B C Z *ᵥ Sum.elim (-(Ainv *ᵥ (B *ᵥ z))) z =
      Sum.elim (0 : q → ℝ) ((Z - C * Ainv * B) *ᵥ z) := by
  simp only [Matrix.fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr,
    Matrix.mulVec_neg, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hA, Matrix.one_mul,
    Matrix.one_mulVec,
    neg_add_cancel, Matrix.sub_mulVec]
  abel_nf

omit [Fintype q] [Fintype l] [DecidableEq q] in
/-- Kernel restriction removes the top part of the low-rank perturbation. -/
theorem kernel_restriction (Y : Matrix q k ℝ) (W : Matrix l k ℝ)
    (V : Matrix k l ℝ) (hker : Y * V = 0) :
    (show Matrix (q ⊕ l) k ℝ from
      fun i j => Sum.elim (fun a => Y a j) (fun b => W b j) i) * V =
      (fun i j => Sum.elim (fun _ : q => 0) (fun b => (W * V) b j) i) := by
  ext i j
  cases i with
  | inl i => simpa [Matrix.mul_apply] using congrFun (congrFun hker i) j
  | inr i => rfl

end Blocks

section Variational
variable {E F K L : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup K] [NormedSpace ℝ K]
  [NormedAddCommGroup L] [NormedSpace ℝ L]

/-- Least norm on the unit sphere, i.e. the least singular value in nonzero
finite-dimensional Euclidean spaces. -/
noncomputable def leastStretch (A : E →L[ℝ] F) : ℝ :=
  sInf {r : ℝ | ∃ x : E, ‖x‖ = 1 ∧ ‖A x‖ = r}

theorem leastStretch_le_of_unit (A : E →L[ℝ] F) {x : E} (hx : ‖x‖ = 1) :
    leastStretch A ≤ ‖A x‖ := by
  apply csInf_le
  · exact ⟨0, by rintro r ⟨y, hy, rfl⟩; exact norm_nonneg _⟩
  · exact ⟨x, hx, rfl⟩

theorem leastStretch_le_ratio (A : E →L[ℝ] F) {x : E} (hx : x ≠ 0) :
    leastStretch A ≤ ‖A x‖ / ‖x‖ := by
  have hnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hu : ‖(‖x‖⁻¹ : ℝ) • x‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x)),
      inv_mul_cancel₀ hnorm]
  have h := leastStretch_le_of_unit A hu
  simpa only [map_smul, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x)), div_eq_mul_inv, mul_comm] using h

/-- Abstract variational form of the Schur-complement and kernel-restriction
comparisons. A unit vector for the core has a lift whose norm is at least one
and whose image has exactly the same norm. -/
theorem leastStretch_le_of_lifts (A : E →L[ℝ] F) (B : K →L[ℝ] L)
    (hunit : ∃ z : K, ‖z‖ = 1)
    (hlift : ∀ z : K, ‖z‖ = 1 → ∃ x : E, 1 ≤ ‖x‖ ∧ ‖A x‖ = ‖B z‖) :
    leastStretch A ≤ leastStretch B := by
  apply le_csInf
  · obtain ⟨z, hz⟩ := hunit
    exact ⟨‖B z‖, z, hz, rfl⟩
  · rintro r ⟨z, hz, rfl⟩
    obtain ⟨x, hx, heq⟩ := hlift z hz
    have hx0 : x ≠ 0 := by intro h; subst x; norm_num at hx
    calc
      leastStretch A ≤ ‖A x‖ / ‖x‖ := leastStretch_le_ratio A hx0
      _ ≤ ‖A x‖ := div_le_self (norm_nonneg _) hx
      _ = ‖B z‖ := heq

end Variational
end Matvec
