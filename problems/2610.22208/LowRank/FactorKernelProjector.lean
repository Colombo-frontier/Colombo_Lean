import LowRank.KernelProjectorMeasurable
import LowRank.FactorDataMeasurable

/-! Put the actual input's kernel projector in the cumulative query basis.
Its bottom block is dominated by the residual matrix's kernel projector. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix
noncomputable section

theorem IsOrthogonalProjector.coordinates {m l : Type*} [Fintype m] [Fintype l]
    [DecidableEq m] [DecidableEq l] {P : Matrix m m ℝ} (hP : IsOrthogonalProjector P)
    (B : Matrix m l ℝ) (hB : B * Bᵀ = 1) : IsOrthogonalProjector (Bᵀ * P * B) := by
  constructor
  · simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hP.symmetric, Matrix.mul_assoc]
  · calc
      _ = Bᵀ * (P * (B * Bᵀ) * P) * B := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hB, Matrix.mul_one, hP.idempotent]

theorem block_kernel_bottom_le {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
    [DecidableEq a] [DecidableEq b] [DecidableEq c]
    (A : Matrix a a ℝ) (C : Matrix b a ℝ) (D : Matrix b c ℝ)
    (K : Matrix (a ⊕ b) (a ⊕ b) ℝ) (hK : IsOrthogonalProjector K)
    (hker : (fromBlocks A 0 C D)ᵀ * K = 0) (hD : Function.Injective D.mulVec) :
    LoewnerLE (K.submatrix Sum.inr Sum.inr) (leftKernelProjector D) := by
  apply bottom_block_le_of_support hK (leftKernelProjector_isProjector D)
  apply bottom_support_of_range
  intro v
  apply (leftKernelProjector_fixed_iff D hD _).mpr
  let z := K *ᵥ v
  have hz : (fromBlocks A 0 C D)ᵀ *ᵥ z = 0 := by
    rw [Matrix.mulVec_mulVec, hker, Matrix.zero_mulVec]
  have he : Sum.elim (z ∘ Sum.inl) (z ∘ Sum.inr) = z := by
    funext i
    cases i <;> rfl
  have hz' : (fromBlocks A 0 C D)ᵀ *ᵥ Sum.elim (z ∘ Sum.inl) (z ∘ Sum.inr) = 0 := by
    rw [he]
    exact hz
  exact ((block_transpose_kernel_iff A C D _ _).mp hz').2

def factorKernelProjector {d t q r s : ℕ} (st : FactorData d t q r s)
    (D : Matrix (Fin r) (Fin s) ℝ) : Matrix (Fin q ⊕ Fin r) (Fin q ⊕ Fin r) ℝ :=
  st.2.1ᵀ * leftKernelProjector (representedMatrix st D) * st.2.1

theorem factorKernelProjector_isProjector {d t q r s : ℕ} (st : FactorData d t q r s)
    (D : Matrix (Fin r) (Fin s) ℝ) (hst : st.Orthogonal) :
    IsOrthogonalProjector (factorKernelProjector st D) :=
  (leftKernelProjector_isProjector (representedMatrix st D)).coordinates st.2.1 hst.2.1

theorem factorKernelProjector_annihilated {d t q r s : ℕ} (st : FactorData d t q r s)
    (D : Matrix (Fin r) (Fin s) ℝ) (hst : st.Orthogonal)
    (hX : Function.Injective (representedMatrix st D).mulVec) :
    (fromBlocks st.1.1 0 st.1.2 D)ᵀ * factorKernelProjector st D = 0 := by
  have he : st.2.2ᵀ * ((representedMatrix st D)ᵀ * leftKernelProjector (representedMatrix st D)) * st.2.1 =
      (fromBlocks st.1.1 0 st.1.2 D)ᵀ * factorKernelProjector st D := by
    calc
      _ = (st.2.2ᵀ * st.2.2) *
          ((fromBlocks st.1.1 0 st.1.2 D)ᵀ * factorKernelProjector st D) := by
        simp only [representedMatrix, factorKernelProjector, Matrix.transpose_mul,
          Matrix.transpose_transpose, Matrix.mul_assoc]
      _ = _ := by rw [hst.2.2.1, Matrix.one_mul]
  rw [← he, transpose_mul_leftKernelProjector _ hX, Matrix.mul_zero, Matrix.zero_mul]

theorem factorKernelProjector_bottom_le {d t q r s : ℕ} (st : FactorData d t q r s)
    (D : Matrix (Fin r) (Fin s) ℝ) (hst : st.Orthogonal)
    (hX : Function.Injective (representedMatrix st D).mulVec) (hD : Function.Injective D.mulVec) :
    LoewnerLE ((factorKernelProjector st D).submatrix Sum.inr Sum.inr) (leftKernelProjector D) :=
  block_kernel_bottom_le st.1.1 st.1.2 D _ (factorKernelProjector_isProjector st D hst)
    (factorKernelProjector_annihilated st D hst hX) hD

theorem measurable_factorKernelProjector {S : Type*} [MeasurableSpace S] {d t q r s : ℕ}
    (st : S → FactorData d t q r s) (D : S → Matrix (Fin r) (Fin s) ℝ)
    (hst : Measurable st) (hD : Measurable D) : Measurable (fun x => factorKernelProjector (st x) (D x)) := by
  have hc : Measurable (fun x => fromBlocks (st x).1.1 0 (st x).1.2 (D x)) := by
    apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro j
    cases i <;> cases j <;> simp only [fromBlocks_apply₁₁, fromBlocks_apply₁₂,
      fromBlocks_apply₂₁, fromBlocks_apply₂₂] <;> fun_prop
  have hx : Measurable (fun x => representedMatrix (st x) (D x)) := by
    apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro j
    simp only [representedMatrix, Matrix.mul_apply, Matrix.transpose_apply]
    fun_prop
  have hk := measurable_leftKernelProjector.comp hx
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  simp only [factorKernelProjector, Matrix.mul_apply, Matrix.transpose_apply]
  fun_prop

end
end LowRank
